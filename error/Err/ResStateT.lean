import Err.ResT

/-! ## Error state monad (transformer)

Monad `ResStateT` stores a bunch of errors as a tree, where nodes carry error-context. The idea is
to register errors without short-circuiting execution, and adding context to error trees.
-/



namespace Err



inductive State.Tree (ε : Type u) where
  --- Leaf, just an error.
  | leaf : Err ε → Tree ε
  --- Stores a context bit and a non-empty list of trees.
  | node : ε → Tree ε → List (Tree ε) → Tree ε

namespace State.Tree
  variable
    {ε : Type u}

  /-! ## (Pretty-)printing

      For nodes, the context is printed as an item `- {ctx}` and subtrees are pretty-printed with an
      indentation of `2`. There is a small readability trick however: if a node only has one
      subtree, no indentation is introduced so that nested mono-tree nodes do not make context and
      errors drift left.
  -/

  /-- Should **not** be partial.
      
      Should be implemented by `Tree.rec`, but there's no code generation for that *atm*. So we use
      structural recursion instead, which Lean cannot prove terminates.

      A commented version using `Tree.rec` is provided in the body.
  -/
  partial def toStyledRepr
    [E : Style.ToStyled ε]
    (self : Tree ε)
    (style : Style)
    (prec : Nat)
    (pref : optParam String "- ")
    (isTop : optParam Bool true)
    : Std.Format
  :=
    -- self.rec
    --   -- leaf case
    --   (fun e =>
    --     e.toStyledRepr style prec pref
    --   )
    --   -- node case, assuming all subtrees have been formatted
    --   (fun ctx _tree _trees treeFmt treesFmt =>
    --     let ctxFmt :=
    --       E.toStyledRepr ctx style prec
    --     let initFmt :=
    --       f!"{ctxFmt}\n{treeFmt}"
    --     if treesFmt.isEmpty
    --     then
    --       initFmt
    --     else
    --       initFmt
    --       |> treesFmt.foldl
    --         fun fmt tree =>
    --           f!"{fmt}\n{treeFmt}"
    --       |>.nest 2
    --   )
    --   -- init for fold over `trees` yielding `Std.Format`
    --   []
    --   -- step for fold over `trees` yielding `Std.Format`
    --   (fun _ _ hdFmt tlFmt => 
    --     hdFmt :: tlFmt
    --   )

    -- structural-recursive-by-hand version
    match self with
    | leaf error =>
      f!"{pref}{error.toStyledRepr style prec pref |>.nest 2}"
    | node e tree tail =>
      let eFmt :=
        E.toStyledRepr e style prec
      let treeFmt :=
        tree.toStyledRepr style prec pref false
      let head :=
        eFmt ++ Std.Format.line ++ treeFmt
      if tail.isEmpty ∧ ¬isTop
      then
        head
      else
        head
        |> tail.foldl
          fun fmt tree =>
            let treeFmt :=
              tree.toStyledRepr style prec pref false
            f!"{fmt}\n{treeFmt}"
        |>.nest 2

  def reprPrec
    [Repr ε]
    (self : Tree ε)
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.toStyledRepr default prec pref

  def toStyledString
    [Style.ToStyled ε]
    (self : Tree ε)
    (style : Style)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr style prec pref}"

  def toString
    [ToString ε]
    (self : Tree ε)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr default prec pref}"
end State.Tree



/-! ## Actual state of the error state monad -/

/-- Maintains a list of current errors and a tree of context-equiped errors. -/
structure State (ε : Type u) where
protected innerMk ::
  style : Style
  current : Err ε |> List
  trees : State.Tree ε |> List

/-- Default value is the empty error state. -/
instance instInhabitedState : Inhabited (State ε) where
  default :=
    ⟨default, [], []⟩

namespace State
  variable
    {ε : Type u}
    {ε' : Type u}
    {α : Type v}
    (self : State ε)

  /-- Empty error state. -/
  def empty : State ε :=
    ⟨default, [], []⟩

  /-- Sets the error state's report style. -/
  def withStyle (style : Style) : State ε :=
    { self with style }

  /-- True if error state is empty. -/
  def isOk : Bool :=
    self.current.isEmpty && self.trees.isEmpty
  /-- True if error state contains errors. -/
  def hasErrors : Bool :=
    ¬ self.isOk

  /-- Worst function name ever. -/
  def errgister [Into ε' (Err ε)] (e : ε') : State ε :=
    { self with current := conv e :: self.current }

  /-- Alias for `errgister`. -/
  abbrev bail :=
    @errgister

  /-- Produces `current` errors and trees as a list of trees. -/
  def getAllTrees : List (Tree ε) :=
    self.current
    |>.map Tree.leaf
    |> List.revAppend self.trees

  -- /-- Adds context to the inner (trees of) errors. -/
  -- def withContext [Into ε' ε] (getCtx' : Unit → ε') : State ε :=
  --   Id.run do
  --     let mut res :=
  --       self
  --     if ¬res.current.isEmpty then
  --       -- turn `res.current` into `Tree`s and add them to `res.trees`
  --       res :=
  --         { res with
  --           current := [],
  --           trees := res.getAllTrees
  --         }
  --     if let hd :: tl := res.trees then
  --       -- would be much better to **prove** this but whatever
  --       if ¬ res.current.isEmpty then
  --         panic! "[fatal] current list of errors is not empty"
  --       -- wrap `res.trees` in a `Tree.node` with relevant context
  --       let ctx :=
  --         getCtx' ()
  --         |> conv
  --       let trees :=
  --         [Tree.node ctx hd tl]
  --       res := { res with trees }
  --     res

  /-- Adds context to the inner errors. -/
  def withContext [Into ε' ε] (getCtx' : Unit → ε') : State ε :=
    match self.current with
    | [] => self
    | hd :: tl =>
      let ctx :=
        getCtx' ()
        |> conv
      let tree :=
        Tree.node ctx (Tree.leaf hd) (tl.map Tree.leaf)
      { self with
        current := [],
        trees := self.trees ++ [tree]
      }
end State



/-! ## (Pretty-)printing -/

namespace State
  variable
    {ε : Type u}
    (self : State ε)

  def toStyledRepr
    [Style.ToStyled ε]
    (style : Style)
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    match self.getAllTrees with
    | [] => "no errors to report"
    | hd :: tl =>
      hd.toStyledRepr style prec pref
      |> tl.foldl
        fun fmt tree =>
          let treeFmt :=
            tree.toStyledRepr style prec pref
          f!"{fmt}\n{treeFmt}"

  def reprPrec
    [Repr ε]
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.toStyledRepr default prec pref

  def toStyledString
    [Style.ToStyled ε]
    (style : Style)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr style prec pref}"

  def toString
    [ToString ε]
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    self.toStyledString default prec pref
end State

instance instToStringState [ToString ε] : ToString (State ε) where
  toString :=
    State.toString

instance instReprState [Repr α] [Repr ε] : Repr (State ε) where
  reprPrec :=
    State.reprPrec

instance instToStyledState [Style.ToStyled ε] : Style.ToStyled (State ε) where
  toStyled :=
    State.toStyledString
  toStyledRepr :=
    State.toStyledRepr



/-! ## Unwrapping -/

namespace State
  variable
    {ε : Type u}
    {α : Type v}
    (self : State ε)

  /-- Registers an error if any, does nothing otherwise. -/
  def unwrap? : Res ε α → Option α × State ε
    | ok a => (a, self)
    | err e => (none, self.errgister e)

  /-- Same as `unwrap?` with a default value. -/
  def getD (res : Res ε α) (default : α) : α × State ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default, state)
  /-- Alias for `getD`. -/
  abbrev unwrapOr :=
    @getD

  /-- Same as `unwrap?` with a lazy default value. -/
  def unwrapOrElse (res : Res ε α) (default : Unit → α) : α × State ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default (), state)

  /-- Same as `unwrap?` but panics if `res` is an error.

      Does **not** report errors in the error state (`self`), only the error being unwrapped.
  -/
  def unwrap! [Inhabited α] [Style.ToStyled ε] : Res ε α → α × State ε
    | ok a => (a, self)
    | err e =>
      let msg :=
        "trying to unwrap an error result:\n"
        |> Std.Format.text
      let full :=
        msg ++ (self.style.toStyledRepr e 1)
      panic! s!"{full.nest 0}"

  /-- Panics if `self` contains errors, yields `pure ()` otherwise. -/
  def unwrapSelf!
    [Style.ToStyled ε]
    {μ : optParam (Type → Type) Id} [Monad μ]
    : μ Unit
  :=
    if self.isOk
    then
      pure ()
    else
      let msg :=
        "trying to unwrap an error state containing errors:\n"
        |> Std.Format.text
      let full :=
        msg ++ Std.Format.line ++ (self.style.toStyledRepr self 1)
      panic! s!"{full.nest 0}"
end State



/-! ## Error state monad -/

/-- State monad transformer, carries an error state `State ε`. -/
abbrev ErrStateT (ε : Type u) (μ : Type u → Type v) (α : Type u) :=
  StateT (State ε) μ α

/-- Error state monad -/
abbrev ErrStateM (ε : Type u) (α : Type u) :=
  ErrStateT ε Id α

instance instSubsingletonStateM [Subsingleton (State ε)] [Subsingleton α]
  : Subsingleton (ErrStateM ε α)
:=
  inferInstance


namespace ErrStateT
  export StateT (
    run run'
    lift
    get set modifyGet
    pure bind map orElse
    failure
  )

  /-- Runs and unwraps the error state, panicking if it contains any error. -/
  def run! [Style.ToStyled ε] [Monad μ] (x : ErrStateT ε μ α) (s : State ε) : μ α :=
    do
      let (res, state) ←
        ErrStateT.run x s
      state.unwrapSelf!
      pure res

  /-- Registers the error from `res`, if any. -/
  def unwrap? [Monad μ] (res : Res ε α) : ErrStateT ε μ (Option α) :=
    do
      let state ← get
      let (a?, state) :=
        state.unwrap? res
      set state
      pure a?

  /-- Adds some context to all current errors. -/
  def withContext [Into ε' ε] [Monad μ] (getCtx' : Unit → ε') : ErrStateT ε μ Unit :=
    do
      let state ← get
      state.withContext getCtx'
      |> set
end ErrStateT

/-! ## Monadic instances -/
section instances
  variable
    [Monad μ]

  instance instAlternativeErrStateT [Alternative μ]
    : Alternative (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadErrStateT
    : Monad (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadLiftErrStateT
    : MonadLift μ (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadFunctorErrStateT
    : MonadFunctor μ (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadExceptOfStateT [MonadExceptOf ε μ]
    : MonadExceptOf ε (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadStateOfStateT
    : MonadStateOf (State ε) (ErrStateT ε μ)
  :=
    inferInstance
  instance instMonadFinallyStateT [MonadFinally μ]
    : MonadFinally (ErrStateT ε μ)
  :=
    inferInstance
end instances



/-! ## State monad operations -/
namespace ErrStateT
  /-- Acts on the error state, sets the style to render errors with. -/
  def errorReportStyle [Monad μ] (style : Style) : ErrStateT ε μ Unit :=
    do
      let state ← get
      state.withStyle style
      |> set
end ErrStateT
