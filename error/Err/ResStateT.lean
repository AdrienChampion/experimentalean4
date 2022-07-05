import Err.ResT

/-! ## Error state monad (transformer)

Monad `ResStateT` stores a bunch of errors as a tree, where nodes carry error-context. The idea is
to register errors without short-circuiting execution, and adding context to error trees.
-/



namespace Err



inductive State.Tree (γ : Type u) (ε : Type v) where
  --- Leaf, just an error.
  | leaf : ε → Tree γ ε
  --- Stores a context bit and a non-empty list of trees.
  | node : γ → Tree γ ε → List (Tree γ ε) → Tree γ ε

namespace State.Tree
  variable
    {γ : Type u}
    {ε : Type v}

  /-- Number of errors appearing in the tree, *i.e.* number of leaves

      Should **not** be partial, but Lean struggles to prove termination.
  -/
  partial def errCount : Tree γ ε → Nat
    | leaf _ => 1
    | node _ hd tl =>
      hd.errCount
      |> tl.foldl
        fun sum tree => sum + tree.errCount

  /-- Turns an `Err` into a `Tree`. -/
  def ofErr (e : Err γ ε) : Tree γ ε :=
    Tree.leaf e.source
    |> e.trace.reverse.foldl
      fun tree ctx =>
        Tree.node ctx tree []


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
    [Eε : Style.ToStyled ε]
    [Eγ : Style.ToStyled γ]
    (self : Tree γ ε)
    (style : Style)
    (prec : Nat)
    (pref : optParam String "- ")
    -- (isTop : optParam Bool true)
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
      (pref ++ Eε.toStyledRepr error style prec)
      |>.nest 2
    | node ctx tree tail =>
      let ctxFmt :=
        pref ++ Eγ.toStyledRepr ctx style prec
      let treeFmt :=
        tree.toStyledRepr style prec pref -- false
      match tail with
      | [] => ctxFmt ++ treeFmt
      | tail =>
        (ctxFmt ++ Std.Format.line ++ treeFmt.nest 2)
        |> tail.foldl
          fun fmt tree =>
            let treeFmt :=
              tree.toStyledRepr style prec pref -- false
              |>.nest 2
            fmt ++ Std.Format.line ++ treeFmt

  def reprPrec
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (self : Tree γ ε)
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.toStyledRepr default prec pref

  def toStyledString
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (self : Tree γ ε)
    (style : Style)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr style prec pref}"

  def toString
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (self : Tree γ ε)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr default prec pref}"
end State.Tree



/-! ## Actual state of the error state monad -/

/-- Maintains a list of current errors and a tree of context-equiped errors. -/
structure State (γ : Type u) (ε : Type v) : Type (max u v) where
protected innerMk ::
  style : Style
  current : List ε
  trees : List (State.Tree γ ε)

/-- Default value is the empty error state. -/
instance instInhabitedState : Inhabited (State γ ε) where
  default :=
    ⟨default, [], []⟩

namespace State
  variable
    {γ : Type u}
    {γ' : Type u}
    {ε : Type v}
    {ε' : Type v}
    {α : Type w}
    (self : State γ ε)

  /-- Empty error state. -/
  def empty : State γ ε :=
    ⟨default, [], []⟩

  /-- Sets the error state's report style. -/
  def withStyle (style : Style) : State γ ε :=
    { self with style }

  /-- True if error state is empty. -/
  def isOk : Bool :=
    self.current.isEmpty && self.trees.isEmpty
  /-- True if error state contains errors. -/
  def hasErrors : Bool :=
    ¬ self.isOk

  /-- Worst function name ever. -/
  def errgister [Into ε' ε] (e : ε') : State γ ε :=
    { self with current := conv e :: self.current }

  /-- Alias for `errgister`. -/
  abbrev bail :=
    @errgister

  /-- Produces `current` errors and trees as a list of trees. -/
  def getAllTrees : List (Tree γ ε) :=
    self.current
    |>.map Tree.leaf
    |> List.revAppend self.trees

  -- /-- Adds context to the inner (trees of) errors. -/
  -- def withContext [Into ε' ε] (getCtx' : Unit → ε') : State γ ε :=
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
  def withContext [Into γ' γ] (getCtx' : Unit → γ') : State γ ε :=
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
    {γ : Type u}
    {ε : Type v}
    (self : State γ ε)

  def toStyledRepr
    [Style.ToStyled γ]
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
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.toStyledRepr default prec pref

  def toStyledString
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (style : Style)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr style prec pref}"

  def toString
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    self.toStyledString default prec pref
end State

instance instToStringState
  [Style.ToStyled γ]
  [Style.ToStyled ε]
: ToString (State γ ε)
where
  toString :=
    State.toString

instance instReprState
  [Style.ToStyled γ]
  [Style.ToStyled ε]
: Repr (State γ ε)
where
  reprPrec :=
    State.reprPrec

instance instToStyledState
  [Style.ToStyled γ]
  [Style.ToStyled ε]
: Style.ToStyled (State γ ε)
where
  toStyled :=
    State.toStyledString
  toStyledRepr :=
    State.toStyledRepr



/-! ## Unwrapping -/

namespace State
  variable
    {γ : Type u}
    {ε : Type v}
    {α : Type w}
    (self : State γ ε)

  /-- Registers an error if any, does nothing otherwise. -/
  def unwrap? : Res γ ε α → Option α × State γ ε
    | ok a => (a, self)
    | err e => (
      none,
      { self with trees := self.trees ++ [Tree.ofErr e] }
    )

  /-- Same as `unwrap?` with a default value. -/
  def getD (res : Res γ ε α) (default : α) : α × State γ ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default, state)
  /-- Alias for `getD`. -/
  abbrev unwrapOr :=
    @getD

  /-- Same as `unwrap?` with a lazy default value. -/
  def unwrapOrElse (res : Res γ ε α) (default : Unit → α) : α × State γ ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default (), state)

  /-- Same as `unwrap?` but panics if `res` is an error.

      Does **not** report errors in the error state (`self`), only the error being unwrapped.
  -/
  def unwrap!
    [Inhabited α]
    [Style.ToStyled γ]
    [Style.ToStyled ε]
  : Res γ ε α → α × State γ ε
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
    [Style.ToStyled γ]
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

/-- State monad transformer, carries an error state `State γ ε`. -/
abbrev ErrStateT (γ : Type u) (ε : Type u) (μ : Type u → Type v) (α : Type u) :=
  StateT (State γ ε) μ α

/-- Error state monad -/
abbrev ErrStateM (γ : Type u) (ε : Type u) (α : Type u) :=
  ErrStateT γ ε Id α

instance instSubsingletonStateM
  [Subsingleton (State γ ε)]
  [Subsingleton α]
: Subsingleton (ErrStateM γ ε α)
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
  def run!
    [Style.ToStyled γ]
    [Style.ToStyled ε]
    [Monad μ]
    (x : ErrStateT γ ε μ α)
    (s : State γ ε)
  : μ α :=
    do
      let (res, state) ←
        ErrStateT.run x s
      state.unwrapSelf!
      pure res

  /-- Registers the error from `res`, if any. -/
  def unwrap?
    [Monad μ]
    (res : Res γ ε α)
  : ErrStateT γ ε μ (Option α) :=
    do
      let state ← get
      let (a?, state) :=
        state.unwrap? res
      set state
      pure a?

  /-- Adds some context to all current errors. -/
  def withContext
    [Into γ' γ]
    [Monad μ]
    (getCtx' : Unit → γ')
  : ErrStateT γ ε μ Unit :=
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
    : Alternative (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadErrStateT
    : Monad (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadLiftErrStateT
    : MonadLift μ (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadFunctorErrStateT
    : MonadFunctor μ (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadExceptOfStateT [MonadExceptOf ε μ]
    : MonadExceptOf ε (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadStateOfStateT
    : MonadStateOf (State γ ε) (ErrStateT γ ε μ)
  :=
    inferInstance
  instance instMonadFinallyStateT [MonadFinally μ]
    : MonadFinally (ErrStateT γ ε μ)
  :=
    inferInstance
end instances



/-! ## State monad operations -/
namespace ErrStateT
  /-- Acts on the error state, sets the style to render errors with. -/
  def errorReportStyle [Monad μ] (style : Style) : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.withStyle style
      |> set
end ErrStateT
