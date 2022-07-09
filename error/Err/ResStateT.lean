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
deriving Inhabited

--- `Err → State.Tree`
instance instIntoErrTree : Into (Err γ ε) (State.Tree γ ε) where
  conv
    | { source, trace } =>
      source
      |> State.Tree.leaf
      |> trace.foldr
        fun ctx tree => State.Tree.node ctx tree []

--- `ε → State.Tree _ ε`
instance instIntoErrorTreeError : Into ε (State.Tree γ ε) where
  conv :=
    State.Tree.leaf

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
    |> e.trace.foldl
      fun tree ctx =>
        Tree.node ctx tree []

  /-- Extracts the longest linear prefix of the tree. -/
  def linearPrefixFoldl
    (init : α)
    (fold : α → γ → α)
    (final : α → Tree γ ε → β)
    (self : Tree γ ε)
  : β :=
    match self with
    | Tree.node ctx tree [] =>
      let a :=
        fold init ctx
      tree.linearPrefixFoldl a fold final
    | Tree.leaf _ | Tree.node _ _ (_ :: _) =>
      final init self


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
    : Std.Format
  :=
    self.linearPrefixFoldl init fold final
  where
    nestLevel :=
      pref.length

    init :=
      none

    fold
      (acc : Option Std.Format)
      (ctx : γ)
    : Option Std.Format :=
      let (pref, andThen) :=
        if let some acc := acc then (
          pref.length |> String.repeat ' ',
          fun fmt => acc ++ Std.Format.line ++ fmt
        ) else (pref, id)
      (pref ++ Eγ.toStyledRepr ctx style prec)
      |> andThen
      |> some

    final
      (acc : Option Std.Format)
    : Tree γ ε → Std.Format
      | leaf error =>
        let (pref, andThen) :=
          if let some acc := acc then (
            pref.length |> String.repeat ' ',
            fun fmt => acc ++ Std.Format.line ++ fmt
          ) else (pref, id)
        let leafFmt :=
          (pref ++ (Eε.toStyledRepr error style prec).nest nestLevel)
        andThen leafFmt
      | node ctx tree tail =>
        let (prefCtx, andThen) :=
          if let some acc := acc then (
            pref.length |> String.repeat ' ',
            fun fmt => acc ++ Std.Format.line ++ fmt
          ) else (pref, id)
        let ctxFmt :=
          prefCtx ++ Eγ.toStyledRepr ctx style prec
        let treeFmt :=
          tree.toStyledRepr style prec pref
        let subFmt :=
          (Std.Format.line ++ treeFmt)
          |> tail.foldl
            fun fmt tree =>
              let treeFmt :=
                tree.toStyledRepr style prec pref
              fmt ++ Std.Format.line ++ treeFmt
        (ctxFmt ++ subFmt.nest nestLevel)
        |> andThen

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

instance instToStyledTree
  [Style.ToStyled α]
  [Style.ToStyled γ]
: Style.ToStyled (State.Tree α γ) where
  toStyled :=
    State.Tree.toStyledString
  toStyledRepr :=
    State.Tree.toStyledRepr



/-! ## Actual state of the error state monad -/

/-- Maintains a list of current errors and a tree of context-equiped errors. -/
structure State (γ : Type u) (ε : Type v) : Type (max u v) where
protected innerMk ::
  style : Style
  current : List (State.Tree γ ε)
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

  /-- Lists all error trees. -/
  def errors : State.Tree γ ε |> List :=
    List.revAppend
      self.current
      self.trees

  /-- Worst function name ever. -/
  def errgister [Into ε' (Tree γ ε)] (e : ε') : State γ ε :=
    { self with
      current :=
        conv e :: self.current
    }

  -- /-- Alias for `errgister`. -/
  -- abbrev bail :=
  --   @errgister

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

  /-- Adds context to current errors. -/
  def withContext [Into γ' γ] (getCtx' : Unit → γ') : State γ ε :=
    match self.current with
    | [] => self
    | hd :: tl =>
      let ctx :=
        getCtx' ()
        |> conv
      let tree :=
        Tree.node ctx hd tl
      { self with current := [tree] }

  /-- Adds context to all errors. -/
  def withGlobalContext [Into γ' γ] (getCtx' : Unit → γ') : State γ ε :=
    match self.errors with
    | [] =>  self
    | hd :: tl =>
      let ctx :=
        getCtx' ()
        |> conv
      let tree :=
        Tree.node ctx hd tl
      ⟨self.style, [], [tree]⟩

  /-- Puts `self.current` into `self.trees`. -/
  def finalize : State γ ε :=
    { self with current := [], trees := self.errors }

  /-- Wraps current errors in some context and adds that to `self.trees`. -/
  def finalizeWith
    [Into γ' γ]
    (getCtx' : Unit → γ')
  : State γ ε :=
    self.withContext getCtx'
    |>.finalize
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
    match self.errors with
    | [] => "no errors to report"
    | hd :: tl =>
      -- let indent := 2
        -- if tl.isEmpty then 0 else 2
      hd.toStyledRepr style prec pref
      |> tl.foldl
        fun fmt tree =>
          let treeFmt :=
            tree.toStyledRepr style prec pref
          fmt ++ Std.Format.line ++ treeFmt

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
  def unwrap?
    {ε' : Type v}
    [Into ε' (Tree γ ε)]
  : Res ε' α → Option α × State γ ε
    | ok a => (a, self)
    | err e => (
      none,
      { self with current := self.current ++ [conv e] }
    )

  /-- Same as `unwrap?` with a default value. -/
  def getD
    {ε' : Type v}
    [Into ε' (Tree γ ε)]
    (res : Res ε' α)
    (default : α)
  : α × State γ ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default, state)
  /-- Alias for `getD`. -/
  abbrev unwrapOr :=
    @getD

  /-- Same as `unwrap?` with a lazy default value. -/
  def unwrapOrElse
    {ε' : Type v}
    [Into ε' (Tree γ ε)]
    (res : Res ε' α)
    (default : Unit → α)
  : α × State γ ε :=
    match self.unwrap? res with
    | (some a, state) =>
      (a, state)
    | (none, state) =>
      (default (), state)

  /-- Same as `unwrap?` but panics if `res` is an error.

      Does **not** report errors in the error state (`self`), only the error being unwrapped.
  -/
  def unwrap!
    {ε' : Type v}
    [Into ε' (Tree γ ε)]
    [Inhabited α]
    [Style.ToStyled γ]
    [Style.ToStyled ε]
  : Res ε' α → α × State γ ε
    | ok a => (a, self)
    | err e =>
      let msg :=
        "trying to unwrap an error result:\n"
        |> Std.Format.text
      let e : Tree γ ε :=
        conv e
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

  /-- Runs itself and returns a result. -/
  def run?
    [Monad μ]
    (x : ErrStateT γ ε μ α)
    (s : State γ ε)
  : μ (Err.Res (State.Tree γ ε |> List) α) :=
    do
      let (res, state) ←
        ErrStateT.run x s
      let res :=
        match state.errors with
        | [] => Err.Res.ok res
        | errors => Err.Res.err errors
      pure res

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

  /-- Worst function name ever. -/
  def errgister
    [Monad μ]
    [Into ε' (State.Tree γ ε)]
    (e : ε')
  : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.errgister e
      |> set

  /-- Registers the error from `res`, if any. -/
  def unwrap?
    [Monad μ]
    [Into ε' (State.Tree γ ε)]
    (res : Res ε' α)
  : ErrStateT γ ε μ (Option α) :=
    do
      let state ← get
      let (a?, state) :=
        state.unwrap? res
      set state
      pure a?

  /-- Adds some context to current errors. -/
  def withContext
    [Into γ' γ]
    [Monad μ]
    (getCtx' : Unit → γ')
  : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.withContext getCtx'
      |> set

  /-- Adds context to all errors. -/
  def withGlobalContext
    [Into γ' γ]
    [Monad μ]
    (getCtx' : Unit → γ')
  : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.withGlobalContext getCtx'
      |> set

  /-- Puts `self.current` into `self.trees`. -/
  def finalize
    [Monad μ]
  : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.finalize
      |> set

  /-- Wraps current errors in some context and adds that to `self.trees`. -/
  def finalizeWith
    [Monad μ]
    [Into γ' γ]
    (getCtx' : Unit → γ')
  : ErrStateT γ ε μ Unit :=
    do
      let state ← get
      state.finalizeWith getCtx'
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
