def 𝕂
  {α : Type u}
  {β : Type v}
  (val : β)
: α → β :=
  fun _ => val


inductive Either
  (α : outParam (Sort u))
  (β : outParam (Sort u))
| left : α → Either α β
| right : β → Either α β

section Either
  variable
    (self : Either α β)

  def Either.collapse
    (f : α → γ)
    (g : β → γ)
  : Either α β → γ
    | left a => f a
    | right b => g b

  def Either.left?
  : Option α :=
    self.collapse some (𝕂 none)

  def Either.right?
  : Option β :=
    self.collapse (𝕂 none) some

  def Either.mapLeft
    (f : α → γ)
  : Either γ β :=
    self.collapse
      (f · |> left)
      right

  def Either.mapRight
    (f : β → γ)
  : Either α γ :=
    self.collapse
      left
      (f · |> right)
end Either


section parse
  inductive Parse.Opt
  | long : String → Opt
  | short : Char → Opt
  deriving Repr, BEq

  def Parse.Opt.toString
  : Opt → String
  | long l => s!"--{l}"
  | short s => s!"-{s}"

  instance instToStringParseOpt
  : ToString Parse.Opt :=
    ⟨Parse.Opt.toString⟩



  inductive Parse.Arg
  | val : String → Arg
  | sep : Arg
  | opt : Opt → Arg
  deriving Repr, BEq

  section helpers
    def Parse.Arg.long
    : String → Arg :=
      (Opt.long · |> opt)
    def Parse.Arg.short
    : Char → Arg :=
      (Opt.short · |> opt)

    def Parse.Arg.isVal
    : Parse.Arg → Bool
    | .val _ => true
    | .sep => false
    | .opt _ => false

    def Parse.Arg.isOpt
    : Parse.Arg → Bool
    | .val _ => false
    | .sep => false
    | .opt _ => true

    def Parse.Arg.isSep
    : Parse.Arg → Bool
    | .val _ => false
    | .sep => true
    | .opt _ => false

    def Parse.Arg.getVal
    : Parse.Arg → Option String
    | .val v => v
    | .sep => none
    | .opt _ => none

    def Parse.Arg.getOpt
    : Parse.Arg → Option Opt
    | .val _ => none
    | .sep => none
    | .opt o => o
  end helpers
  
  def Parse.Arg.toString
  : Arg → String
  | .val v => v
  | .sep => "--"
  | .opt o => o.toString

  instance instToStringParseArg
  : ToString Parse.Arg :=
    ⟨Parse.Arg.toString⟩



  structure Parse.Err where
    arg : Option Arg
    msg : String
  deriving Repr, BEq
  
  def Parse.Err.toString
    (self : Err)
  : String :=
    if let some arg := self.arg then
      s!"on `{arg}`: {self.msg}"
    else self.msg

  instance instToStringParseErr
  : ToString Parse.Err :=
    ⟨Parse.Err.toString⟩



  inductive Parse.Res
    (α : Sort u)
  | ok : α → Res α
  | err : Err → Res α

  export Parse (Res)
end parse



section validate
  structure Validator (In : Sort v) (Out : Sort u) where
    validate : In → Out

  /-- Identity validator. -/
  protected def Validator.id
    (α : Sort u)
  : Validator α α :=
    ⟨id⟩

  /-- `Unit` to `Unit` validator. -/
  def Validator.unit
  : Validator Unit Unit :=
    ⟨id⟩
  
  /-- Constant validator. -/
  def Validator.const
    {In : Sort u}
    {Out : Sort v}
    (val : Out)
  : Validator In Out :=
    ⟨fun _ => val⟩
end validate



section opt
  structure Opt.Flag where
    long : String
    short : Char
    desc : String
  deriving Repr, BEq

  inductive Opt.Card
    (α : Sort u)
  | none : Card α
  | one : Validator String α → Card α
  | many : Validator (List String) α → Card α

  structure Opt where
  innerMk ::
    flag : Opt.Flag
    Out : Sort u
    card : Opt.Card Out

  def Opt.mk
    (flag : Opt.Flag)
    {Out : Sort u}
    (card : Opt.Card Out)
  : Opt :=
    ⟨flag, Out, card⟩
end opt



section cxt
  structure Cxt.Run.TopState where
    args : List Parse.Arg
    errsRev : List Parse.Err

  structure Cxt.Run.ArgState where
    top : TopState
    arg : Parse.Arg
    errsRev : List String

  def Cxt.Run.ArgState.toTop
    (self : ArgState)
  : TopState :=
    let mkErr :=
      Parse.Err.mk self.arg
    let errs :=
      self.errsRev.map mkErr
    { self.top with
      errsRev :=
        errs ++ self.top.errsRev
    }



  def Cxt.Run.Top
    (α : Type)
  :=
    StateM TopState α

  def Cxt.Run.Arg
    (α : Type)
  :=
    StateM ArgState α
end cxt
