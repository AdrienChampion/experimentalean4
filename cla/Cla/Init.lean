import Lean.Data.HashMap

section HashMap
  export Std (HashMap)

  def Std.HashMap.withCapacity
  :=
    @Std.mkHashMap
end HashMap



section EStateM
  def EStateM.bail! :=
    @EStateM.throw

  export EStateM (Result bail!)
end EStateM


def 𝕂
  {α : Type u}
  {β : Type v}
  (val : β)
: α → β :=
  fun _ => val



def plural
  {α : Type u}
  (notPlural : α)
  (plural : α)
: Nat → α
| 0 | 1 => notPlural
| _ => plural

def plural.s
: Nat → String :=
  plural "" "s"



def EStateM.mapError
  (self : EStateM ε σ α)
  (f : ε → ε')
: EStateM ε' σ α :=
  do
    let state ←
      get
    match self.run state with
    | .ok res state =>
      set state
      pure res
    | .error err state =>
      set state
      Result.error (f err)



section ArrayIdx
  /-- Monad version of [`Array.foldlIdx`]. -/
  @[inline]
  def Array.foldlIdxM
    {α : Type u}
    {β : Type v}
    {m : Type v → Type w}
    [Monad m]
    (as : Array α)
    (f : β → Fin as.size → α → m β)
    (init : β)
  : m β :=
    let rec @[specialize] foldl
      (i j : Nat)
      (inv : i + j = as.size)
      (acc : β)
    : m β := do
      match i, inv with
      | 0,    _  => pure acc
      | i+1, inv =>
        have : j < as.size := by
          rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
          apply Nat.le_add_right
        let idx : Fin as.size := ⟨j, this⟩
        have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
        let acc ← f acc idx (as.get idx)
        foldl i (j+1) this acc
    foldl as.size 0 rfl init

  /-- Folds left over the elements and their indices as `Fin self.size`. -/
  def Array.foldlIdx
    (self : Array α)
    (fold : β → Fin self.size → α → β)
    (init : β)
  : β :=
    self.foldlIdxM fold init
    |> Id.run

  def Array.foldlIdx!
    (self : Array α)
    (fold : β → Fin self.size → α → Except String β)
    (init : β)
  : Except String β :=
    self.foldlIdxM fold init
    

  /-- Type of a legal index of `self`. -/
  def Array.Idx
    (self : Array α)
  : Type :=
    Fin (self.size)
end ArrayIdx



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
end parse


section result
  export EStateM (Result)

  abbrev Res :=
    Result
  abbrev IRes :=
    Result String
  abbrev PRes :=
    Result Parse.Err
end result
