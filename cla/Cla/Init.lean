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



inductive Cla.Either
  (α : outParam (Sort u))
  (β : outParam (Sort u))
| left : α → Either α β
| right : β → Either α β

section Either
  variable
    (self : Cla.Either α β)

  def Cla.Either.collapse
    (f : α → γ)
    (g : β → γ)
  : Either α β → γ
    | left a => f a
    | right b => g b

  def Cla.Either.left?
  : Option α :=
    self.collapse some (𝕂 none)

  def Cla.Either.right?
  : Option β :=
    self.collapse (𝕂 none) some

  def Cla.Either.mapLeft
    (f : α → γ)
  : Either γ β :=
    self.collapse
      (f · |> left)
      right

  def Cla.Either.mapRight
    (f : β → γ)
  : Either α γ :=
    self.collapse
      left
      (f · |> right)
end Either


section parse
  inductive Cla.Parse.Opt
  | long : String → Opt
  | short : Char → Opt
  deriving Repr, BEq

  def Cla.Parse.Opt.toString
  : Opt → String
  | long l => s!"--{l}"
  | short s => s!"-{s}"

  instance instToStringParseOpt
  : ToString Cla.Parse.Opt :=
    ⟨Cla.Parse.Opt.toString⟩



  inductive Cla.Parse.Arg
  | val : String → Arg
  | sep : Arg
  | opt : Opt → Arg
  deriving Repr, BEq

  section helpers
    def Cla.Parse.Arg.long
    : String → Arg :=
      (Opt.long · |> opt)
    def Cla.Parse.Arg.short
    : Char → Arg :=
      (Opt.short · |> opt)

    def Cla.Parse.Arg.isVal
    : Cla.Parse.Arg → Bool
    | .val _ => true
    | .sep => false
    | .opt _ => false

    def Cla.Parse.Arg.isOpt
    : Cla.Parse.Arg → Bool
    | .val _ => false
    | .sep => false
    | .opt _ => true

    def Cla.Parse.Arg.isSep
    : Cla.Parse.Arg → Bool
    | .val _ => false
    | .sep => true
    | .opt _ => false

    def Cla.Parse.Arg.getVal
    : Cla.Parse.Arg → Option String
    | .val v => v
    | .sep => none
    | .opt _ => none

    def Cla.Parse.Arg.getOpt
    : Cla.Parse.Arg → Option Opt
    | .val _ => none
    | .sep => none
    | .opt o => o
  end helpers
  
  def Cla.Parse.Arg.toString
  : Arg → String
  | .val v => v
  | .sep => "--"
  | .opt o => o.toString

  instance instToStringParseArg
  : ToString Cla.Parse.Arg :=
    ⟨Cla.Parse.Arg.toString⟩



  structure Cla.Parse.Err where
    arg : Option Arg
    msg : String
  deriving Repr, BEq
  
  def Cla.Parse.Err.toString
    (self : Err)
  : String :=
    if let some arg := self.arg then
      s!"on `{arg}`: {self.msg}"
    else self.msg

  instance instToStringParseErr
  : ToString Cla.Parse.Err :=
    ⟨Cla.Parse.Err.toString⟩
end parse


section result
  export EStateM (Result)

  abbrev Res :=
    Result
  abbrev IRes :=
    Result String
  abbrev PRes :=
    Result Cla.Parse.Err
end result













-- abbrev SRes (α : Type u) :=
--   Except String α

-- structure AbsArg (In : Type u) where
--   resType : Type v
--   validate : In → SRes resType
-- deriving Inhabited

-- def AbsArg.inType
--   (_ : AbsArg In)
-- := In


-- abbrev Arg :=
--   AbsArg String
-- namespace Arg
--   export AbsArg (mk inType)

--   def ofOption
--     (desc: String)
--     (get? : String → Option α)
--   : Arg where
--     resType := α
--     validate s :=
--       if let some res := get? s then
--         .ok res
--       else
--         .error s! "expected {desc}, got {s}"

--   def mkString : Arg where
--     resType := String
--     validate := pure

--   def mkNat :=
--     ofOption "natural number" String.toNat?

--   def mkInt :=
--     ofOption "integer" String.toInt?
-- end Arg

-- abbrev ArgTail :=
--   AbsArg <| List String
-- namespace ArgTail
--   export AbsArg (mk inType)

--   def mkListString : ArgTail where
--     resType := List String
--     validate := pure
-- end ArgTail

-- structure Args.{u} where
--   args : Array Arg.{u}
--   tail : Option ArgTail.{u}

-- def Args.empty : Args where
--   args := #[]
--   tail := none

-- def Args.push
--   (self : Args)
--   (arg : Arg)
-- : Args := {
--   self with
--     args := self.args.push arg
-- }

-- def Args.typeFoldr
--   (self : Args.{u})
--   (fArg : Arg → α → α)
--   (fTail : ArgTail → α → α)
--   (init : α)
-- : α :=
--   let init :=
--     self.tail.map (fTail · init)
--     |>.getD init
--   self.args.foldr fArg init

-- def Args.inType
--   (self : Args.{u})
-- : Type :=
--   Unit
--   |> self.typeFoldr
--     (fun arg acc => arg.inType → acc)
--     (fun tail acc => tail.inType → acc)

-- def Args.outType
--   (self : Args.{u})
--   (α : Type u)
-- : Type u :=
--   SRes α
--   |> self.typeFoldr
--     (fun arg acc => arg.resType → acc)
--     (fun tail acc => tail.resType → acc)

-- def Args.apply
--   (self : Args.{u})
--   (input : self.inType)
--   (action : self.outType α)
-- : SRes α :=
--   by
--     simp [outType, typeFoldr, Array.foldr, Array.foldrM] at action
--     cases h : self.args.data with
--     | cons hd tl =>
--       rw [h] at action
--       simp [outType.loop] at action
--       sorry
--     | nil =>
--       match self.tail with
--       | some tail => sorry
--       | none => sorry

-- def Args.test : IO Unit :=
--   let args :=
--     Args.mk
--       #[Arg.mkNat, Arg.mkString, Arg.mkInt]
--     <|some ArgTail.mkListString

--   let eatAll
--     (n : Nat) (s : String) (i : Int) (tail : List String)
--   : IO Unit :=
--     do
--       println! "n: {n}, s: `{s}`, i: {i}"
--       println! "tail:"
--       for elm in tail do
--         println! "- `{elm}`"

  

--   return ()
