/-! Specialization library. 

-/

namespace Spe

open Except (ok error)



/-- Can check an `α`-value. -/
structure Check (ε α : Type u) : Type u where
  /-- Okay if legit, error otherwise. -/
  check : α → Except ε Unit

/-- Proposition corresponding to [`Check.check`] being `ok ()`. -/
@[simp]
def Check.isLegit
  (self : Check ε α)
  (val : α)
: Prop :=
  self.check val = ok ()

/-- [`Check.isLegit`] is decidable. -/
instance instDecIsLegit
  {self : Check ε α}
  {val : α}
: Decidable (self.isLegit val) :=
  match legit? : self.check val with
  | ok () => isTrue legit?
  | error _ => isFalse (
    by
      simp
      intro h
      rw [legit?] at h
      contradiction
  )

/-- [`Check`] coerces to function [`Check.isLegit`]. -/
instance instCoeFunCheck
: CoeFun (Check ε α) (fun _ => α → Prop) where
  coe self :=
    self.isLegit



/-- Wraps an `α`, the [`Check`] function, and a proof of legitimacy. -/
structure Legit (ε α : Type u) where
private mk ::
  val : α
  check : Check ε α
  legit : check val

/-- [`Legit`] coerces to [`Legit.val`]. -/
instance instCoeLegit : Coe (Legit ε α) α where
  coe self :=
    self.val



section
  variable
    {ε α : Type u}

  /-- Tries to build a legitimate `α`. -/
  def Legit.mk?
    (check : Check ε α)
    (val : α)
  : Except ε <| Legit ε α :=
    match legit : check.check val with
    | ok () => ok ⟨val, check, legit⟩
    | error e => error e

  /-- Alias for [`Legit.mk?`] -/
  abbrev Check.validate? :=
    @Legit.mk?

  /-- Builds the [`Check`] corresponding to being a member of a list of values. -/
  def Check.ofList
    [DecidableEq α]
    (set : List α)
    (err : (a : α) → a ∉ set → ε)
  : Check ε α where
    check val :=
      if mem? : val ∈ set
      then ok ()
      else error <| err val mem?

  /-- Proof that legit value cannot be `val` if `val` is not legit. -/
  theorem Legit.absurd
    (self : Legit ε α)
    (val : α)
    (illegit : ¬(self.check val) := by dsimp)
  : self.val ≠ val :=
    by
      intro h
      rw [←h] at illegit
      apply illegit self.legit
end


namespace Demo

  inductive Test
  | Var1
  | Var2
  | Var3
  deriving BEq, DecidableEq, Hashable, Repr

  instance instToStringTest : ToString Test where
    toString
    | .Var1 => "Var1"
    | .Var2 => "Var2"
    | .Var3 => "Var3"

  def list12 : List Test :=
    [Test.Var1, Test.Var2]

  def errMsg (l : List Test) (a : Test) (_ : a ∉ l) : String :=
    s! "value `{a}` is not a member of [{pretty}]"
  where
    pretty :=
      "" |> l.foldl
        fun (s : String) (val : Test) => -- fold
          if s.isEmpty then toString val
          else s ++ ", " ++ (toString val)

  def not3 : Check String Test :=
    Check.ofList list12 (errMsg list12)

  #eval (
    match not3.validate? Test.Var1 with
    | .ok legit => "ok " ++ toString legit.val
    | .error msg => "error: " ++ msg
  )
  #eval (
    match not3.validate? Test.Var2 with
    | .ok legit => "ok " ++ toString legit.val
    | .error msg => "error: " ++ msg
  )
  #eval (
    match not3.validate? Test.Var3 with
    | .ok legit => "ok " ++ toString legit.val
    | .error msg => "error: " ++ msg
  )

end Demo

