import Category.Init


/-!
# Category **FPL**

`Fpl` is the **FPL** category:
- objects are all `int`, `real`, `bool` and `unit`, and
- arrows are the following operations:
  - identity on all four objects
  - `isZero : int → bool`
  - `not : bool → bool`
  - `succᵢ : int → int`
  - `succᵣ : real → real`
  - `toReal : int → real`
  - `zero : unit → int`
  - `true : unit → Bool`
  - `false : unit → Bool`
  - `unit : unit → unit`
-/



namespace Fpl

open Lean (Rat)



inductive Obj : Type 1
  --- Naturals.
  | N
  --- Rationals.
  | R
  --- Bool.
  | B
  --- Unit.
  | U
deriving Inhabited, BEq

abbrev nat :=
  Obj.N
abbrev rat :=
  Obj.R
abbrev bool :=
  Obj.B
abbrev unit :=
  Obj.U

abbrev Obj.concrete : Obj → Type
  | N => Nat
  | R => Rat
  | B => Bool
  | U => Unit



inductive Val
  | N : Obj.N.concrete → Val
  | R : Obj.R.concrete → Val
  | B : Obj.B.concrete → Val
  | U : Obj.U.concrete → Val
deriving Inhabited, BEq

abbrev Val.type : Val → Obj
  | N _ => Obj.N
  | R _ => Obj.R
  | B _ => Obj.B
  | U _ => Obj.U



abbrev F (α β : Obj) : Type :=
  α.concrete → β.concrete

infix:min " ⇒ " => F



abbrev F.id (α : Obj) : α ⇒ α :=
  fun val => val



abbrev F.tru : unit ⇒ bool :=
  𝕂 true

abbrev F.fls : unit ⇒ bool :=
  𝕂 false

abbrev F.not : bool ⇒ bool :=
  fun b => !b



abbrev F.isZero : nat ⇒ bool :=
  fun
    | 0 => true
    | _ + 1 => false

abbrev F.succᵢ : nat ⇒ nat :=
  (· + 1)

abbrev F.zero : unit ⇒ nat :=
  𝕂 0

abbrev F.toRat : nat ⇒ rat :=
  (Lean.mkRat · 1)



abbrev F.succᵣ : rat ⇒ rat :=
  (· + 1)



@[reducible]
inductive A : Obj → Obj → Type 1
  | id : {γ : Obj} → A γ γ
  | tru : A unit bool
  | fls : A unit bool
  | not : A bool bool
  | isZero : A nat bool
  | succᵢ : A nat nat
  | zero : A unit nat
  | toRat : A nat rat
  | succᵣ : A rat rat
  | comp : (A β γ) → (A α β) → A α γ

abbrev A.concrete : A α β → (α ⇒ β)
  | id => F.id α
  | tru => F.tru
  | fls => F.fls
  | not => F.not
  | isZero => F.isZero
  | succᵢ => F.succᵢ
  | zero => F.zero
  | toRat => F.toRat
  | succᵣ => F.succᵣ
  | comp f g => f.concrete ∘ g.concrete
abbrev A.χ :=
  @A.concrete



theorem A.concrete_comp
  (f : A β γ)
  (g : A α β)
: f.χ ∘ g.χ = (f.comp g).χ
:=
  rfl

theorem A.concrete_comp_assoc
  (f : A γ δ)
  (g : A β γ)
  (h : A α β)
: (f.comp (g.comp h)).χ = ((f.comp g).comp h).χ
:=
  rfl



theorem A.id_comp
  (f : A α β)
: (id.comp f).χ = f.χ
:=
  rfl
theorem A.comp_id
  (f : A α β)
: (f.comp id).χ = f.χ
:=
  rfl



theorem A.comp_not_not
: (not.comp not).χ = id.χ
:=
  funext (by simp)
theorem A.comp_not_tru
: (not.comp tru).χ = fls.χ
:=
  rfl
theorem A.comp_not_fls
: (not.comp fls).χ = tru.χ
:=
  rfl



theorem A.comp_isZero_zero
: (isZero.comp zero).χ = tru.χ
:=
  rfl

theorem A.comp_isZero_succᵢ
: (isZero.comp (succᵢ.comp f)).χ = fls.χ
:=
  rfl



end Fpl


/-! ## FPL is a category -/

def Cat.Fpl : Cat Fpl.Obj Fpl.Obj.concrete Fpl.A Fpl.F where
  aConcrete :=
    Fpl.A.concrete

  compose :=
    Fpl.A.comp
  compose_assoc :=
    Fpl.A.concrete_comp_assoc

  id :=
    Fpl.A.id
  id_compose :=
    Fpl.A.id_comp
  compose_id :=
    Fpl.A.comp_id

