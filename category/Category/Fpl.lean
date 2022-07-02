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

*Monoid homomorphisms* preserve the neutral element and are proper *w.r.t.* the monoid's
multiplication.
-/



namespace Mon.Fpl

  inductive All
  | int
  | real
  | bool
  | unit

  inductive ArrowIB
  | isZero
  inductive ArrowUB
  | tru
  | fls
  inductive ArrowUI
  | zero

  inductive ArrowUU
  | unit
  | id
  inductive ArrowII
  | succᵢ
  | id
  inductive ArrowBB
  | not
  | id
  inductive ArrowRR
  | succᵣ
  | id



end Mon.Fpl