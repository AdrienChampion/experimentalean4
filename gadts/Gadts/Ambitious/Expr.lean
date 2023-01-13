import Gadts.Ambitious.Theories

inductive Pretend : Typ → Type
| nil : Pretend α
| cons {α : Typ} : α.ops.many.type → Array (Pretend α) → Pretend α
| doesNotBreakEveryting {α : Typ} : α → Pretend α → Pretend α
-- | breaksEveryting : Bool → Pretend Typ.bool → Pretend Typ.bool

inductive Expr : Typ → Type
| var {α : Typ} :
  String → Expr α
| cst {α : Typ} :
  α.type → Expr α
| ite {α : Typ} :
  Expr Typ.bool → Expr α → Expr α → Expr α
| eq {α : Typ} :
  Expr α → Expr α → Expr α
-- -- operators
-- | opUn {α : Typ} :
--   α.ops.un.type → Expr α → Expr α
-- | opBin {α : Typ} :
--   α.ops.bin.type → Expr α → Expr α → Expr α
-- | opMany {α : Typ} :
--   α.ops.many.type → Array (Expr α) → Expr α
-- | opMany1 {α : Typ} :
--   α.ops.many1.type → Expr α → Array (Expr α) → Expr α
-- | opMany2 {α : Typ} :
--   α.ops.many2.type → Expr α → Expr α → Array (Expr α) → Expr α
-- relations
-- | relUn {α : Typ} :
--   α.rels.un.type → Expr α → Expr Typ.bool
-- | relBin {α : Typ} :
--   α.rels.bin.type → Expr α → Expr α → Expr Typ.bool
-- | relMany {α : Typ} :
--   α.rels.many.type → Array (Expr α) → Expr Bool
-- | relMany1 {α : Typ} :
--   α.rels.many1.type → Expr α → Array (Expr α) → Expr Bool
-- | relMany2 {α : Typ} :
--   α.rels.many2.type → Expr α → Expr α → Array (Expr α) → Expr Bool

-- abbrev Expr.B := Expr Typ.bool
-- def Expr.B.cst := @Expr.cst Typ.bool
-- def Expr.B.var := @Expr.var Typ.bool
-- def Expr.B.unApp := @Expr.unApp Typ.bool
-- def Expr.B.ite := @Expr.ite Typ.bool

-- abbrev Expr.N := Expr Typ.nat
-- def Expr.N.cst := @Expr.cst Typ.nat
-- def Expr.N.var := @Expr.var Typ.nat
-- def Expr.N.unApp := @Expr.unApp Typ.nat
-- def Expr.N.ite := @Expr.ite Typ.nat

-- def Expr.neg : Expr Typ.bool → Expr Typ.bool :=
--   Expr.unApp BoolUnOp.neg
-- def Expr.uMinus : Expr Typ.nat → Expr Typ.nat :=
--   Expr.unApp NatUnOp.neg

-- protected def Expr.toString
-- : {typ : Typ} → [ToString typ.unOps] → (e : Expr typ) → String
--   | _, _, .var s => s!"`{s}`"
--   | .bool, _, .cst b =>
--     match b with
--     | true => "true"
--     | false => "false"
--   | .nat, _, .cst n => toString n
--   | _, _, .unApp op sub =>
--     s!"({toString op} {sub.toString})"
--   | _, _, ite cnd thn els =>
--     s!"(if {cnd.toString} then {thn.toString} else {els.toString})"

-- instance instToStringExpr : ToString <| Expr typ :=
--   ⟨Expr.toString⟩

-- #eval
--   let tru := Expr.B.cst true
--   let fls := Expr.B.cst false
--   let one := Expr.N.cst 1
--   let bVar := Expr.B.var "b"
--   let nVar := Expr.N.var "n"
--   Expr.ite tru.neg
--     (Expr.ite fls.neg one one.uMinus)
--     (Expr.ite bVar nVar nVar.uMinus)
--   |> toString
-- --> "(if (¬ true) then (if (¬ false) then 1 else (- 1)) else (if `b` then `n` else (- `n`)))"