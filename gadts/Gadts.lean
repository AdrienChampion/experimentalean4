inductive Typ
| bool
| nat

abbrev Typ.type : Typ → Type
| .bool => Bool
| .nat => Nat

inductive BoolUnOp
| neg
def BoolUnOp.toString : BoolUnOp → String
| .neg => "¬"
instance : ToString BoolUnOp := ⟨BoolUnOp.toString⟩

inductive NatUnOp
| neg
def NatUnOp.toString : NatUnOp → String
| .neg => "-"
instance : ToString NatUnOp := ⟨NatUnOp.toString⟩

abbrev Typ.unOps : Typ → Type
| .bool => BoolUnOp
| .nat => NatUnOp

instance instToStringTypUnOps {typ : Typ} : ToString typ.unOps :=
  match typ with
  | .bool => inferInstance
  | .nat => inferInstance



inductive Expr : Typ → Type
| var : String → Expr typ
| cst : {typ : Typ} → typ.type → Expr typ
| unApp : {typ : Typ} → typ.unOps → Expr typ → Expr typ
| ite : Expr Typ.bool → Expr typ → Expr typ → Expr typ

abbrev Expr.B := Expr Typ.bool
def Expr.B.cst := @Expr.cst Typ.bool
def Expr.B.var := @Expr.var Typ.bool
def Expr.B.unApp := @Expr.unApp Typ.bool
def Expr.B.ite := @Expr.ite Typ.bool

abbrev Expr.N := Expr Typ.nat
def Expr.N.cst := @Expr.cst Typ.nat
def Expr.N.var := @Expr.var Typ.nat
def Expr.N.unApp := @Expr.unApp Typ.nat
def Expr.N.ite := @Expr.ite Typ.nat

def Expr.neg : Expr Typ.bool → Expr Typ.bool :=
  Expr.unApp BoolUnOp.neg
def Expr.uMinus : Expr Typ.nat → Expr Typ.nat :=
  Expr.unApp NatUnOp.neg

protected def Expr.toString
: {typ : Typ} → [ToString typ.unOps] → (e : Expr typ) → String
  | _, _, .var s => s!"`{s}`"
  | .bool, _, .cst b =>
    match b with
    | true => "true"
    | false => "false"
  | .nat, _, .cst n => toString n
  | _, _, .unApp op sub =>
    s!"({toString op} {sub.toString})"
  | _, _, ite cnd thn els =>
    s!"(if {cnd.toString} then {thn.toString} else {els.toString})"

instance instToStringExpr : ToString <| Expr typ :=
  ⟨Expr.toString⟩

#eval
  let tru := Expr.B.cst true
  let fls := Expr.B.cst false
  let one := Expr.N.cst 1
  let bVar := Expr.B.var "b"
  let nVar := Expr.N.var "n"
  Expr.ite tru.neg
    (Expr.ite fls.neg one one.uMinus)
    (Expr.ite bVar nVar nVar.uMinus)
  |> toString
--> "(if (¬ true) then (if (¬ false) then 1 else (- 1)) else (if `b` then `n` else (- `n`)))"