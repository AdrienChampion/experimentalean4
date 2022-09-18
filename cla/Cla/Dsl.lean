import Lean

import Cla.ParseDefs



/-! ## The DSL that makes everything super nice -/
namespace Cla.Dsl

open Lean Elab Meta



def Str : Expr :=
  mkConst ``String
def Chr : Expr :=
  mkConst ``Char
def LstStr : Expr :=
  mkAppN (mkConst ``List) #[Str]
def OptStr : Expr :=
  mkAppN (mkConst ``Option [Level.zero]) #[Str]
def OptChr : Expr :=
  mkAppN (mkConst ``Option [Level.zero]) #[Chr]


section flags

  syntax shortFlag :=
    " -" ident
  def elabShort?
  : TSyntax `Cla.Dsl.shortFlag → MetaM Expr
    | `(shortFlag| - $id:ident) =>
      do
        let s :=
          id.getId.getString!
        match s.toList with
        | [c] =>
          let n :=
            mkNatLit c.toNat
          let c ←
            mkAppM ``Char.ofNat #[n]
          mkAppM ``some #[c]
        | _ =>
          throwErrorAt id "expected exactly one character for short flag, found `{s}`"
      | _ => throwUnsupportedSyntax

  syntax longFlag :=
    " ─" ident
  def elabLong?
  : TSyntax `Cla.Dsl.longFlag → MetaM Expr
    | `(longFlag| ─ $id:ident) =>
      let s :=
        mkStrLit id.getId.getString!
      mkAppM ``some #[s]
    | _ =>
      throwUnsupportedSyntax

  syntax startFlags :=
    (shortFlag)?
    (longFlag)?

  def elabStartFlags
  : TSyntax `Cla.Dsl.startFlags → TermElabM (Expr × Expr)
    | `(startFlags| $short:shortFlag $long:longFlag) =>
      do
        let s ← elabShort? short
        let l ← elabLong? long
        return (s, l)
    | `(startFlags| $short:shortFlag) =>
      do
        let c ← elabShort? short
        let n0ne ← ``(none)
        let OptStr : Expr ←
          mkAppM ``Option #[Str]
        let n0ne ←Term.elabTerm n0ne (some OptStr)
        return (c, n0ne)
    | `(startFlags| $long:longFlag) =>
      do
        let l ← elabLong? long
        let n0ne ← ``(none)
        let OptChr : Expr ←
          mkAppM ``Option #[Chr]
        let n0ne ←Term.elabTerm n0ne (some OptChr)
        return (n0ne, l)
    | `(startFlags| ) =>
      throwError "expected a short flag, a long flag, or both"
    | _ =>
      throwUnsupportedSyntax

end flags



section argsSpec

  syntax argsSpec :=
    (
      " taking "
        ( "(" ident+ " : " "String" ")" )?
        ( "(" ident " : " "List String" (" ≤ " num)? ")" )?
    )?
    " := " term

  def elabArgsSpec.validator
    (state : Name × Expr)
    (pref : Array Name)
    (tail : Option Name)
    (body : Expr)
  : TermElabM Expr :=
    let (state, stateType) :=
      state
    let argsName : Name :=
      `claReservedArgsIdent
    let argsVar : Expr :=
      Expr.fvar ⟨argsName⟩
    do

      let rec argsTypeAndBindingOfPref
        (path : Expr)
      : List Name → TermElabM (Option (Expr × (Expr → Expr)))
        | hd::tl =>
          let proj1 :=
            mkProj ``Prod 1 path
          let proj2 :=
            mkProj ``Prod 2 path
          do
            match ← argsTypeAndBindingOfPref proj2 tl with
            | some (argsType, bindings) =>
              let argsType ←
                mkAppM ``Prod #[Str, argsType]
              let bindings :=
                fun e =>
                  Expr.letE hd Str proj1 (bindings e) true
              return some (argsType, bindings)
            | none =>
              let binding : Expr → Expr :=
                (Expr.letE hd Str argsVar · true)
              return some (Str, binding)
        | [] =>
          do
            if let some tailName := tail then
              let bindings : Expr → Expr :=
                (Expr.letE tailName LstStr path · true)
              return some (LstStr, bindings)
            else
              return none
      let (argsType, bindings) :=
        (← argsTypeAndBindingOfPref argsVar pref.data).getD (mkConst ``Unit, id)

      withLocalDeclD argsName argsType fun _ =>
        withLocalDeclD state stateType fun _ =>
          return bindings body

  def elabArgsSpec
    (stateStx : TSyntax `term)
    (stateTypeStx : TSyntax `term)
    (stateType : Expr)
  : TSyntax `Cla.Dsl.argsSpec → TermElabM Expr
    | `(argsSpec| := $body) =>
      do
        let bounds :=
          mkConst ``ArgSpec.Bounds.zero
        let bodyFun ←
          ``(fun (_ : Unit) ($stateStx : $stateTypeStx) =>
            match ($body : Except String $stateTypeStx) with
            | .ok state => EStateM.Result.ok () state
            | .error msg => EStateM.Result.error msg $stateStx
          )
        let body ←
          Term.elabTermEnsuringType bodyFun
          <| ← expectedType? bounds
        mkAppM ``ArgSpec.mk #[bounds, body]
      | _ =>
        throwUnsupportedSyntax
  where
    expectedType? (bounds : Expr) : TermElabM <| Option Expr :=
      do
        let type ←
          mkAppM ``ArgSpec.Bounds.Validator #[bounds, stateType, mkConst ``Unit]
        return some type

end argsSpec


section flag

  syntax flag :=
    startFlags ws str argsSpec

  def elabFlag
    (stateStx : TSyntax `term)
    (stateTypeStx : TSyntax `term)
    (stateType : Expr)
  : TSyntax `Cla.Dsl.flag → TermElabM Expr
    | `(flag|
      $flags:startFlags $desc $spec:argsSpec
    ) =>
      do
        let desc ←
          Term.elabTerm desc (mkConst ``String)
        let (short, long) ←
          elabStartFlags flags
        let argsSpec ←
          elabArgsSpec stateStx stateTypeStx stateType spec
        mkAppM ``Flag.mk #[desc, short, long, argsSpec]
    | _ =>
      throwUnsupportedSyntax

end flag



section com
  syntax comItem :=
    flag <|> term

  def elabComItem
    (stateStx : TSyntax `term)
    (stateTypeStx : TSyntax `term)
    (stateType : Expr)
  : TSyntax `Cla.Dsl.comItem → TermElabM Expr
    | `(comItem| $flag:flag) => do
      elabFlag stateStx stateTypeStx stateType flag
    | `(comItem| $term:term) => do
      Term.elabTerm term (some stateType)
    | _ =>
      throwUnsupportedSyntax



  syntax com :=
    ident ( " (" ident " : " term ")" )? " where "
      withPosition(group(colGe "| " comItem))+

  def elabCom
  : TSyntax `Cla.Dsl.com → TermElabM Expr
    | `(com| $name ($stateStx : $stateTypeStx) where $[| $items:comItem]*) => do
      let stateType ←
        Term.elabTerm stateTypeStx none
      let items ←
        items.mapM (elabComItem stateStx stateTypeStx stateType)
      let name :=
        name.getId.toString |> mkStrLit
      let flagType ←
        mkAppM ``Cla.Flag #[stateType]
      let flags ←
        mkAppM ``Flags.mk #[← mkArrayLit flagType items.data]
      mkAppM ``Com.mkM #[name, flags]
    | _ =>
      throwUnsupportedSyntax

end com

-- syntax (name := claTop)
--   "clap! " com
-- : term

-- @[termElab claTop]
-- def claTopImpl : Term.TermElab := fun stx _typ? =>
--   match stx with
--   | `(clap! $com:com) => elabCom com
--   | _ => throwUnsupportedSyntax



scoped elab "clap! " com:com : term =>
  elabCom com



def Test.clap1 : Com Nat :=
  let clap :=
    clap! my_app (n : Nat) where
    | -v
      "increases verbosity"
      := pure (n + 1)
    | -q
      "decreases verbosity"
      := pure (n - 1)
    | ─verb
      "sets the verbosity"
      := pure n
        -- taking (verb : String) :=
        --   if let some n := String.toNat verb then
        --     .ok n
        --   else
        --     .err s! "expected natural, got `{verb}`"
  match clap with
  | .ok clap => clap
  | .error e =>
    panic e

#eval Test.clap1.name