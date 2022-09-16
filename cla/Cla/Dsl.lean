import Cla.ParseDefs



/-! ## The DSL that makes everything super nice -/
namespace Cla.Dsl

open Lean



section flag

  syntax pShort :=
    "-" ( char <|> ("(" term ")") )
  def parseShort : TSyntax `Cla.Dsl.pShort → MacroM Term
    | `(pShort| - $c:char) => `($c)
    | `(pShort| - ( $t:term )) => `($t)
    | _ => Macro.throwUnsupported

  syntax pLong :=
    "─" ( str <|> ("(" term ")") )
  def parseLong : TSyntax `Cla.Dsl.pLong → MacroM Term
    | `(pLong| ─ $s:str) => `($s)
    | `(pLong| ─ ( $t:term )) => `($t)
    | _ => Macro.throwUnsupported

  syntax pFlags :=
    (pShort)?
    (pLong)?

  def handleFlag : TSyntax `Cla.Dsl.pFlags → MacroM Term
    | `(pFlags| $short:pShort) =>
      do `((some $(← parseShort short), none))
    | `(pFlags| $long:pLong) =>
      do `((none, some $(← parseLong long)))
    | `(pFlags| $short:pShort $long:pLong) =>
      do `((some $(← parseShort short), some $(← parseLong long)))
    | `(pFlags| ) =>
      Macro.throwError "expected a short flag, a long flag, or both"
    | _ => Macro.throwUnsupported



  declare_syntax_cat pCardBounds
  syntax "∞" : pCardBounds
  syntax num (", " (num <|> "∞"))? : pCardBounds
  syntax "≤ " num : pCardBounds

  def handleBounds : TSyntax `pCardBounds → MacroM Term
    | `(pCardBounds| ∞) => `(Cla.ArgSpec.Bounds.mk none none)
    | `(pCardBounds| $n:num) => `(
        Cla.ArgSpec.Bounds.mk (some $n) (some $n)
    )
    | `(pCardBounds| $min:num, $max:num) =>
        `(Cla.ArgSpec.Bounds.mk (some $min) (some $max))
    | `(pCardBounds| $min:num, ∞) =>
        `(Cla.ArgSpec.Bounds.mk (some $min) none)
    | `(pCardBounds| ≤ $max:num) =>
        `(Cla.ArgSpec.Bounds.mk none (some $max))
    | _ => Macro.throwUnsupported

  syntax pCard :=
    "arity" pCardBounds

  def handleCard : TSyntax `Cla.Dsl.pCard → MacroM Term
    | `(pCard| arity $bounds:pCardBounds) =>
      do `( $(← handleBounds bounds) )
    | _ => Macro.throwUnsupported



  syntax pHandler :=
    "update " ident
      (
        " taking "
          ( "(" ident+ " : " "String" ")" )?
          ( "(" ident " : " "List String" ")" (" < " num)? )?
      )?
    " := " term

  def handleHandler : TSyntax `Cla.Dsl.pHandler → MacroM Term
    | `(pHandler|
      update $state := $body
    ) => `(
        let bounds :=
          Cla.ArgSpec.Bounds.zero
        (bounds, (
          fun () =>
            do
              let $state ← get
              set ($body)
          : bounds.Validator
        ))
      )
    | `(pHandler|
      update $state taking ($head $tail* : String) := $body
    ) =>
      let arity :=
        tail.size + 1
        |> toString
        |> Lean.Syntax.mkLit `term
      `(
        let bounds :=
          Cla.ArgSpec.Bounds.exact $arity
        (bounds, (
          fun | ($head, $tail,*) =>
              do
                let $state ← get
                  set ($body)
          : bounds.Validator
        ))
      )
    | `(pHandler|
      update $state taking ($head $tail* : String) ($list : List String) := $body
    ) =>
      let arity :=
        tail.size + 1
        |> toString
        |> Lean.Syntax.mkLit `term
      `(
        let bounds :=
          Cla.ArgSpec.Bounds.atLeast $arity
        (bounds, (
          fun | ($head, $tail,* , $list) =>
              do
                let $state ← get
                  set ($body)
          : bounds.Validator
        ))
      )
    | `(pHandler|
      update $state taking ($head $tail* : String) ($list : List String) < $max := $body
    ) =>
      do
        let arity :=
          tail.size + 1
          |> toString
          |> Lean.Syntax.mkLit `term
            (info := ← MonadRef.mkInfoFromRefPos)
        `(
          let bounds :=
            Cla.ArgSpec.Bounds.between $arity $max
          (bounds, (
            fun | ($head, $tail,* , $list) =>
                do
                  let $state ← get
                    set ($body)
            : bounds.Validator
          ))
        )
      | _ => Macro.throwUnsupported

end flag

