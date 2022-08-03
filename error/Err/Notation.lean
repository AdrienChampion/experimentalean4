import Err.Res



/-! ## Syntax extensions

The main thing we want is a notation for creating error types and/or error state monads. This is
inspired by Rust's [`error-chain` crate][echain]: the DSL is different but the philosophy is
similar.

[echain]: https://crates.io/crates/error-chain
(error-chain on crates.io)
-/



syntax
  declModifiers
  "inductiveError " declId bracketedBinder*
  -- ("extends " withPosition(group(colGe term ","?)*))?
  (":" term)?
  (
    ("|" ident optDeclSig)
  )*
: command

macro_rules
  | `(
    $mods:declModifiers
    inductiveError $inductiveName:declId $params:bracketedBinder*
    $[: $ty:term]?
    $[ | $variant:ident $sig?:optDeclSig ]*
  ) => `(
    $mods:declModifiers
    inductive $inductiveName:declId
      $[$params:bracketedBinder]*
      $[: $ty:term]?
      $[
        | $variant:ident $sig?:optDeclSig
      ]*
  )



inductiveError Error
  | Io : IO.Error → Error
  | Msg : String → Error
