import Err.Res



/-! ## Syntax extensions

The main thing we want is a notation for creating error types and/or error state monads. This is
inspired by Rust's [`error-chain` crate][echain]: the DSL is different but the philosophy is
similar.

[echain]: https://crates.io/crates/error-chain
(error-chain on crates.io)
-/



syntax "inductiveError "
  declId bracketedBinder* (
    "| " ident
      " : " term
  )+
  : command

macro_rules
  | `(
    inductiveError $inductiveName
      $[ | $variant : $resTy ]*
  ) => `(
    inductive $inductiveName
      $[
        | $variant:ident : $resTy
      ]*
  )



inductiveError Error
  | Io : IO.Error → Error
  | Msg : String → Error
