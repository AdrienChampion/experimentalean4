import Cla.ParseDefs



/-! # An example of using `Cla` -/

namespace Cla.Example



structure Conf where
  verb : Nat
  inputs : List String
  output : Option String
deriving Repr, Inhabited



def Conf.default : Conf where
  verb := 1
  inputs := []
  output := none

section Conf
  variable
    (self : Conf)

  def Conf.verbDo
    (action : Nat → Nat)
  : Conf := {
    self with
      verb := action self.verb
  }

  def Conf.addInputs
    (inputs : List String)
  : Conf := {
    self with
      inputs := self.inputs ++ inputs
  }

  def Conf.addInput
    (input : String)
  : Conf :=
    self.addInputs [input]

  def Conf.revInputs : Conf := {
    self with inputs := self.inputs.reverse
  }
end Conf



section Parse
  variable
    (self : Conf)

  def Conf.clap.short
  : Char → IParseM Conf
    | 'v' =>
      self.verbDo (· + 1)
      |> pure
    | flag =>
      EStateM.throw s! "unexpected flag `-{flag}`"

  def Conf.clap.long
  : String → IParseM Conf
    | "verb"
    | "verbose" =>
      do
        let arg ←
          Parse.nextFlagArg
        if let some verb := arg.toNat? then
          self.verbDo (𝕂 verb)
          |> pure
        else
          EStateM.throw s! "expected natural, got `{arg}`"
    | "input" =>
      do
        let arg ←
          Parse.nextFlagArg
        self.addInput arg
        |> pure
    | "inputs" =>
      do
        Parse.foldFlagArgs
          (min := 1)
          (max := none)
          (fold := Conf.addInput)
          (init := self)
    | flag =>
      EStateM.throw s! "unexpected flag `--{flag}`"

  def Conf.clap.val
  : String → Nat → IParseM Conf
    | output, 0 =>
      { self with output := output }
      |> pure
    | spurious, _ =>
      EStateM.throw
        s! "already have one value (`{self.output}`), value `{spurious}` is unexpected"

  def Conf.clap
  : EParseM Parse.Err Conf :=
    do
      let conf ←
        Parse.loopDo
          clap.long
          clap.short
          clap.val
          (fun _ conf => conf)
          Conf.default
      if conf.output.isNone then
        Parse.Err.mk
          none
          s! "no output file was provided, expected exactly one"
        |> EStateM.throw
      else if conf.inputs.isEmpty then
        Parse.Err.mk
          none
          s! "no input file was provided, expected at least one"
        |> EStateM.throw
      else
        conf.revInputs
        |> pure
end Parse



namespace Tests

  def test
    (args : String)
  : String :=
    let parser :=
      Parse.mk args.splitOn
    match EStateM.run Conf.clap parser with
    | .ok conf _ =>
      s! "okay: {reprPrec conf 1}"
    | .error err _ =>
      s! "error: {err}"

  def test₁ :=
    test "--input input₁ -v -v --input input₂ output"
  #eval test₁

  def test₂ :=
    test "--input input₁ -v -v --input input₂ output --verbose 27"
  #eval test₂

  def test₃ :=
    test "--input input₁ -v -v --input input₂ output --verbose 27 -v -v"
  #eval test₃

  def test₄ :=
    test "--inputs input₁ input₂ -- output"
  #eval test₄



  def error₀ :=
    test "output"
  #eval error₀

  def error₁ :=
    test "output₁ output₂"
  #eval error₁

  def error₂ :=
    test "--input input₁ output₁ output₂"
  #eval error₂

  def error₃ :=
    test "--inputs input₁ input₂ output"
  #eval error₃


end Tests



namespace Conf.flag
  def v : Flag Conf :=
    Flag.withDesc
      "increases verbosity"
    |>.withShort 'v'
    |>.effect (
      fun () =>
        do
          let conf ← get
          conf.verbDo (fun v => v + 1)
          |> set
    )

  def q : Flag Conf :=
    Flag.withDesc
      "decreases verbosity"
    |>.withShort 'q'
    |>.effect (
      fun () =>
        do
          let conf ← get
          conf.verbDo (fun v => v - 1)
          |> set
    )

  def verb : Flag Conf :=
    Flag.withDesc
      s! "sets the verbosity (default {Conf.default.verb})"
    |>.withLong "verb"
    |>.argsTake 1
    |>.effect (
      fun verb =>
        do
          if let some verb := verb.toNat?
          then
            let conf ← get
            conf.verbDo (𝕂 verb)
            |> set
    )

  def quiet : Flag Conf :=
    Flag.withDesc
      "sets verbosity to zero"
    |>.withLong "quiet"
    |>.effect (
      fun () =>
        do
          let conf ← get
          conf.verbDo (𝕂 0)
          |> set
    )

  def inputs : Flag Conf :=
    Flag.withDesc
      "inputs, requires two values or more"
    |>.withLong "inputs"
    |>.argsAtLeast 2
    |>.effect (
      fun (h₁, h₂, tail) =>
        do
          let conf ← get
          conf
          |>.addInputs [h₁, h₂]
          |>.addInputs tail
          |> set
    )
end Conf.flag

protected def Conf.com : Com Conf :=
  let com? :=
    Com.mkBuilder
      Conf
      "myProgram"
    |>.withFlags [
      flag.v,
      flag.q,
      flag.verb,
      flag.quiet,
      flag.inputs
    ]
    |>.build
  match com? with
  | .ok com => com
  | .error err =>
    panic! s! "Failed to build command: {err}"

def Conf.parse : List String → Except Parse.Err Conf :=
  Parse.run Conf.com Conf.default


#eval Conf.parse [
  "--verb", "662",
  "-vvvv",
  "--inputs", "in₁", "in₂", "in₃", "in₄"
]
