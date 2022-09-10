import Cla.Init

def String.splitCommas
  (s : String)
: List Substring :=
  s.toSubstring.splitOn ","



def String.claKindDo
  (longAction : Substring → α)
  (shortAction : Substring → α)
  (valAction : String → α)
  (sepAction : α)
  (s : String)
: α :=
  match (Pos.mk 0 |> s.get?, Pos.mk 1 |> s.get?, Pos.mk 2 |> s.get?) with
  | ('-', '-', none) =>
    sepAction
  | ('-', '-', some _) =>
    s.toSubstring.drop 2
    |>.trim
    |> longAction 
  | ('-', _, _) =>
    s.toSubstring.drop 1
    |>.trim
    |> shortAction
  | _ =>
    valAction s

def String.isLongFlag
: String → Bool :=
  claKindDo
    (𝕂 true)
    (𝕂 false)
    (𝕂 false)
    false

def String.isShortFlag
: String → Bool :=
  claKindDo
    (𝕂 false)
    (𝕂 true)
    (𝕂 false)
    false

def String.isVal
: String → Bool :=
  claKindDo
    (𝕂 false)
    (𝕂 false)
    (𝕂 true)
    false

def String.isSep
: String → Bool :=
  claKindDo
    (𝕂 false)
    (𝕂 false)
    (𝕂 false)
    true

/-- Argument handler.

Used through [`Parse.nextDo`], which parses short flags, long flags **and** their arguments, and
plain values.

A *plain value* `val` is a string that is *i)* not a flag and *ii)* not a flag argument. Plain value
have a notion of *index*, a [`Nat`] equal to the number of plain values seen before `val`.

```text
--long arg1,arg2 plain0 plain1 -s plain2 -t arg1 plain3
                   0      1         2              3
```

The difference between a flag argument and a plain value is enforced by whatever [`Parse.nextDo`] is
ordered to do. Basically, `Parse.valIdx` is incremented everytime [`Parse.nextDo`] is called on a
[`Parse.Arg.val`].
-/
structure Parse where protected innerMk ::
  args : List Parse.Arg
  /-- Index of the next plain value. -/
  valIdx : Nat
deriving Repr, BEq

/-- Sanitizes the list of arguments.

- `-abcde` is split in `-a`, `-b`, `-c`...
- `--flag=blah` is split in `--flag`, `blah`
-/
def Parse.mk
  (args : List String)
: Parse :=
  let args :=
    sanitizeArgs args
  ⟨args, 0⟩
where
  sanitizeArgs args :=
    match args with
    | [] => []
    | arg :: tail =>
      -- splits a string into a list of its characters as strings
      let splitShortMap
        {α : Type}
        (map : Char → α)
        (short : String)
      : List α :=
        let f char acc :=
          map char :: acc
        short.foldr f []

      -- new arguments for `arg`
      let args :=
        arg.claKindDo
          ([Arg.long ·.toString])
          (·.toString |> splitShortMap Arg.short)
          ([Arg.val ·])
          ([Arg.sep])

      args ++ sanitizeArgs tail



def Parse.example.ex1 :=
  Parse.mk ["--long", "arg0", "arg1", "--", "-multishort", "arg2", "arg3"]
#eval Parse.example.ex1



section Parse

  /-- Sets the `args` field. -/
  def Parse.setArgs
    (self : Parse)
    (args : List Arg)
  : Parse :=
    { self with args }

  /-- Increases `valIdx`. -/
  def Parse.incValIdx
    (self : Parse)
  : Parse :=
    { self with valIdx := self.valIdx + 1 }

  /-- Pops the **first** argument, does **not** update `valIdx`. -/
  def Parse.pop
  : Parse → Option Arg × Parse
  | ⟨head :: tail, count⟩ =>
    (head, ⟨tail, count⟩)
  | self@ ⟨[], _⟩ =>
    (none, self)



  abbrev EParseM
    (ε : Type)
    (α : Type)
  :=
    EStateM ε Parse α

  abbrev IParseM :=
    EParseM String

  abbrev ParseM
    (α : Type)
  :=
    EStateM Empty Parse α

  def IParseM.errOnArg
    (self : IParseM α)
    (arg : Parse.Arg)
  : EParseM Parse.Err α :=
    do
      let parser ← get
      match EStateM.run self parser with
      | .ok res parser =>
        set parser
        pure res
      | .error msg parser =>
        set parser
        Parse.Err.mk arg msg
        |> EStateM.throw

  abbrev EParseM.run :=
    @EStateM.run

  abbrev IParseM.run :=
    @EStateM.run

  abbrev ParseM.run :=
    @EStateM.run

  abbrev EParseM.run' :=
    @EStateM.run'

  abbrev IParseM.run' :=
    @EStateM.run'

  abbrev ParseM.run' :=
    @EStateM.run'

  /-- Reads an argument `arg` iff one exists and `consume arg`. -/
  def Parse.readIfM
    (consume : @&Parse.Arg → Bool)
  : ParseM (Option Parse.Arg) :=
    do
      -- get `Parse` state
      let self ← get
      if
        let arg :: args :=
          self.args
      then
        if consume arg
        then
          -- user confirmed argument, update `Parse` state
          self.setArgs args
          |> set
          return arg
        else
          -- user rejected argument
          return none
      else
        -- no next argument
        return none



  def Parse.nextFlagArg?
  : IParseM (Option String) :=
    do
      let self ← get
      let (arg?, self) :=
        self.pop
      match arg? with
      | some Arg.sep =>
        set self
        pure none
      | some (Arg.val v) =>
        set self
        pure v
      | some (Arg.opt _)
      | none =>
        pure none



  def Parse.nextFlagArg
  : IParseM String :=
    do
      let self ← get
      let (arg?, self) :=
        self.pop
      match arg? with
      | some (Arg.val v) =>
        set self
        pure v
      | some arg =>
        EStateM.throw
          s! "expected argument, got `{arg}`"
      | none =>
        EStateM.throw
          s! "expected argument, got nothing"
      


  def Parse.foldFlagArgs
    (min : Option Nat)
    (max : Option Nat)
    (fold : α → String → α)
    (init : α)
  : IParseM α :=
    do
      let mut acc :=
        init
      let mut count := 0
      let stillParsing : Nat → Bool :=
        if let some max := max then
          (· < max)
        else
          𝕂 true
      
      while stillParsing count do
        let self ← get
        match self.pop with
        | (some Arg.sep, self) =>
          set self
          break
        | (some (Arg.val v), self) =>
          set self
          count := count + 1
          acc := fold acc v
        | (some (Arg.opt _), _)
        | (none, _) =>
          break
      
      if let some min := min then
        if count < min then
          throw s! "expected at least {min} arguments, got {count}"

      pure acc



  /-- Consumes something and applies the appropriate function, skips [`Parse.Arg.sep`]-s. -/
  partial def Parse.nextDo
    {α : Type}
    (longDo : String → IParseM α)
    (shortDo : Char → IParseM α)
    (valDo : String → Nat → IParseM α)
  : EParseM Parse.Err (Option α) :=
    do
      let self ← get
      match self.pop with
      | (none, self) =>
        set self -- not necessary
        return none
      | (some arg, self) =>
        set self
        -- let res : ParseT μ (Option α) ←
        match arg with
        | .long l =>
          longDo l
          |>.errOnArg arg
        | .short s =>
          shortDo s
          |>.errOnArg arg
        | .val v =>
          set (←get).incValIdx
          valDo v self.valIdx
          |>.errOnArg arg
        | .sep =>
          nextDo longDo shortDo valDo

  /-- Folds over [`Parse.nextDo`]. -/
  partial def Parse.loopDo
    {α β : Type}
    (longDo : β → String → IParseM α)
    (shortDo : β → Char → IParseM α)
    (valDo : β → String → Nat → IParseM α)
    (foldl : β → α → β)
    (init : β)
  : EParseM Parse.Err β :=
    do
      match ←nextDo (longDo init) (shortDo init) (valDo init) with
      | none => pure init
      | some res =>
        foldl init res
        |> loopDo longDo shortDo valDo foldl


  def Parse.example.ex1.test1 :=
    let loop :=
      Parse.loopDo
        (fun _ s => pure s!"--{s}")
        (fun _ c => pure s!"-{c}")
        (fun _ s n => pure s!"{s}#{n}")
        (fun acc s =>
          if acc.isEmpty then s else s! "{acc}, {s}"
        )
        ""
    IParseM.run' loop ex1
  #eval Parse.example.ex1.test1

end Parse



structure Flag
  (μ : Type → Type u)
  [Monad μ]
  (α : Type)
where
  short : Option Char
  long : Option String
  parseArgs : IParseM α

-- structure PlainVal
--   (μ : Type → Type u)
--   [Monad μ]
--   (α : Type)
-- where
--   validate 
