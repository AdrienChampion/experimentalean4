import Cla.Parse



/-! # `Com`mand types and helpers -/

namespace Cla

structure Validator
  (In : Type)
  (σ : Type)
  (α : Type)
where
  validate : In → EStateM String σ α



/-- `M`ulti `Prod`uct, stores a `β` in `n` nested pairs, all with first elements in `α`.

For example, `MProd 3 Nat String` is `Nat × (Nat × (Nat × String))`.

This is used for flags that take *at least `n` arguments*, to a type that stores `n` strings (the
first `n` mandatory arguments), followed by
- nothing if the flag expects exactly `n` arguments;
- `List String` (tail of arguments) if the flag expects at most `m` (`m > n`) arguments or expects
  an unbounded number of arguments.
-/
abbrev MProd
  (n : Nat)
  (α β : Type)
: Type :=
  match n with
  | 0 => β
  | n + 1 => α × (MProd n α β)

example :
  MProd 3 Nat String
  =
  (Nat × Nat × Nat × String)
:=
  rfl

-- pattern matching works too :D
example : MProd 3 Nat String → String
| (_i, _j, _k, s) => s



/-- Number of `α` appearing in an [`MProd`].

That's right, it just returns `n`.
-/
def MProd.countLeft
  (_ : MProd n α β)
: Nat :=
  n



/-- Type for a validator that validates at least `min` and at most `max` arguments.

Number of arguments is unbounded if `max = none`. Accepts no argument at all if `max = 0` or `max =
some m` with `m < min`.
-/
abbrev Validator.forMinMax
  (min : Nat)
  (max : Option Nat)
  (σ : Type)
  (α : Type)
: Type :=
  -- `min` strings followed by a list of strings, used for `[min, max]` intervals where `min < max`
  -- or `max` is `∞`, *i.e.* `none`
  let minThenList :=
    Validator (MProd min String <| List String) σ α

  match max with
  | some max =>
    if max = 0 || max < min then
      Validator Unit σ α
    else if max = min then
      Validator (MProd min String Unit) σ α
    else
      minThenList
  | none =>
    minThenList



structure ArgSpec
  (σ : Type)
where
  min :
    Nat
  max :
    Option Nat
  validator :
    Validator.forMinMax min max σ Unit

section ArgSpec
  variable
    {σ : Type}
    (self : @&ArgSpec σ)

  def ArgSpec.descCountExpected : String :=
    match (self.min, self.max) with
    | (0, none) => "any number of argument"
    | (min, none) => s! "{min} argument{plural.s min} or more"
    | (_, some 0) => "no argument"
    | (min, some max) =>
      if min = max then
        s! "exactly {min} argument{plural.s min}"
      else
        s! "between {min} and {max} argument{plural.s max}"

  def ArgSpec.countBail! : IParseM α :=
    do
      bail! self.descCountExpected
end ArgSpec



structure Flag (σ : Type) where
  short : Option Char
  long : Option String
  desc : String
  argSpec : ArgSpec σ



structure Flags (σ : Type) where
protected innerMk ::
  flags : Array (Flag σ)
  /-- [`Char`] is not [`Hashable`] :( -/
  short : HashMap String flags.Idx
  long : HashMap String flags.Idx

section Flags
  /-- Constructor. -/
  def Flags.mk
    (flags : Array (Flag σ))
  : Except String <| Flags σ :=
    do
      let (short, long) ←
        flags.foldlIdx! foldl init
      pure ⟨flags, short, long⟩
  where
    init := (
      Std.mkHashMap flags.size,
      Std.mkHashMap flags.size
    )
    foldl (state : (HashMap _ _ × HashMap _ _)) idx (flag : Flag σ) :=
      do
        let (short, long) :=
          state
        let short ←
          if let some c := flag.short then
            let (short, notNew) :=
              short.insert' s!"c" idx
            if notNew then
              throw s! "two flags have the same short name `-{c}`"
            else
              pure short
          else
            pure short
        let long ←
          if let some l := flag.long then
            let (long, notNew) :=
              long.insert' l idx
            if notNew then
              throw s! "two flags have the same long name `--{l}`"
            else
              pure long
          else
            pure long
        pure (short, long)
end Flags




/-- Used to build [`CommBuilder`] and [`Comm`].

Abstract description of a command, there's no reason to use this directly.
-/
structure Command
  (F : Type u)
where
  name : String
  flags : F



/-- Stores a [`Flags`] structure.

To build a `Comm` use the [`CommBuilder`], for instance using [`Comm.mkBuilder`].
-/
abbrev Comm
  (σ : Type)
:=
  Command (Flags σ)



section builder
  /-- Stores an array of [`Flag`]s. -/
  abbrev CommBuilder
    (σ : Type)
  :=
    Command (Array <| Flag σ)

  /-- Empty constructor. -/
  def CommBuilder.empty
    (σ : Type)
    (name : String)
  : CommBuilder σ :=
    ⟨name, Array.empty⟩

  /-- Pushes a flag. -/
  def CommBuilder.push
    (self : CommBuilder σ)
    (flag : Flag σ)
  : CommBuilder σ :=
    { self with
      flags := self.flags.push flag
    }

  /-- Turns the builder into an actual [`Comm`]. -/
  def CommBuilder.build
    (self : CommBuilder σ)
  : Except String <| Comm σ :=
    do
      let flags ←
        Flags.mk self.flags
      pure ⟨self.name, flags⟩
end builder



/-- Constructor for [`CommBuilder`]. -/
def Comm.mkBuilder
  (σ : Type)
  (name : String)
: CommBuilder σ :=
  CommBuilder.empty σ name
