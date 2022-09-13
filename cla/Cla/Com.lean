import Cla.Parse



/-! # `Com`mand types and helpers -/

namespace Cla



/-! ## Building blocks -/



/-- Validates some `In`put.

- `σ` is the type of the state that the validator affects;
- `α` is the output type, which is currently not used (set to [`Unit`]).
-/
abbrev Validator
  (In : Type)
  (σ : Type)
  (α : Type)
:=
  In → EStateM String σ α



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



/-! ## Bounds, specify how many values a flag takes -/



/-- An interval with a possibly infinite upper-bound.

Upper-bound is infinite iff `max = none`.
-/
structure ArgSpec.Bounds where
  min : Nat
  max : Option Nat
deriving Repr, BEq



instance instToStringArgSpecBounds
: ToString ArgSpec.Bounds where
  toString self :=
    let max :=
      self.max.map
        (s! "{·}]")
      |>.getD
        "∞["
    s! "[{self.min}, {max}"

namespace ArgSpec.Bounds
  /-- The interval `[min, max]` with `min ≤ max`. -/
  def between
    (min max : Nat)
    (_legal : min ≤ max := by simp)
  : Bounds where
    min := min
    max := some max

  example : s! "{between 1 7}" = "[1, 7]" := rfl
  example : s! "{between 3 3}" = "[3, 3]" := rfl

  /-- `[min, ∞[` -/
  def atLeast
    (min : Nat)
  : Bounds where
    min := min
    max := none

  example : s! "{atLeast 0}" = "[0, ∞[" := rfl
  example : s! "{atLeast 7}" = "[7, ∞[" := rfl

  /-- `[0, max]` -/
  def atMost
    (max : Nat)
  : Bounds where
    min := 0
    max := some max

  example : s! "{atMost 0}" = "[0, 0]" := rfl
  example : s! "{atMost 7}" = "[0, 7]" := rfl

  /-- `[n, n]` -/
  def exact
    (n : Nat)
  :=
    between n n

  example : s! "{exact 0}" = "[0, 0]" := rfl
  example : s! "{exact 7}" = "[7, 7]" := rfl

  /-- `[0, 0]` -/
  def default :=
    exact 0

  /-- `[0, 0]` -/
  def zero :=
    exact 0



  /-! Simple DSL using `⟦` (`\[[`), `⟧` (`\[[`) and `∞` (`\infty`). -/
  namespace Dsl
    local syntax "⟦" term ", " term "⟧" : term
    local syntax "⟦" term ", " "∞" "⟧" : term
    macro_rules
    | `(⟦ $min, $max ⟧) =>
      `(ArgSpec.Bounds.between $min $max)
    | `(⟦ $min, ∞ ⟧) =>
      `(ArgSpec.Bounds.atLeast $min)
  end Dsl



  /-- Type for a validator that validates at least `min` and at most `max` arguments.

  Number of arguments is unbounded if `max = none`. Accepts no argument at all if `max = 0` or `max =
  some m` with `m < min`.
  -/
  protected abbrev Validator
    (bounds : ArgSpec.Bounds)
    (σ : Type)
    (α : Type)
  : Type :=
    let ⟨min, max⟩ := bounds
    -- `min` strings followed by a list of strings, used for `[min, max]` intervals where `min < max`
    -- or `max` is `∞`, *i.e.* `none`
    let finiteArgs : Nat → Type
      | 0 =>  Unit
      | 1 => String
      | min + 1 => MProd min String String
    let minThenList :=
      Validator (MProd min String <| List String) σ α

    match max with
    | some max =>
      if max = 0 || max < min then
        Validator Unit σ α
      else if max = min then
        Validator (finiteArgs min) σ α
      else
        minThenList
    | none =>
      minThenList
end ArgSpec.Bounds



structure ArgSpec
  (σ : Type)
extends
  ArgSpec.Bounds
where
  validator :
    toBounds.Validator σ Unit

section ArgSpec
  variable
    {σ : Type}
    (self : @&ArgSpec σ)

  def ArgSpec.bounds :=
    self.toBounds

  /-- A user-friendly description of the number of arguments expected.

  Designed to follow, typically, `"expected ..."`.
  -/
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

  /-- Produces an error using [`ArgSpec.descCountExpected`]. -/
  def ArgSpec.countBail! : IParseM α :=
    do
      bail! self.descCountExpected
end ArgSpec



/-! ## Building [`Flag`]s with session types -/



/-- A description. -/
structure Flag0 (σ : Type) where
  desc : String
deriving Repr, BEq

/-- Adds short and/or long names to [`Flag0`]. -/
structure Flag1 (σ : Type)
extends Flag0 σ
where
  short : Option Char
  long : Option String
deriving Repr, BEq

/-- Adds cardinality bounds to [`Flag1`]. -/
structure Flag2 (σ : Type)
extends Flag1 σ
where
  bounds : ArgSpec.Bounds
deriving Repr, BEq

/-- Adds arguments specification to [`Flag1`], but **built** from [`Flag2`]. -/
structure Flag
  (σ : Type)
extends Flag1 σ
where
  args: ArgSpec σ



namespace Flag0
  variable (self : Flag0 σ)

  /-- Sets the flag's short name. -/
  def withShort (short : Option Char) : Flag1 σ := {
      self with
        short
        long := none
  }

  /-- Sets the flag's long name. -/
  def withLong (long : Option String) : Flag1 σ := {
    self with
      short := none
      long
  }
end Flag0

namespace Flag1
  variable (self : Flag1 σ)

  /-- Sets the flag's short name. -/
  def withShort (short : Option Char) : Flag1 σ := {
    self with short
  }

  /-- Sets the flag's long name. -/
  def withLong (long : Option String) : Flag1 σ := {
    self with long
  }

  /-- Specifies the number of arguments expected as an interval. -/
  def argsIn (bounds : ArgSpec.Bounds) : Flag2 σ := {
    self with bounds
  }

  /-- Specifies an arbitrary number of arguments greater than `min`. -/
  def argsAtLeast (min : Nat) : Flag2 σ := {
    self with
      bounds := ArgSpec.Bounds.atLeast min
  }

  /-- Specifies an arbitrary number of arguments less than `max`. -/
  def argsAtMost (max : Nat) : Flag2 σ := {
    self with
      bounds := ArgSpec.Bounds.atMost max
  }

  /-- Specifies a precise number of arguments. -/
  def argsTake (n : Nat) : Flag2 σ := {
    self with
      bounds := ArgSpec.Bounds.exact n
  }

  def effect
    (validator : ArgSpec.Bounds.zero.Validator σ Unit)
  : Flag σ := {
    self with
      args := ⟨ArgSpec.Bounds.zero, validator⟩
  }
end Flag1

namespace Flag2
  variable (self : Flag2 σ)

  def effect
    (validator : self.bounds.Validator σ Unit)
  : Flag σ := {
    self.toFlag1 with
      args := ⟨self.bounds, validator⟩
  }
end Flag2

namespace Flag
  def withDesc (desc : String) : Flag0 σ :=
    ⟨desc⟩

  -- def adapt
  --   (self : Flag σ)
  --   (adaptor : EStateM String σ Unit → EStateM String σ' Unit)
  -- : Flag σ' :=
  --   let validator : self.args.bounds.Validator σ' Unit :=
  --     by
  --       let validator :=
  --         self.args.validator
  --       simp [ArgSpec.Bounds.Validator]
  --       simp [ArgSpec.Bounds.Validator] at validator
  --       cases h_max : self.args.1.max
  --       · simp [h_max] at validator
  --         simp
  --         intro input
  --         apply adaptor
  --         apply validator input
  --       · simp [h_max] at validator
  --         simp
  --         sorry
  --   let args : ArgSpec σ' :=
  --     ⟨self.args.bounds, fun i =>
  --       adaptor ∘ self.args.validator
  --     ⟩
  --   { self.toFlag1 with args := ⟨self.args.bounds, fun i => self.validator i |> adaptor⟩ }
end Flag



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




/-- Used to build [`Comm.Builder`] and [`Comm`].

Abstract description of a command, there's no reason to use this directly.
-/
structure Command
  (F : Type u)
where
  name : String
  flags : F



/-- Stores a [`Flags`] structure.

To build a `Comm` use the [`Comm.Builder`], for instance using [`Comm.mkBuilder`].
-/
def Comm
  (σ : Type)
:=
  Command (Flags σ)



section builder
  /-- Stores an array of [`Flag`]s. -/
  abbrev Comm.Builder
    (σ : Type)
  :=
    Command (Array <| Flag σ)

  /-- Empty constructor. -/
  def Comm.Builder.empty
    (σ : Type)
    (name : String)
  : Comm.Builder σ :=
    ⟨name, Array.empty⟩

  /-- Pushes a flag. -/
  def Comm.Builder.withFlag
    (self : Comm.Builder σ)
    (flag : Flag σ)
  : Comm.Builder σ :=
    { self with
      flags := self.flags.push flag
    }

  /-- Adds some flags. -/
  def Comm.Builder.withFlags
    (self : Comm.Builder σ)
    (flags : List (Flag σ))
  : Comm.Builder σ :=
    { self with
      flags := self.flags ++ flags
    }

  /-- Turns the builder into an actual [`Comm`]. -/
  def Comm.Builder.build
    (self : Comm.Builder σ)
  : Except String <| Comm σ :=
    do
      let flags ←
        Flags.mk self.flags
      pure ⟨self.name, flags⟩

  /-- Type of flags accepted by a builder. -/
  protected def Comm.Builder.Flag
    (_self : Comm.Builder σ)
  : Type :=
    Flag σ
end builder



/-- Constructor for [`Comm.Builder`]. -/
def Comm.mkBuilder
  (σ : Type)
  (name : String)
: Comm.Builder σ :=
  Comm.Builder.empty σ name
