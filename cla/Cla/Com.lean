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


/-- Builds a `μ (MProd min α β)` from `α` and `β` getters. -/
def MProd.build
  {μ : Type → Type}
  [Monad μ]
  (getα : μ α)
  (getβ : μ β)
  (min : Nat)
: μ <| MProd min α β :=
  match min with
  | 0 =>
    getβ
  | min + 1 =>
    do
      let a ← getα
      let tail ← MProd.build getα getβ min
      pure (a, tail)


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

  open Dsl



  protected abbrev MProd
    (bounds : ArgSpec.Bounds)
  : Type :=
    if bounds.max == some bounds.min then
      match bounds.min with
      | 0 => Unit
      | min + 1 => MProd min String String
    else
      MProd bounds.min String <| List String

  example :
    (Bounds.mk 0 (some 0) |>.MProd) = Unit
  := rfl
  example :
    (Bounds.mk 0 none |>.MProd) = (MProd 0 String <| List String)
  := rfl
  example :
    (Bounds.mk 0 (some 1) |>.MProd) = (MProd 0 String <| List String)
  := rfl
  example :
    (Bounds.mk 7 (some 7) |>.MProd) = (MProd 6 String String)
  := rfl
  example :
    (Bounds.mk 7 (some 8) |>.MProd) = (MProd 7 String <| List String)
  := rfl


  /-- Type for a validator that validates at least `min` and at most `max` arguments.

  Number of arguments is unbounded if `max = none`. Accepts no argument at all if `max = 0` or `max =
  some m` with `m < min`.
  -/
  protected abbrev Validator
    (bounds : ArgSpec.Bounds)
    (σ : Type)
    (α : Type)
  : Type :=
    Validator bounds.MProd σ α




  section MProdBuild
    variable
      (bounds : Bounds)
      (getArg : IParseM String)
      (getAll : IParseM <| List String)

    protected def MProd.buildNone
    : IParseM <| MProd 0 String Unit :=
      by
        dsimp [Bounds.MProd]
        simp
        apply pure ()

    protected def MProd.buildExact
      (minMinus1 : Nat)
    : IParseM <| MProd minMinus1 String String :=
      MProd.build getArg getArg minMinus1

    protected def MProd.buildMinOnly
      (min : Nat)
    : IParseM <| MProd min String <| List String :=
      MProd.build getArg getAll min



    protected def MProdRun
      {σ : outParam Type}
    : (bounds.Validator σ Unit) → IParseM (EStateM String σ Unit) :=
      by
        simp [Bounds.MProd, Bounds.Validator, Validator]
        cases bounds.max == some bounds.min with
        | true =>
          simp
          cases bounds.min with
          | zero =>
            exact fun action =>
              pure <| action ()
          | succ min =>
            simp
            exact
              fun action =>
                do
                  let input ←
                    MProd.buildExact getArg min
                  pure <| action input
        | false =>
          simp
          exact
            fun action =>
              do
                let input ←
                  MProd.buildMinOnly getArg getAll bounds.min
                pure <| action input
  end MProdBuild
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
  /-- Creates an empty `Flags`. -/
  def Flags.empty : Flags σ :=
    ⟨Array.empty, Std.mkHashMap 0, Std.mkHashMap 0⟩

  def Flags.debug
    (flags : Flags σ)
  : IO Unit :=
    do
      IO.println "shorts:"
      for (c, _) in flags.short.toList do
        IO.println s! "- `{c}`"
      IO.println "longs:"
      for (l, _) in flags.long.toList do
        IO.println s! "- `{l}`"

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
              short.insert' s!"{c}" idx
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




/-- Used to build [`Com.Builder`] and [`Com`].

Abstract description of a command, there's no reason to use this directly.
-/
structure Command
  (F : Type u)
where
  name : String
  flags : F
deriving Inhabited



/-- Stores a [`Flags`] structure.

To build a `Com` use the [`Com.Builder`], for instance using [`Com.mkBuilder`].
-/
def Com
  (σ : Type)
:=
  Command (Flags σ)

instance instInhabitedCom
  [Inhabited σ]
: Inhabited <| Com σ where
  default := ⟨"default", Flags.empty⟩



section builder
  /-- Stores an array of [`Flag`]s. -/
  abbrev Com.Builder
    (σ : Type)
  :=
    Command (Array <| Flag σ)

  /-- Empty constructor. -/
  def Com.Builder.empty
    (σ : Type)
    (name : String)
  : Com.Builder σ :=
    ⟨name, Array.empty⟩

  /-- Pushes a flag. -/
  def Com.Builder.withFlag
    (self : Com.Builder σ)
    (flag : Flag σ)
  : Com.Builder σ :=
    { self with
      flags := self.flags.push flag
    }

  /-- Adds some flags. -/
  def Com.Builder.withFlags
    (self : Com.Builder σ)
    (flags : List (Flag σ))
  : Com.Builder σ :=
    { self with
      flags := self.flags ++ flags
    }

  /-- Turns the builder into an actual [`Com`]. -/
  def Com.Builder.build
    (self : Com.Builder σ)
  : Except String <| Com σ :=
    do
      let flags ←
        Flags.mk self.flags
      pure ⟨self.name, flags⟩

  /-- Type of flags accepted by a builder. -/
  protected def Com.Builder.Flag
    (_self : Com.Builder σ)
  : Type :=
    Flag σ
end builder



section Com
  /-- Constructor for [`Com.Builder`]. -/
  def Com.mkBuilder
    (σ : Type)
    (name : String)
  : Com.Builder σ :=
    Com.Builder.empty σ name

  variable
    (self : Com σ)

  def Com.shortOf
    (short : String)
    : IParseM (Flag σ)
  :=
    do
      if let some idx := self.flags.short.find? short
      then pure <| self.flags.flags.get idx
      else throw "unexpected short flag"

  def Com.longOf
    (long : String)
    : IParseM (Flag σ)
  :=
    do
      if let some idx := self.flags.long.find? long
      then pure <| self.flags.flags.get idx
      else throw "unexpected long flag"

  -- def Com.runShort (short : String) : IParseM σ :=
  --   do
  --     let flag ←
  --       self.shortOf short
      
    

  -- def Com.run
  --   (self : Com σ)
  --   (parser : Parse)
  -- : ParseM σ :=
  --   do
  --     parser.nextDo
  --       ()

  -- def Com.parse
  --   (args : List String)
end Com
