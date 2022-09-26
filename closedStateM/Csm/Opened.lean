import Csm.Init

/-! # Opened state monad -/



/-- Same as [`StateT`] but without a `set` operation. -/
abbrev OsmT
  (σ : Type u)
  (μ : Type u → Type v)
  (α : Type u)
: Type (max u v) :=
  σ → μ (α × σ)

/-- [`OsmT`] with the [`Res`] monad. -/
abbrev EOsm
  (σ : Type u)
  (α : Type u)
: Type u :=
  OsmT σ Res α

/-- [`OsmT`] with the [`Id`] monad. -/
abbrev Osm
  (σ : Type u)
  (α : Type u)
: Type u :=
  OsmT σ Id α



namespace OsmT
  variable
    {σ : Type u}
    {μ : Type u → Type v}
    [Monad μ]



  section helpers
    variable
      (self : OsmT σ μ α)
      (state : σ)

    def stateDo
      [Inhabited α]
      (f : σ → σ)
    : OsmT σ μ α :=
      fun s =>
        pure (default, f s)

    def run : μ (α × σ) :=
      self state
    def run' : μ α :=
      do
        pure (←self.run state).fst
    def runit : μ σ :=
      do
        pure (←self.run state).snd
  end helpers



  /-! ## Monad operations -/
  section monad_stuff
    protected def pure
      (a : α)
    : OsmT σ μ α :=
      fun state => pure (a, state)

    protected def map
      (f : α → β)
      (getA : OsmT σ μ α)
    : OsmT σ μ β :=
      fun state => do
        let (a, state) ← getA state
        pure (f a, state)

    protected def seq
      (getF : OsmT σ μ <| α → β)
      (getAofUnit : Unit → OsmT σ μ α)
    : OsmT σ μ β :=
      fun state => do
        let (f, state) ← getF state
        let (a, state) ← getAofUnit () state
        pure (f a, state)

    protected def bind
      (getA : OsmT σ μ α)
      (getBofA : α → OsmT σ μ β)
    : OsmT σ μ β :=
      fun state => do
        let (a, state) ← getA state
        getBofA a state
  end monad_stuff
end OsmT



instance instMonadOpenedOsmT
  {σ : Type u}
  {μ : Type u → Type v}
  [Monad μ]
: Monad <| OsmT σ μ where
  pure :=
    OsmT.pure
  map :=
    OsmT.map
  seq :=
    OsmT.seq
  bind :=
    OsmT.bind



/-- Adds some context to an error. -/
def OsmT.context
  {σ : Type u}
  {α : Type u}
  (self : OsmT σ Res α)
  (getMsg : Unit → String)
: OsmT σ Res α :=
  fun state =>
    self.run state
    |>.context getMsg
