import Csm.Init
import Csm.Opened

/-! # Closed state monad -/



/-- Opaque, stores a [`OsmT`]. -/
structure CsmT
  (σ : Type u)
  (μ : Type u → Type v)
  (α : Type u)
where
  private app : OsmT σ μ α

/-- [`CsmT`] with the [`Res`] monad. -/
abbrev ECsm
  (σ : Type u)
  (α : Type u)
: Type u :=
  CsmT σ Res α

/-- [`CsmT`] with the [`Id`] monad. -/
abbrev Csm
  (σ : Type u)
  (α : Type u)
: Type u :=
  CsmT σ Id α



namespace CsmT
  variable
    {σ : Type u}
    {μ : Type u → Type v}
    [Monad μ]
    {α : Type u}



  section helpers
    variable
      (self : CsmT σ μ α)

    def stateDo
      [Inhabited α]
      (f : σ → σ)
    : CsmT σ μ α where
      app s :=
        pure (default, f s)

    def stateYield
      (f : σ → μ (α × σ))
    : CsmT σ μ α where
      app s :=
        do
          let res ← f s
          pure res

    def run : σ → μ (α × σ) :=
      self.app.run
    def run' : σ → μ α :=
      self.app.run'
    def runit : σ → μ σ :=
      self.app.runit
  end helpers


  section monad_stuff
    protected def pure
      (a : α)
    : CsmT σ μ α where
      app := pure a

    protected def bind
      (getA : CsmT σ μ α)
      (getBofA : α → CsmT σ μ β)
    : CsmT σ μ β where
      app :=
        getA.app
        >>= (getBofA · |>.app)
  end monad_stuff
end CsmT



instance instMonadCsmT
  {σ : Type u}
  {μ : Type u → Type v}
  [Monad μ]
: Monad <| CsmT σ μ where
  pure :=
    CsmT.pure
  bind :=
    CsmT.bind



/-- Adds some context to an error. -/
def CsmT.context
  {σ : Type u}
  {α : Type u}
  (self : CsmT σ Res α)
  (getMsg : Unit → String)
: CsmT σ Res α where
  app :=
    OsmT.context self.app getMsg