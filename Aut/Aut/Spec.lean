import Aut.Init



structure Spec.State where
  S : Type u
  Ty : S → Type v
  Err : Type v
  describe : (s : S) → Ty s → String

instance instCoeStateSpec
: CoeSort Spec.State.{u, v} (Type u)
where
  coe self :=
    self.S

instance instCoeFunStateSpec
: CoeFun Spec.State.{u, v} (fun state => state.S → Type v)
:=
  ⟨Spec.State.Ty⟩

namespace Spec.State
  universe
    u v
  variable
    (self : Spec.State.{u, v})
    {self' : Spec.State.{u, v}}

  def Res
    (S : self')
  : Type v :=
    self' S
    |> Except self'.Err
end Spec.State



structure Spec.Arrow.{u, v} (S : Spec.State.{u, v}) (Dom : S) where
  Cod : S
  Args : Type v
  apply : S Dom → Args → S.Res Cod
  describe : S Dom → Args → String

namespace Spec.Arrow
  variable
    {S : Spec.State}
    {Dom : S}
    (self : Arrow S Dom)
  
  def DomTy :=
    S Dom

  def CodTy :=
    S self.Cod
end Spec.Arrow



structure Fsm.{u, v} where
  State : Spec.State.{u, v}
  Arrow : (s : State) → Spec.Arrow.{u, v} State s
  NewArgs : Type u
  protected new : NewArgs → (s : State) × State s
  protected checkDone : (s : State) → State s → Bool



structure Run.{u, v} (fsm : Fsm.{u, v}) where
  curr : fsm.State
  state : fsm.State curr

namespace Run
  universe
    u v
  variable
    {fsm : Fsm.{u, v}}
    (self : Run fsm)

  abbrev init
    (fsm : Fsm)
    (args : fsm.NewArgs)
  : Run fsm :=
    let ⟨curr, state⟩ :=
      fsm.new args
    ⟨curr, state⟩

  def describe : String :=
    fsm.State.describe self.curr self.state

  abbrev trans
    (args : fsm.Arrow self.curr |>.Args)
  : Except fsm.State.Err (Run fsm) :=
    fsm.Arrow self.curr
    |>.apply self.state args
    |>.map fun state => ⟨
      fsm.Arrow self.curr |>.Cod,
      state
    ⟩

  abbrev isDone : Bool :=
    fsm.checkDone self.curr self.state
end Run



abbrev Fsm.init
  (self : Fsm)
  (args : self.NewArgs)
: Run self :=
  Run.init self args
