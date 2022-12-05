import Aut.Spec

namespace Acc



structure Acc₁ where
  email : String

structure Acc₂
extends
  Acc₁
where
  pass : String

structure Acc₃
extends
  Acc₂
where
  name : String

structure Acc
extends
  Acc₃
where
  uid : Nat



def Acc₁.pass
  (self : Acc₁)
  (pass : String)
: Except String Acc₂ :=
  if pass.isEmpty
  then Except.error s!"illegal empty pass for `{self.email}`"
  else pure ⟨self, pass⟩
def Acc₁.describe (self : Acc₁) : String :=
  s!"Acc₁:\n  email : {self.email}"

def Acc₂.name
  (self : Acc₂)
  (name : String)
: Except String Acc₃ :=
  if name.isEmpty
  then Except.error s!"illegal empty name for `{self.email}`"
  else pure ⟨self, name⟩
def Acc₂.describe (self : Acc₂) : String :=
  s!"Acc₂:\n  email : {self.email}\n  pass : {self.pass}"

def Acc₃.uid
  (self : Acc₃)
  (uid : Nat)
: Acc :=
  ⟨self, uid⟩
def Acc₃.describe (self : Acc₃) : String :=
  s!"Acc₃:\n  email : {self.email}\n  pass : {self.pass}\n  name : {self.name}"

def Acc.describe (self : Acc) : String :=
  s!"Acc[{self.uid}]:\n  email : {self.email}\n  pass : {self.pass}\n  name : {self.name}"



inductive Acc.S
| Acc₁
| Acc₂
| Acc₃
| Acc

abbrev Acc.Ty : Acc.S → Type
| .Acc₁ => Acc₁
| .Acc₂ => Acc₂
| .Acc₃ => Acc₃
| .Acc => Acc

abbrev Acc.S.describe
: (s : S) → Acc.Ty s → String
| Acc₁ => Acc₁.describe
| Acc₂ => Acc₂.describe
| Acc₃ => Acc₃.describe
| Acc => Acc.describe


abbrev Acc.State : Spec.State where
  S := Acc.S
  Ty := Acc.Ty
  Err := String
  describe := Acc.S.describe


abbrev Acc₁.Arrow : Spec.Arrow Acc.State Acc.S.Acc₁ where
  Cod := Acc.S.Acc₂
  Args := String
  apply := Acc₁.pass
  describe self pass :=
    s!"(Acc₁ {self.email}).pass \"{pass}\""

abbrev Acc₂.Arrow : Spec.Arrow Acc.State Acc.S.Acc₂ where
  Cod := Acc.S.Acc₃
  Args := String
  apply := Acc₂.name
  describe self name :=
    s!"(Acc₂ {self.email}).name \"{name}\""

abbrev Acc₃.Arrow : Spec.Arrow Acc.State Acc.S.Acc₃ where
  Cod := Acc.S.Acc
  Args := Nat
  apply self uid := Except.ok (self.uid uid)
  describe self uid :=
    s!"(Acc₂ {self.email}).uid \"{uid}\""

abbrev Acc.Arrow : Spec.Arrow Acc.State Acc.S.Acc where
  Cod := Acc.S.Acc
  Args := Unit
  apply self _ := Except.ok self
  describe _ _ :=
    s!"stuttering on final state"

abbrev Acc.Arrows : (s : Acc.S) -> Spec.Arrow Acc.State s
| .Acc₁ => Acc₁.Arrow
| .Acc₂ => Acc₂.Arrow
| .Acc₃ => Acc₃.Arrow
| .Acc => Acc.Arrow

protected abbrev Acc.Fsm : Fsm where
  State := Acc.State
  Arrow := Acc.Arrows
  NewArgs := String
  new email :=
    ⟨Acc.S.Acc₁, ⟨email⟩⟩
  checkDone
    | Acc.S.Acc => 𝕂 True
    | _ => 𝕂 False

#check Acc.Fsm.Arrow Acc.S.Acc₂ |>.Args

partial def demo₁ : IO Unit :=
  Acc.Fsm.init "cat@neko.nya"
  |> script
where
  script (fsm : Run Acc.Fsm) := do
    IO.println "currently in"
    IO.println fsm.describe

    if fsm.isDone then
      IO.println "done: reached final state"
    else

      let fsm? :=
        match h : fsm.curr with
        | .Acc₁ =>
          fsm.trans (by
            rw [h]
            simp
            apply "my pass is NYA ♥"
          )
        | .Acc₂ =>
          fsm.trans (by
            rw [h]
            simp
            apply "my name is also NYA ♥"
          )
        | .Acc₃ =>
          fsm.trans (by
            rw [h]
            simp
            apply 69
          )
        | .Acc =>
          Except.ok fsm

      match fsm? with
      | .ok fsm =>
        script fsm
      | .error e =>
        IO.println s!"error: {e}"

#eval demo₁

structure Acc.Run
extends
  Run Acc.Fsm

namespace Acc.Run
  variable
    (self : Run)

  def init (email : String) : Acc.Run :=
    ⟨Acc.Fsm.init email⟩

  def pass
    (pass : String)
    (h : self.curr = .Acc₁ := by assumption)
  : Except String Acc.Run := do
    let run ←
      self.trans (by
        dsimp [Arrows]
        rw [h]
        apply pass
      )
    pure ⟨run⟩
  def name
    (name : String)
    (h : self.curr = .Acc₂ := by assumption)
  : Except String Acc.Run := do
    let run ←
      self.trans (by
        dsimp [Arrows]
        rw [h]
        apply name
      )
    pure ⟨run⟩
  def uid
    (uid : Nat)
    (h : self.curr = .Acc₃ := by assumption)
  : Except String Acc.Run := do
    let run ←
      self.trans (by
        dsimp [Arrows]
        rw [h]
        apply uid
      )
    pure ⟨run⟩
end Acc.Run

partial def demo₂ : IO Unit :=
  Acc.Run.init "cat@neko.nya"
  |> script
where
  script (fsm : Acc.Run) := do
    IO.println "currently in"
    IO.println fsm.describe

    if fsm.isDone then
      IO.println "done: reached final state"
    else

      let fsm? :=
        match h : fsm.curr with
        | .Acc₁ =>
          fsm.pass "my pass is NYA ♥"
        | .Acc₂ =>
          fsm.name "my name is also NYA ♥"
        | .Acc₃ =>
          fsm.uid 69
        | .Acc =>
          Except.ok fsm

      match fsm? with
      | .ok fsm =>
        script fsm
      | .error e =>
        IO.println s!"error: {e}"

#eval demo₂
