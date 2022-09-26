/-! # Basic helpers -/



/-- `𝕂`onstant combinator. -/
def 𝕂
  {α : Type u}
  {β : Type v}
  (val : α)
: β → α :=
  fun _ => val



/-- A result or a string. -/
abbrev Res
  (α : Type u)
:=
  Except String α



namespace Res
  def bail
    {α : Type u |> outParam}
    (msg : optParam String "a fatal error occurred")
  : Res α :=
    Except.error msg

  variable
    {α : Type u}
    (self : Res α)

  def map
    (f : α → β)
  : Res β :=
    match self with
    | .ok a => f a |> .ok
    | .error msg => .error msg

  def mapError
    (f : String → String)
  : Res α :=
    match self with
    | .ok _ => self
    | .error e => .error (f e)

  def context
    (getMsg : Unit → String)
  : Res α :=
    self.mapError
      fun e => e ++ "\n- " ++ getMsg ()
end Res
