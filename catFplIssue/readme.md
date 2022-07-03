- [Zulip topic][zulip]

## Issue

I'm quite out of my depth here, I'm messing with dependent pattern matching and there's something I
just don't understand. Here my non-minimal but small example.

```lean
inductive O
| int
| real
| bool
| unit
deriving Inhabited, BEq, Repr

-- only `Arrow.id` and `Arrow.comp` really matter for my problem
inductive Arrow : (_dom _cod : O) → Type
  -- identity
  | id : {α : O} → Arrow α α

  -- `α → α` arrows
  | unit : Arrow O.unit O.unit
  | not : Arrow O.bool O.bool
  | succᵢ : Arrow O.int O.int
  | succᵣ : Arrow O.real O.real

  | comp {α β γ} : Arrow β γ → Arrow α β → Arrow α γ

  -- `unit → bool`
  | tru : Arrow O.unit O.bool
  | fls : Arrow O.unit O.bool
  -- `unit → int`
  | zero : Arrow O.unit O.int
  -- `int → bool`
  | isZero : Arrow O.int O.bool
  -- `int → real`
  | toReal : Arrow O.int O.real
deriving Repr

def Arrow.compose₁ {α β γ : O} :
  Arrow β γ
  → Arrow α β
  → Arrow α γ
-- id.compose₁ g = g
| id, g => g
-- f.compose₁ id = f
| f, id => f
-- else
| comp f₁ f₂, g => comp f₁ (comp f₂ g)
| f, g => comp f g

#print Arrow.compose₁
-- def Arrow.compose₁ : {α β γ : O} → Arrow β γ → Arrow α β → Arrow α γ :=
-- fun {α β γ} x x_1 =>
--   match β, γ, x, x_1 with
--   | β, .(β), Arrow.id, g => g
--   | .(α), γ, f, Arrow.id => f
--   | β, γ, Arrow.comp f₁ f₂, g => Arrow.comp f₁ (Arrow.comp f₂ g)
--   | β, γ, f, g => Arrow.comp f g
#eval Arrow.compose₁ Arrow.unit Arrow.id
-- Arrow.comp (Arrow.unit) (Arrow.id)
```

I really don't get why this `#eval` produces a `comp` and not `Arrow.unit` as per the second branch
of `compose₁`'s `match`. I guess I'm making a stupid, obvious mistake as that's what I usually do as
a noob, but I just can't see it.

[zulip] : https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/case.20in.20dependent.20match.20not.20triggering.20.28.3F.29