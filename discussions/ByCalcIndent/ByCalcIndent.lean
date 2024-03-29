/-!

Lean versions used, most recent to oldest:

- `nightly`: 20 Nov. 2022
- `#1844`: https://github.com/leanprover/lean4/pull/1844
- `pre #1811`: right before https://github.com/leanprover/lean4/pull/1811

# `calc`

On mathlib 4, plain (no special indent/padding):
- https://github.com/leanprover-community/mathlib4/search?q=calc

On std 4:
- plain: https://github.com/leanprover/std4/blob/main/Std/Data/Int/Lemmas.lean#L1133-L1139
- padded `_`: https://github.com/leanprover/std4/blob/main/Std/Data/List/Init/Lemmas.lean#L129-L131
-/

variable
  (t1 t2 t3 t4 t5 : Nat)

  (pf12 : t1 = t2)
  (pf23 : t2 < t3)
  (pf34 : t3 = t4)
  (pf45 : t4 < t5)

abbrev longId : Nat → Nat := id
abbrev longerId := longId
abbrev evenLongerId := longId

-- plain
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t5 :=
  let p := calc
    t1 = t2 := pf12
    _ < t3 := pf23
    _ = t4 := pf34
    _ < t5 := pf45
  -- dedent terminates the block
  p

-- sensible indentation with padding, rel-ops aligned
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t5 :=
  let p := calc
    t1 = t2 := pf12
    _  < t3 := pf23
    _  = t4 := pf34
    _  < t5 := pf45
  -- dedent terminates the block
  p

-- align on rel-ops with arbitrary `_` indentation
-- nightly ✅ #1844 ❌ pre #1811 ✅
example : t1 < t5 :=
  let _ := calc
    t1 = t2 := pf12
     _ < t3 := pf23
     _ = t4 := pf34
     _ < t5 := pf45
  let p := calc
    longId t1 = t2 := pf12
            _ < t3 := pf23
            _ = t4 := pf34
            _ < t5 := pf45
  -- dedent terminates the block
  p

-- align on rel-ops with arbitrary `_` indentation, drifting
-- nightly ✅ #1844 ❌ pre #1811 ✅
example : t1 < t5 :=
  let p := calc
    longId t1 = t2 :=
            pf12 -- error if less indented
            _ < t3 := id
                        pf23 -- error if less indented
            _ = t4 := pf34
            _ < t5 := pf45
  -- dedent terminates the block
  p

-- same-line `calc <first relation>` with normal indent afterwards
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t5 :=
  calc t1 = t2 := pf12
    _ < t3 := pf23
    _ = t4 := pf34
    _ < t5 := pf45

-- `calc <first relation LHS>\n<indent><relation and relation RHS>`
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t5 :=
  let _ :=
    calc t1
        = t2 := pf12
      _ < t3 := pf23
      _ = t4 := pf34
      _ < t5 := pf45
  -- alternatively
  calc
    t1
      = t2 := pf12
    _ < t3 := pf23
    _ = t4 := pf34
    _ < t5 := pf45

-- `calc <first relation LHS>\n<indent><relation and relation RHS>`
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t5 :=
  calc t1 = t2 := pf12
       _  < t3 := pf23
       _  = t4 := pf34
       _  < t5 := pf45



-- `by` with indented sequence of tactics in `calc`-item RHS
-- nightly ❌ #1844 ✅ pre #1811 ✅
example : t1 < t4 :=
  calc
    t1 = t2 := pf12
    _  < t3 := by
      skip
      skip
      exact pf23
    _  = t4 := pf34

-- function application with indented argument in `calc`-item RHS
-- nightly ❌ #1844 ✅ pre #1811 ❌
example : t1 < t4 :=
  calc
    t1 = t2 := pf12
    _  < t3 := id
      pf23
    _  = t4 := id
                pf34

-- vicious `v1`, single line
-- https://github.com/leanprover-community/mathlib/blob/568eb9b432c885f2a2cb8fe3bbfa77467e774da7/archive/100-theorems-list/37_solution_of_cubic.lean#L166-L172
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t4 :=
  calc  longId t1
      = longerId t2
        := pf12
    _ < t3
        := id pf23
    _ = t4
        := id pf34

-- vicious `v2`
-- https://github.com/leanprover-community/mathlib/blob/568eb9b432c885f2a2cb8fe3bbfa77467e774da7/archive/100-theorems-list/37_solution_of_cubic.lean#L166-L172
-- nightly ❌ #1844 ✅ pre #1811 ❌
example : t1 < t4 :=
  calc  longId t1
      = longerId t2
        := pf12
    _ < t3
        := id
      pf23
    _ = t4
        := id
            pf34

-- vicious `v3`, single line
-- https://github.com/leanprover-community/mathlib/blob/568eb9b432c885f2a2cb8fe3bbfa77467e774da7/archive/100-theorems-list/37_solution_of_cubic.lean#L176-L181
-- nightly ✅ #1844 ✅ pre #1811 ✅
example : t1 < t4 :=
  calc  longId t1
      = longerId t2 := pf12
    _ < t3
      := id pf23
    _ = t4
      := id pf34

-- vicious `v4`
-- https://github.com/leanprover-community/mathlib/blob/568eb9b432c885f2a2cb8fe3bbfa77467e774da7/archive/100-theorems-list/37_solution_of_cubic.lean#L176-L181
-- nightly ❌ #1844 ✅ pre #1811 ❌
example : t1 < t4 :=
  calc  longId t1
      = longerId t2 := pf12
    _ < t3
      := id
        pf23
    _ = t4
      := id
          pf34

-- playing with `by`
-- nightly ❌ #1844 ✅ pre #1811 ✅
example : t1 < t4 :=
  calc  longId t1
      = longerId t2
        := pf12
    _ < t3 := by
      apply id pf23
    _ = t4 :=
      by
        apply id pf34

-- `@digama0`'s crazy idea
-- nightly ❌ #1844 ❌ pre #1811 ❌
example : t1 < t4 :=
  calc t1
    _ = t2 := pf12
    _ < t3 := pf23
    _ = t4 := pf34
