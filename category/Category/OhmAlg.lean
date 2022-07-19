import Category.Init

/-!
# Category **Ω-Alg**

`OhmAlg` is the **Ω-Alg** category:
- objects are all Ω-algebras, and
- arrows are Ω-homomorphisms.

An Ω-algebra is a carrier set `|A|` and some operators, each with its own arity `n` taking `n`
elements of `|A|` and producing a `|A|`.

An Ω-homomorphism is a function that's proper *w.r.t.* all operators.
-/



namespace Cat.OhmAlg

  def OhmOpName := String

  structure OhmOp (α : Type u) where
    arity : Nat
    apply (args : List α) : args.length = arity → α
    name : String
  
  def OhmOps (α : Type u) :=
    Set (OhmOp α)

  structure All (opNames : Set String) where
    Elm : Type u
    arity (name : String) : Nat
    ops (name : String) (known : name ∈ opNames) : OhmOp Elm
  


  -- structure OhmHomo (o₁ o₂ : All Ops) where
  --   apply : o₁.Elm → o₂.Elm
  --   apply_post
  --     (args : List o₁.Elm) (op : OhmOpName) (known : name ∈ Opts)
  --     (legal : args.length = o₁.ops op known |>.arity)
  --     : apply (op.apply args legal) = o₂.ops

end Cat.OhmAlg



/-! ## TODO `Cat` instance -/
