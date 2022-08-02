import Cat.Fam.CatDefs



/-! # Useful theorems over categories -/

namespace Cat



/-! ## Dual notions

Proposition `p₂` is *the dual* of proposition `p₁` if the fact that `p₁` holds in `ℂ` is
**equivalent** to `p₂` holding in `ℂ.Dual`. 

For instance, an initial object in a category is terminal in the category's dual. So *initial* and
*terminal* are each other's dual.
-/
section dual_stuff
  variable
    {ℂ : Cat}

  /-- Being a terminal object is the dual of being an initial object. -/
  instance Fam.Cat.Initial.dual
    (α : ℂ.Obj)
    [instα : Initial α]
  : @Terminal ℂ.Dual α where
    arrow :=
      instα.arrow
    unique :=
      instα.unique

  /-- Being an initial object is the dual of being a terminal object. -/
  instance Fam.Cat.Teminal.dual
    (α : ℂ.Obj)
    [instα : Terminal α]
  : @Initial ℂ.Dual α where
    arrow :=
      instα.arrow
    unique :=
      instα.unique

  /-- "Monic morphisms" are the dual of "epic morphisms". -/
  instance Fam.Cat.Epic.dual
    (f : |ℂ.Hom β γ|)
    [inst : ℂ.Epic f]
  : ℂ.Dual.Monic f :=
    ⟨inst.law⟩

  /-- "Epic morphisms" are the dual of "monic morphisms". -/
  instance Fam.Cat.Mono.dual
    (f : |ℂ.Hom β γ|)
    [inst : ℂ.Monic f]
  : ℂ.Dual.Epic f :=
    ⟨inst.law⟩

  /-- The notion of isomorphism is its own dual. -/
  instance Fam.Cat.Iso.dual
    {α β : ℂ.Obj}
    (f : |ℂ.Hom α β|)
    [inst : ℂ.Iso f]
  : ℂ.Dual.Iso (ℂ.isoInv f) where
    inv :=
      f
    law_left :=
      inst.law_left
    law_right :=
      inst.law_right

  /-- The notion of isomorphic objects is its own dual. -/
  instance Fam.Cat.IsoObj.dual
    (α β : ℂ.Obj)
    [inst : α ≅ β]
  : @IsoObj ℂ.Dual α β :=
    ⟨_, Iso.dual inst.iso⟩



  /-- Two initial objects are isomorphic. -/
  instance Fam.Cat.IsoObj.ofInitial
    (α β : ℂ.Obj)
    [instα : Initial α]
    [instβ : Initial β]
  : α ≅ β :=
    -- proof outline: only one arrow from `α` to `β`, only one back; their composition must be `id`
    -- since there's only one arrow from `β` to `β` (same for `α`), which must be the identity.
    let f : |ℂ.Hom α β| :=
      instα.arrow
    let fInv : |ℂ.Hom β α| :=
      instβ.arrow
    let id_left :=
      ℂ.compose f fInv
      |> Fam.Cat.Initial.equivId
    let id_right :=
      ℂ.compose fInv f
      |> Fam.Cat.Initial.equivId
    let iso : Iso f :=
      ⟨fInv, id_left, id_right⟩
    ⟨f, iso⟩

  /-- Two initial objects are isomorphic. -/
  instance Fam.Cat.IsoObj.ofTerminal
    (α β : ℂ.Obj)
    [Terminal α]
    [Terminal β]
  : α ≅ β :=
    -- reuse `IsoObj.ofInitial` in `ℂ.Dual`
    IsoObj.ofInitial (ℂ := ℂ.Dual) α β
    |>.dual

end dual_stuff
