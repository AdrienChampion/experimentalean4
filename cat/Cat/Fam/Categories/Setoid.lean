import Cat.Fam.CatLemmas



/-! # Category of setoids -/

namespace Cat



/-- Category of setoids. -/
def Fam.Cat.SET : Cat :=
  Morph.compose.Comp.toCat
    Morph.compose.assoc
    Morph.id
    Morph.id_compose
    Morph.compose_id
