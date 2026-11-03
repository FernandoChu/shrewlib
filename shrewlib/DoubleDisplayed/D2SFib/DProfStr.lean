import Displayed.Opfibration.SplitOpfibStr
import DoubleDisplayed.Fibration

/-!
# Dependent profunctors over split opfibrations

The category `DProfStr` of dependent profunctors, doubly displayed over `SplitOpfibStr`: it is the
Grothendieck construction of the contravariant functor sending a split opfibration `B` over `A` to
the category of functors `Bᵒᵖ.Total ⥤ Cat`, out of the total category of its dual opfibration.

A dependent profunctor over `B` is a functor `P : Bᵒᵖ.Total ⥤ Cat`. The objects of `Bᵒᵖ.Total` are
the pairs `⟨a, x⟩` with `x : B.Ob a`, and its morphisms `⟨a, x⟩ ⟶ ⟨a', x'⟩` the pairs of
`α : a ⟶ a'` and a vertical morphism `β : x' ⟶ push α x`. For `B` the unstraightening of a constant
functor at a category `B₀`, it is a profunctor from `A` to `B₀`, a functor `A × B₀ᵒᵖ ⥤ Cat`. A
morphism of dependent profunctors over an opcartesian functor `H` from `P` to `P'` is a natural
transformation `P ⟶ H.dualOp.total ⋙ P'`, where `H.dualOp.total : Bᵒᵖ.Total ⥤ B'ᵒᵖ.Total` is the
functor that `H` induces. Composition whiskers the second transformation along the first.

Over the identities of `SplitOpfibStr`, `H.dualOp.total` is the identity functor by a rule, so the
fiber of `DProfStr` over `B` has the natural transformations `P ⟶ P'` as morphisms.

`DProfStr` is a split fibration over `SplitOpfibStr` by precomposition: the pullback of `P'` along
`H` is `H.dualOp.total ⋙ P'`, with the identity as chosen lift (`DProfStr.splitDDFib`).
-/

universe u

namespace DoubleDisplayed

open CategoryTheory Displayed

open scoped Displayed

/-- **The category of dependent profunctors**, doubly displayed over `SplitOpfibStr`: over `B`,
the functors `Bᵒᵖ.Total ⥤ Cat`, and over an opcartesian functor `H`, the natural transformations
`P ⟶ H.dualOp.total ⋙ P'`. -/
def DProfStr : DoubleDisplayed.{u, u + 1, u, u + 1, u, u + 1} SplitOpfibStr.{u} where
  Ob {_} (B : SplitOpfibOb _) := B.toDisplayedᵒᵖ.Total ⥤ Cat.{u, u}
  Hom {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B')) P P' :=
    P ⟶ H.dualOp.total ⋙ P'
  id P := 𝟙 P
  comp {_ _ _ u _ B B' _ H _ _ _ _} κ κ' :=
    κ ≫ Functor.whiskerLeft (OpcartesianFunctor.dualOp (u := u.toFunctor)
      (D := SplitOpfibOb.toDisplayed B) (E := SplitOpfibOb.toDisplayed B') H).total κ'
  id_comp _ := rfl
  comp_id _ := NatTrans.ext (funext fun _ => rfl)
  assoc _ _ _ := NatTrans.ext (funext fun _ => rfl)

/-- The chosen pullback of a dependent profunctor along an opcartesian functor `H` is the
precomposition with `H.dualOp.total`, with the identity as chosen lift. -/
instance DProfStr.ddFib : DDFib DProfStr.{u} where
  pull {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B'))
      (P' : (SplitOpfibOb.toDisplayed B')ᵒᵖ.Total ⥤ Cat.{u, u}) :=
    H.dualOp.total ⋙ P'
  clift {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B'))
      (P' : (SplitOpfibOb.toDisplayed B')ᵒᵖ.Total ⥤ Cat.{u, u}) :=
    𝟙 (H.dualOp.total ⋙ P')
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => χ
      lift_fac := fun {_ _ _} _ {_} _ => NatTrans.ext (funext fun _ => rfl)
      lift_uniq := fun {_ _ _ _ _ _} _ h => (NatTrans.ext (funext fun _ => rfl)).trans h }

instance DProfStr.preSplitDDFib : PreSplitDDFib DProfStr.{u} where
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **`DProfStr` is a split fibration over `SplitOpfibStr`**, by precomposition. -/
instance DProfStr.splitDDFib : SplitDDFib DProfStr.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := NatTrans.ext (funext fun _ => rfl)

end DoubleDisplayed
