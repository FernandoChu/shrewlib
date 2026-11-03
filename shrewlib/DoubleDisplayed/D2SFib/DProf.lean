import Displayed.Opfibration.Straightening.ICatStr
import DoubleDisplayed.Fibration

/-!
# Dependent profunctors

The category `DProf` of dependent profunctors, doubly displayed over `ICatStr`: it is the
Grothendieck construction of the contravariant functor sending `F : A ⥤ Cat` to the category of
functors `(∫ F)ᵒᵖ.Total ⥤ Cat`, over the Grothendieck construction `ICatStr` of `A ↦ (A ⥤ Cat)`.

A dependent profunctor over `F : A ⥤ Cat` is a functor `P : (∫ F)ᵒᵖ.Total ⥤ Cat` out of the total
category of the dual of the unstraightening of `F`, the Grothendieck construction of
`a ↦ (F a)ᵒᵖ`: its objects are the pairs `⟨a, x⟩` with `x : F a`, and its morphisms
`⟨a, x⟩ ⟶ ⟨a', x'⟩` the pairs of `α : a ⟶ a'` and `β : x' ⟶ F α x`. For `F` constant at `B`, it
is a profunctor from `A` to `B`, a functor `A × Bᵒᵖ ⥤ Cat`. A morphism of dependent profunctors over
a strict transformation `τ` over `u` from `P` to `P'` is a natural transformation
`P ⟶ τ.dualTotal ⋙ P'`, where `τ.dualTotal : (∫ F)ᵒᵖ.Total ⥤ (∫ G)ᵒᵖ.Total` is the functor that
`τ` induces. Composition whiskers the second transformation along the first `dualTotal`.

Over the identities of `ICatStr`, `dualTotal` is the identity functor by a rule, so the fiber of
`DProf` over `F` has the natural transformations `P ⟶ P'` as morphisms.

`DProf` is a split fibration over `ICatStr` by precomposition: the pullback of `P'` along `τ` is
`τ.dualTotal ⋙ P'`, with the identity as chosen lift (`DProf.splitDDFib`).
-/

universe u v₃ u₃

namespace DoubleDisplayed

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

-- The universes of the fibers only occur in the levels of `DProf` through the `max` of the levels
-- of its objects and morphisms.
set_option linter.checkUnivs false in
/-- **The category of dependent profunctors**, doubly displayed over `ICatStr`: over `F : A ⥤ Cat`,
the functors `(∫ F)ᵒᵖ.Total ⥤ Cat`, and over a strict transformation `τ`, the natural
transformations `P ⟶ τ.dualTotal ⋙ P'`. -/
def DProf : DoubleDisplayed ICatStr.{u} where
  Ob {A} (F : A ⥤ Cat.{u, u}) := (∫ F)ᵒᵖ.Total ⥤ Cat.{v₃, u₃}
  Hom {_ _ u F G} (τ : StrictTrans F (u.toFunctor ⋙ G)) P P' :=
    P ⟶ StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P'
  id P := 𝟙 P
  comp {_ _ _ u _ F G _ τ _ _ _ _} κ κ' :=
    κ ≫ Functor.whiskerLeft (StrictTrans.dualTotal (u := u.toFunctor) (F := F) (G := G) τ) κ'
  id_comp _ := rfl
  comp_id _ := NatTrans.ext (funext fun _ => rfl)
  assoc _ _ _ := NatTrans.ext (funext fun _ => rfl)

/-- The chosen pullback of a dependent profunctor along a strict transformation is the
precomposition with its `dualTotal`, with the identity as chosen lift. -/
instance DProf.ddFib : DDFib DProf.{u, v₃, u₃} where
  pull {_ _ u _ G} τ (P' : (∫ (G : _ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{v₃, u₃}) :=
    StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P'
  clift {_ _ u _ G} τ (P' : (∫ (G : _ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{v₃, u₃}) :=
    𝟙 (StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P')
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => χ
      lift_fac := fun {_ _ _} _ {_} _ => NatTrans.ext (funext fun _ => rfl)
      lift_uniq := fun {_ _ _ _ _ _} _ h => (NatTrans.ext (funext fun _ => rfl)).trans h }

instance DProf.preSplitDDFib : PreSplitDDFib DProf.{u, v₃, u₃} where
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **`DProf` is a split fibration over `ICatStr`**, by precomposition. -/
instance DProf.splitDDFib : SplitDDFib DProf.{u, v₃, u₃} where
  clift_id _ := rfl
  clift_comp _ _ _ := NatTrans.ext (funext fun _ => rfl)

end DoubleDisplayed
