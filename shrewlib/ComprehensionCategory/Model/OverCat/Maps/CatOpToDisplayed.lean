import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Unit
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Unit
import Displayed.Straightening.Equivalence

/-!
# From the contravariant category model to the displayed category model

A type `C : Γᵒᵖ ⥤ Cat` of the contravariant category model is a type of the displayed category
model (`catOpToDisp C`), the straightening of its unstraightening `∫⁻ C`, seen as a displayed
category over `Γ`. This is the action on objects of the vertical functor `catOpToDispFunctor`, the
composite of the unstraightening `ICatOpLax ⟶ SplitFibLax`, forgetting the cleavage, and the
straightening `DisplayedCat ⟶ LaxNormalCat`.

As for the category model (`OverCat/Maps/CatToDisplayed`), it is a strict map of comprehension
categories over the identity of `Cat` (`catOpToDispComprehensionMap`), whose axioms hold by `rfl`,
which gives the rules Lift-Intro, Lift-Elim and Lift-Ext, and it preserves unit types strictly, by
`rfl`. It does not preserve Σ-types on the nose, for the same reason as there.

This is the dual of `OverCat/Maps/CatToDisplayed.lean`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Fibration.Straightening

open scoped Displayed

/-- The vertical functor from the contravariant category model to the displayed category model:
unstraighten, forget the cleavage, and straighten. -/
def catOpToDispFunctor :
    VertFunctor ICatOpLax.{u, u, u, u} Straightening.LaxNormalCat.{u, u, u} :=
  unstraighten ⋙ᵥ SplitFibLax.forget ⋙ᵥ Straightening.straighten

/-- A type `C` of the contravariant category model as a type of the displayed model: the
straightening of its unstraightening `∫⁻ C`. -/
def catOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Straightening.LaxNormalCat.{u, u, u}.Ty Γ :=
  Straightening.straightenObj (∫⁻ C)

/-- `catOpToDisp` is the action of `catOpToDispFunctor` on objects. -/
theorem catOpToDispFunctor_obj {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    catOpToDispFunctor.obj C = catOpToDisp C :=
  rfl

/-- **The inclusion of the contravariant category model into the displayed model is a strict map
of comprehension categories**: the comprehension functors commute on the nose. -/
def catOpToDispComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ICatOpLax.{u, u, u, u}
      Straightening.LaxNormalCat.{u, u, u} where
  toPre.toDispFunctor := catOpToDispFunctor
  toPre.isCartesianMap H :=
    DisplayedModel.comprFullyFaithful.isCartesianOfMap (isCartesianComprMap ICatOpLax H)
  toPre.compr_obj _ := rfl

/-- **Lift-Intro and Lift-Elim**: the terms of `C` are those of `catOpToDisp C`. -/
def tmEquivCatOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Tm(Γ, C) ≃ Tm(Γ, catOpToDisp C) :=
  catOpToDispComprehensionMap.tmEquiv

/-- **Lift-Ext**: the context extensions by `C` and by `catOpToDisp C` are the same. -/
theorem ext_catOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Γ ▹ catOpToDisp C = Γ ▹ C :=
  rfl

/-- **The inclusion preserves unit types strictly**, by `rfl`. -/
theorem catOpToDispComprehensionMap_preservesUnit :
    catOpToDispComprehensionMap.{u}.PreservesUnit where
  obj_unit _ := rfl

end ComprehensionCategory.OverCat
