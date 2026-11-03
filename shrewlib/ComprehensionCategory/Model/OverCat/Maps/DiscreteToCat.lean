import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Sigma

/-!
# From the discrete model to the category model

Forgetting the discreteness, `IDisc.forget : IDisc ⟶ ICatLax`, is a strict map of comprehension
categories over the identity of `Cat` (`forgetComprehensionMap`): the comprehension functor of the
discrete model is `IDisc.forget ⋙ᵥ compr` by definition, so both axioms hold by `rfl`.

It preserves the type formers strictly, by `rfl`, since those of the discrete model are those of
the category model with a proof of discreteness:

* the Σ-types and the pairings (`forgetComprehensionMap_preservesSigma`);
* the opposite types (`forgetComprehensionMap_obj_op`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel DiscreteModel

open scoped Displayed

/-- **Forgetting the discreteness is a strict map of comprehension categories** from the discrete
model to the category model, over the identity of `Cat`: the comprehension functor of the discrete
model is `IDisc.forget ⋙ᵥ compr`, so the comprehension functors commute on the nose. -/
def forgetComprehensionMap : StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u} ICatLax.{u} where
  toPre.toDispFunctor := IDisc.forget.toDispFunctor
  toPre.isCartesianMap := IDisc.forget.isCartesianMap
  toPre.compr_obj _ := rfl
  compr_map _ := rfl

/-- **Forgetting the discreteness preserves Σ-types strictly**: the Σ-types and the pairings of the
discrete model are those of the category model. -/
theorem forgetComprehensionMap_preservesSigma : forgetComprehensionMap.{u}.PreservesSigma where
  obj_sigma _ _ := rfl
  map_pair _ _ := HEq.rfl

/-- **Forgetting the discreteness preserves opposite types strictly.** -/
theorem forgetComprehensionMap_obj_op {Γ : Cat.{u, u}} (A : IDisc.{u}.Ty Γ) :
    forgetComprehensionMap.toPre.obj Aᵒᵖ = (forgetComprehensionMap.toPre.obj A)ᵒᵖ :=
  rfl

end ComprehensionCategory.OverCat
