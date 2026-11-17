import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Unit
import Tactic.KernelTactic

/-!
# From the discrete model to the category model

Forgetting the discreteness, `IDisc.forget : IDisc ⟶ ICatLax`, is a strict map of comprehension
categories over the identity of `Cat` (`forgetComprehensionMap`): the comprehension functor of the
discrete model is `IDisc.forget ⋙ᵥ compr` by definition, so both axioms hold by `rfl`.

It preserves the type formers strictly, by `rfl`, since those of the discrete model are those of
the category model with a proof of discreteness:

* the Σ-types and the pairings (`forgetComprehensionMap_preservesSigma`);
* the opposite types (`forgetComprehensionMap_obj_op`);
* the unit types (`forgetComprehensionMap_preservesUnit`), and so the stars.

It sends a term to the term with the same section, which commutes with substitution by `rfl`
(`forgetComprehensionMap_tmEquiv_pull`), as any strict map
(`StrictComprehensionMap.tmEquiv_pull`); here the two terms have the same type by `rfl`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel DiscreteModel

open scoped Displayed

/-- **Forgetting the discreteness is a strict map of comprehension categories** from the discrete
model to the category model, over the identity of `Cat`: the comprehension functor of the discrete
model is `IDisc.forget ⋙ᵥ compr`, so the comprehension functors commute on the nose. -/
def forgetComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u, u, u, u} ICatLax.{u, u, u, u} where
  toPre.toDispFunctor := IDisc.forget.toDispFunctor
  toPre.isCartesianMap := IDisc.forget.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **Forgetting the discreteness preserves Σ-types strictly**: the Σ-types and the pairings of the
discrete model are those of the category model. -/
theorem forgetComprehensionMap_preservesSigma : forgetComprehensionMap.{u}.PreservesSigma where
  obj_sigma _ _ := rfl
  map_pair _ _ := HEq.rfl

/-- **Forgetting the discreteness preserves opposite types strictly.** -/
theorem forgetComprehensionMap_obj_op {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) :
    forgetComprehensionMap.toPre.obj Aᵒᵖ = (forgetComprehensionMap.toPre.obj A)ᵒᵖ :=
  rfl

/-- **Forgetting the discreteness preserves unit types strictly**: the unit types of the discrete
model are those of the category model. -/
theorem forgetComprehensionMap_preservesUnit : forgetComprehensionMap.{u}.PreservesUnit where
  obj_unit _ := rfl

/-- **Forgetting the discreteness commutes with the substitution of terms**, as any strict map. -/
theorem forgetComprehensionMap_tmEquiv_pull {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    {A : IDisc.{u, u}.Ty Γ} (t : Tm(Γ, A)) :
    forgetComprehensionMap.tmEquiv (t⦃σ⦄) = (forgetComprehensionMap.tmEquiv t)⦃σ⦄ :=
  eq_of_heq (forgetComprehensionMap.tmEquiv_pull σ t)

end ComprehensionCategory.OverCat
