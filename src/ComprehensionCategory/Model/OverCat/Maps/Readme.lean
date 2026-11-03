import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat
import ComprehensionCategory.Model.OverCat.Maps.SmallToCat

/-!
# Maps between the models over `Cat`

Maps of comprehension categories between the models over `Cat`, and their preservation of type
formers, one file per pair of models.

* `DiscreteToCat`: forgetting the discreteness is a strict map from the discrete model to the
  category model, which preserves the Σ-types and the opposite types strictly, by `rfl`.
* `SmallToCat`: the lifts of the types and of the discrete types of level `v` into the category
  model at level `v + 1` are strict maps, along which it has universes of them.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory OverCat Opfibration.Straightening
  Displayed.Discrete.Straightening

/-! ## Main results -/

/-- **Forgetting the discreteness is a strict map of comprehension categories** from the discrete
model to the category model. -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u} ICat.{u}

/-- **It preserves Σ-types strictly.** -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap_preservesSigma :
    forgetComprehensionMap.{u}.PreservesSigma

/-- **It preserves opposite types strictly.** -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap_obj_op {Γ : Cat.{u, u}}
    (A : IDisc.{u}.Ty Γ) :
    forgetComprehensionMap.toPre.obj (DiscreteModel.op A) =
      CatModel.op (forgetComprehensionMap.toPre.obj A)

section Small

universe v

/-- **The lifts of the types of level `v`** are strict maps of comprehension categories. -/
recall ComprehensionCategory.OverCat.liftComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) CatModel.SmallICat.{v} ICat.{v + 1}

recall ComprehensionCategory.OverCat.liftDiscComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) DiscreteModel.SmallIDisc.{v} ICat.{v + 1}

end Small
