import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Discrete.Small
import ComprehensionCategory.Model.OverCat.CatOp.Small

/-!
# From the types of a lower level to the category models

The lifts of the types of level `v`, `SmallICat.lift : SmallICat ⟶ ICatLax`, and of the discrete
types of level `v`, `SmallIDisc.lift : SmallIDisc ⟶ ICatLax`, into the category model at level
`v + 1` are strict maps of comprehension categories over the identity of `Cat.{v + 1, v + 1}`
(`liftComprehensionMap`, `liftDiscComprehensionMap`): the comprehension functors of `SmallICat` and
`SmallIDisc` are the lifts followed by that of the category model by definition, so both axioms
hold by `rfl`. So is the lift of the contravariant types of level `v`,
`SmallICatOp.lift : SmallICatOp ⟶ ICatOpLax`, into the contravariant category model
(`liftOpComprehensionMap`). These are the maps along which the terms of the universes of these
types in the category model decode (`Cat/TypeFormers/Universe`, `Shared/Universe`).
-/

universe v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel DiscreteModel

/-- **The lift of the types of level `v` is a strict map of comprehension categories** into the
category model. -/
def liftComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) SmallICat.{v} ICatLax.{v + 1, v + 1, v + 1, v + 1}
    where
  toPre.toDispFunctor := SmallICat.lift.toDispFunctor
  toPre.isCartesianMap := SmallICat.lift.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **The lift of the discrete types of level `v` is a strict map of comprehension categories**
into the category model. -/
def liftDiscComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) SmallIDisc.{v}
    ICatLax.{v + 1, v + 1, v + 1, v + 1} where
  toPre.toDispFunctor := SmallIDisc.lift.toDispFunctor
  toPre.isCartesianMap := SmallIDisc.lift.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **The lift of the contravariant types of level `v` is a strict map of comprehension
categories** into the contravariant category model. -/
def liftOpComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) CatOpModel.SmallICatOp.{v}
    Fibration.Straightening.ICatOpLax.{v + 1, v + 1, v + 1, v + 1} where
  toPre.toDispFunctor := CatOpModel.SmallICatOp.lift.toDispFunctor
  toPre.isCartesianMap := CatOpModel.SmallICatOp.lift.isCartesianMap
  toPre.compr_obj _ := rfl

end ComprehensionCategory.OverCat
