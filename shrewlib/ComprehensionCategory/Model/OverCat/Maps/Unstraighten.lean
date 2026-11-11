import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Fibred.Basic
import ComprehensionCategory.Model.OverCat.Cat.Basic
import ComprehensionCategory.Model.OverCat.CatOp.Basic
import ComprehensionCategory.Model.OverCat.Discrete.Basic
import ComprehensionCategory.Model.OverCat.Displayed.Basic
import Displayed.Discrete.Straightening.Equivalence

/-!
# The unstraightenings as maps of comprehension categories

Each of the four category models is related to a model of fibrations (`OverCat/Fibred`) by an
unstraightening, an equivalence over `Cat` (straightening–unstraightening):

* the category model `ICatLax` and the split opfibrations `SplitOpfibLax`;
* the contravariant category model `ICatOpLax` and the split fibrations `SplitFibLax`;
* the discrete model `IDisc` and the discrete opfibrations `DiscOpfibCat`;
* the displayed category model `IProf` and the displayed categories `DisplayedCat`.

**The equivalences are fibred**: each unstraightening sends the chosen lifts to the chosen lifts, on
the nose (`unstraightenCatCartesian`, …), since the unstraightening of the reindexing `u ⋙ G` is
the reindexing of the unstraightening of `G`, and both lifts are identities; their laws hold by
`rfl`. Being equivalences, they preserve all cartesian morphisms (`VertEquivalence.isCartesianMap`).

**Each category model is the model of fibrations, along the unstraightening**: the unstraightening
is a strict map of comprehension categories over the identity of `Cat`
(`unstraightenCatComprehensionMap`, …). Both axioms hold by `rfl`, since the comprehension functor
of each category model is defined as its unstraightening followed by that of the model of
fibrations, forgetting the (op)cleavage and the discreteness and taking total categories. This is
how the paper obtains the split models from the non-split ones.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed

/-! ## The unstraightenings preserve the chosen lifts -/

/-- **The unstraightening of indexed categories preserves the chosen lifts.** -/
def unstraightenCatCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) Opfibration.Straightening.ICatLax.{u, u, u, u}
      SplitOpfibLax.{u, u, u, u} where
  toPre := { toDispFunctor := Opfibration.Straightening.unstraighten }

/-- **The unstraightening of contravariant indexed categories preserves the chosen lifts.** -/
def unstraightenCatOpCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) Fibration.Straightening.ICatOpLax.{u, u, u, u}
      SplitFibLax.{u, u, u, u} where
  toPre := { toDispFunctor := Fibration.Straightening.unstraighten }

/-- **The unstraightening of indexed discrete categories preserves the chosen lifts.** -/
def unstraightenDiscCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) Discrete.Straightening.IDisc.{u, u, u, u}
      DiscOpfibCat.{u, u, u, u} where
  toPre := { toDispFunctor := Discrete.Straightening.unstraighten }

/-! ## The unstraightenings are strict maps of comprehension categories -/

/-- **The category model is the split opfibration model**, along the unstraightening, a strict map
of comprehension categories. -/
def unstraightenCatComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Opfibration.Straightening.ICatLax.{u, u, u, u}
      SplitOpfibLax.{u, u, u, u} where
  toPre.toDispFunctor := Opfibration.Straightening.unstraighten
  toPre.isCartesianMap := Opfibration.Straightening.straighteningEquivLax.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **The contravariant category model is the split fibration model**, along the unstraightening,
a strict map of comprehension categories. -/
def unstraightenCatOpComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Fibration.Straightening.ICatOpLax.{u, u, u, u}
      SplitFibLax.{u, u, u, u} where
  toPre.toDispFunctor := Fibration.Straightening.unstraighten
  toPre.isCartesianMap := Fibration.Straightening.straighteningEquivLax.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **The discrete model is the discrete opfibration model**, along the unstraightening, a strict
map of comprehension categories. -/
def unstraightenDiscComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Discrete.Straightening.IDisc.{u, u, u, u}
      DiscOpfibCat.{u, u, u, u} where
  toPre.toDispFunctor := Discrete.Straightening.unstraighten
  toPre.isCartesianMap := Discrete.Straightening.straighteningEquiv.isCartesianMap
  toPre.compr_obj _ := rfl

/-- **The displayed category model is the model of displayed categories**, along the
unstraightening, a strict map of comprehension categories. -/
def unstraightenDisplayedComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Straightening.IProf.{u, u, u}
      DisplayedCat.{u, u, u, u} where
  toPre.toDispFunctor := Straightening.unstraighten
  toPre.isCartesianMap := Straightening.isCartesianUnstraightenMap
  toPre.compr_obj _ := rfl

end ComprehensionCategory.OverCat
