import Displayed.Opfibration.Straightening.Unstraighten
import ComprehensionCategory.Basic

/-!
# The category model

The *category model* is the full split comprehension category over `Cat` given by the split
fibration `ICat` of functors into `Cat` and lax transformations, whose comprehension functor is
the unstraightening `ICat ⟶ cod Cat`, sending `F : A ⥤ Cat` to the projection `π : A ⋉ F ⥤ A` of
its Grothendieck construction (`Displayed/Opfibration/Straightening`). That unstraightening sends
the chosen lifts to pullbacks and is fully faithful gives the comprehension structure and its
fullness.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Opfibration.Straightening

@[instance_reducible]
instance comprehension : Comprehension ICat.{u} :=
  Comprehension.ofClift unstraighten isCartesianUnstraightenClift

/-- **The category model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension ICat.{u} where

@[instance_reducible]
instance fullComprehension : FullComprehension ICat.{u} where
  comprFullyFaithful := unstraightenFullyFaithful

end ComprehensionCategory.CatModel
