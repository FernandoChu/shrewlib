import Displayed.CodCatEquiv.Fibration
import ComprehensionCategory.Model.OverCat.Cat.Extension
import Displayed.Opfibration.SplitOpfibCat
import ComprehensionCategory.Basic

/-!
# The category model

The *category model* is the full split comprehension category over `Cat` given by the split
fibration `ICat` of functors into `Cat` and lax transformations. Its comprehension functor
`compr : ICat ⟶ cod Cat` sends `F : A ⥤ Cat` to the projection `π : A ⋉ F ⥤ A` of the total
category of its unstraightening. It is the composite of

* the unstraightening `ICat ⟶ SplitOpfibCat` (`Displayed/Opfibration/Straightening`),
* the functor `SplitOpfibCat ⟶ DisplayedCat` forgetting the opcleavage, and
* the total category functor `DisplayedCat ⟶ cod Cat`,

all three fully faithful, which gives the fullness. The unstraightening of the reindexing
`u ⋙ G` is the reindexing of the unstraightening of `G`, by `rfl`, and reindexing goes to
pullbacks (`DisplayedCat.isCartesianTotalMapClift`), which gives the comprehension structure.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Opfibration.Straightening

/-- The comprehension functor of the category model: unstraighten, forget the opcleavage, and take
the total category. -/
def compr : VertFunctor ICat.{u} (cod Cat.{u, u}) :=
  unstraighten ⋙ᵥ SplitOpfibCat.forget ⋙ᵥ DisplayedCat.total

/-- **The comprehension functor sends the chosen lifts to cartesian morphisms**: `A ⋉ ICat.pull u G`
is the pullback of `B ⋉ G` along `u`. -/
def isCartesianComprClift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) :
    IsCartesian (compr.map (ICat.clift u G)) :=
  DisplayedCat.isCartesianTotalMapClift (u := u) (E := ∫ G)

/-- **The comprehension functor is fully faithful.** -/
def comprFullyFaithful : compr.{u}.FullyFaithful :=
  unstraightenFullyFaithful.comp
    (SplitOpfibCat.forgetFullyFaithful.comp DisplayedCat.totalFullyFaithful)

@[instance_reducible]
instance comprehension : Comprehension ICat.{u} :=
  Comprehension.ofClift compr isCartesianComprClift

/-- **The category model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension ICat.{u} where

@[instance_reducible]
instance fullComprehension : FullComprehension ICat.{u} where
  comprFullyFaithful := comprFullyFaithful

end ComprehensionCategory.CatModel
