import Displayed.CodCatEquiv.Fibration
import ComprehensionCategory.Model.OverCat.CatOp.Extension
import Displayed.Fibration.SplitFibLax
import Displayed.Fibration.Straightening.Equivalence
import ComprehensionCategory.Basic

/-!
# The contravariant category model

The *contravariant category model* is the full split comprehension category over `Cat` given by
the split fibration `ICatOpLax` of functors `Aᵒᵖ ⥤ Cat` and lax transformations. Its
comprehension functor `compr : ICatOpLax ⟶ cod Cat` sends `F : Aᵒᵖ ⥤ Cat` to the projection
`π : A ⋉⁻ F ⥤ A` of the total category of its unstraightening. It is the composite of

* the unstraightening `ICatOpLax ⟶ SplitFibLax` (`Displayed/Fibration/Straightening`),
* the functor `SplitFibLax ⟶ DisplayedCat` forgetting the cleavage, and
* the total category functor `DisplayedCat ⟶ cod Cat`,

all three fully faithful, which gives the fullness. The unstraightening of the reindexing
`u.op ⋙ G` is the reindexing of the unstraightening of `G`, by `rfl`, and reindexing goes to
pullbacks (`DisplayedCat.isCartesianTotalMapClift`), which gives the comprehension structure.

This is the dual of `OverCat/Cat/Basic.lean`.
-/

universe u

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Displayed Fibration.Straightening

/-- The comprehension functor of the contravariant category model: unstraighten, forget the
cleavage, and take the total category. -/
def compr : VertFunctor ICatOpLax.{u, u, u, u} (cod Cat.{u, u}) :=
  unstraighten ⋙ᵥ SplitFibLax.forget ⋙ᵥ DisplayedCat.total

/-- **The comprehension functor sends the chosen lifts to cartesian morphisms**:
`A ⋉⁻ ICatOpLax.pull u G` is the pullback of `B ⋉⁻ G` along `u`. -/
def isCartesianComprClift {A B : Cat.{u, u}} (u : A ⟶ B) (G : Bᵒᵖ ⥤ Cat.{u, u}) :
    IsCartesian (compr.map (ICatOpLax.clift u G)) :=
  DisplayedCat.isCartesianTotalMapClift (u := u) (E := ∫⁻ G)

/-- **The comprehension functor is fully faithful.** -/
def comprFullyFaithful : compr.{u}.FullyFaithful :=
  unstraightenFullyFaithful.comp
    (SplitFibLax.forgetFullyFaithful.comp DisplayedCat.totalFullyFaithful)

@[instance_reducible]
instance comprehension : Comprehension ICatOpLax.{u, u, u, u} :=
  Comprehension.ofClift compr isCartesianComprClift

/-- **The contravariant category model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension ICatOpLax.{u, u, u, u} where

@[instance_reducible]
instance fullComprehension : FullComprehension ICatOpLax.{u, u, u, u} where
  comprFullyFaithful := comprFullyFaithful

end ComprehensionCategory.CatOpModel
