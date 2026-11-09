import ComprehensionCategory.Basic
import Displayed.CodCatEquiv.Fibration
import Displayed.Discrete.Basic
import Displayed.Fibration.SplitFibLax

/-!
# The models of fibrations

The categories of displayed categories (`DisplayedCat`), split opfibrations (`SplitOpfibLax`),
split fibrations (`SplitFibLax`) and discrete opfibrations (`DiscOpfibCat`), displayed over `Cat`,
are comprehension categories: the comprehension of a type `X` over `Γ` is the projection of its
total category, `π : X.Total ⥤ Γ`. The comprehension functor forgets the (op)cleavage and the
discreteness, and takes the total category (`DisplayedCat.total`). These are the *functor model*
(up to the equivalence `DisplayedCat ≃ cod Cat`), the *split opfibration model*, the *split
fibration model* and the *discrete opfibration model* of the paper, whose types are the
unstraightenings of those of the displayed, covariant, contravariant and discrete category models
(`OverCat/Maps/Unstraighten`).

The paper takes them as full subcategories of `Cat^→`, with the pullbacks as chosen lifts, which
are not split. Here their types are displayed categories, and reindexing them is strictly unital
and associative, so they are split fibrations over `Cat` (`DisplayedCat.splitFib`,
`SplitOpfibLax.splitFibCat`, `SplitFibLax.splitFibCat`, `DiscOpfibCat.splitFibCat`). The
comprehension functors send the chosen lifts to pullbacks (`DisplayedCat.isCartesianTotalMapClift`)
and are fully faithful, as composites of fully faithful functors. So all four are full split
comprehension categories. Only `cod Cat` is not split (`Model/Codomain`).
-/

universe u

namespace ComprehensionCategory.FibredModel

open CategoryTheory Displayed

/-! ## Displayed categories -/

/-- The comprehension of displayed categories: their total categories. -/
@[instance_reducible]
instance displayedCatComprehension : Comprehension DisplayedCat.{u, u, u, u} :=
  Comprehension.ofClift DisplayedCat.total fun u E =>
    DisplayedCat.isCartesianTotalMapClift (u := u) (E := E)

/-- **The displayed categories** form a full split comprehension category over `Cat`. -/
instance displayedCatSplitComprehension : SplitComprehension DisplayedCat.{u, u, u, u} where

@[instance_reducible]
instance displayedCatFullComprehension : FullComprehension DisplayedCat.{u, u, u, u} where
  comprFullyFaithful := DisplayedCat.totalFullyFaithful

/-! ## Split opfibrations -/

/-- The comprehension functor of the split opfibration model: forget the opcleavage, and take the
total category. -/
def splitOpfibCompr : VertFunctor SplitOpfibLax.{u, u, u, u} (cod Cat.{u, u}) :=
  SplitOpfibLax.forget ⋙ᵥ DisplayedCat.total

@[instance_reducible]
instance splitOpfibComprehension : Comprehension SplitOpfibLax.{u, u, u, u} :=
  Comprehension.ofClift splitOpfibCompr fun u X =>
    DisplayedCat.isCartesianTotalMapClift (u := u) (E := X.toDisplayed)

/-- **The split opfibration model** is a full split comprehension category over `Cat`. -/
instance splitOpfibSplitComprehension : SplitComprehension SplitOpfibLax.{u, u, u, u} where

@[instance_reducible]
instance splitOpfibFullComprehension : FullComprehension SplitOpfibLax.{u, u, u, u} where
  comprFullyFaithful := SplitOpfibLax.forgetFullyFaithful.comp DisplayedCat.totalFullyFaithful

/-! ## Split fibrations -/

/-- The comprehension functor of the split fibration model: forget the cleavage, and take the total
category. -/
def splitFibCompr : VertFunctor SplitFibLax.{u, u, u, u} (cod Cat.{u, u}) :=
  SplitFibLax.forget ⋙ᵥ DisplayedCat.total

@[instance_reducible]
instance splitFibComprehension : Comprehension SplitFibLax.{u, u, u, u} :=
  Comprehension.ofClift splitFibCompr fun u X =>
    DisplayedCat.isCartesianTotalMapClift (u := u) (E := X.toDisplayed)

/-- **The split fibration model** is a full split comprehension category over `Cat`. -/
instance splitFibSplitComprehension : SplitComprehension SplitFibLax.{u, u, u, u} where

@[instance_reducible]
instance splitFibFullComprehension : FullComprehension SplitFibLax.{u, u, u, u} where
  comprFullyFaithful := SplitFibLax.forgetFullyFaithful.comp DisplayedCat.totalFullyFaithful

/-! ## Discrete opfibrations -/

/-- The comprehension functor of the discrete opfibration model: forget the discreteness and the
opcleavage, and take the total category. -/
def discOpfibCompr : VertFunctor DiscOpfibCat.{u, u, u, u} (cod Cat.{u, u}) :=
  DiscOpfibCat.forget ⋙ᵥ splitOpfibCompr

@[instance_reducible]
instance discOpfibComprehension : Comprehension DiscOpfibCat.{u, u, u, u} :=
  Comprehension.ofClift discOpfibCompr fun u X =>
    DisplayedCat.isCartesianTotalMapClift (u := u) (E := X.toDisplayed)

/-- **The discrete opfibration model** is a full split comprehension category over `Cat`. -/
instance discOpfibSplitComprehension : SplitComprehension DiscOpfibCat.{u, u, u, u} where

@[instance_reducible]
instance discOpfibFullComprehension : FullComprehension DiscOpfibCat.{u, u, u, u} where
  comprFullyFaithful := DiscOpfibCat.forgetFullyFaithful.comp
    (SplitOpfibLax.forgetFullyFaithful.comp DisplayedCat.totalFullyFaithful)

end ComprehensionCategory.FibredModel
