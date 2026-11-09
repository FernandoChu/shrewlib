import ComprehensionCategory.Model.OverCat.Fibred.Basic

/-!
# The models of fibrations

The comprehension categories over `Cat` whose types are fibrations rather than indexed categories:
the displayed categories (`DisplayedCat`), the split opfibrations (`SplitOpfibLax`), the split
fibrations (`SplitFibLax`) and the discrete opfibrations (`DiscOpfibCat`), with the total
categories as comprehension. These are the functor model (up to `DisplayedCat ≃ cod Cat`) and the
split opfibration, split fibration and discrete opfibration models of the paper, which takes them
as non-split comprehension categories, full subcategories of `Cat^→`. Here reindexing is strictly
unital and associative, so they are full split comprehension categories.

* `Basic`: their comprehension structures, fullness and splitness.

The category models are these models along the unstraightenings, which are strict maps of
comprehension categories (`OverCat/Maps/Unstraighten`).
-/

universe u

open CategoryTheory Displayed ComprehensionCategory

/-! ## Main results -/

/-- **The four models of fibrations** are full split comprehension categories over `Cat`. -/
recall ComprehensionCategory.FibredModel.displayedCatFullComprehension :
    FullComprehension DisplayedCat.{u, u, u, u}

recall ComprehensionCategory.FibredModel.splitOpfibFullComprehension :
    FullComprehension SplitOpfibLax.{u, u, u, u}

recall ComprehensionCategory.FibredModel.splitFibFullComprehension :
    FullComprehension SplitFibLax.{u, u, u, u}

recall ComprehensionCategory.FibredModel.discOpfibFullComprehension :
    FullComprehension DiscOpfibCat.{u, u, u, u}

example : SplitComprehension SplitOpfibLax.{u, u, u, u} := inferInstance
