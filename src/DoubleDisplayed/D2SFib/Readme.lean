import DoubleDisplayed.D2SFib.Basic
import DoubleDisplayed.D2SFib.Category
import DoubleDisplayed.D2SFib.Straightening.Readme

/-!
# Dependent 2-sided fibrations

In this folder we define dependent 2-sided fibrations (D2SFibs) over a split opfibration `B` over
`A`: categories doubly displayed over `B` with chosen cartesian lifts of the vertical morphisms of
`B`, chosen opcartesian lifts over those of `B`, and a strict interchange between the two. The
split ones form a category, which straightening shows equivalent to the functors from the total
category of the dual opfibration of `B` to `Cat`.

The files are:

* `Basic`: cloven (`D2SFib`), pre-split (`PreSplitD2SFib`) and split (`SplitD2SFib`) D2SFibs,
  like the (op)fibrations of `Displayed/`.
* `Category`: the category `D2SFibCat B` of split D2SFibs, whose morphisms preserve the chosen
  lifts.
* `Straightening/`: the equivalence `(Bᵒᵖ.Total ⥤ Cat) ≌ D2SFibCat B`.
-/
