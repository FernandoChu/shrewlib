import DoubleDisplayed.D2SFib.Basic
import DoubleDisplayed.D2SFib.Map
import DoubleDisplayed.D2SFib.Category
import DoubleDisplayed.D2SFib.DProfStr
import DoubleDisplayed.D2SFib.D2SFibStr
import DoubleDisplayed.D2SFib.Straightening.Readme

/-!
# Dependent 2-sided fibrations

In this folder we define dependent 2-sided fibrations (D2SFibs) over a split opfibration `B` over
`A`: categories doubly displayed over `B` with chosen cartesian lifts of the vertical morphisms of
`B`, chosen opcartesian lifts over those of `B`, and a strict interchange between the two. The
split ones form a category, which straightening shows equivalent to the functors from the total
category of the dual opfibration of `B` to `Cat`, the dependent profunctors over `B`. Over all
split opfibrations, with the opcartesian functors between them, both form split fibrations over
`SplitOpfibStr`, and straightening is an equivalence of fibred categories.

The files are:

* `Basic`: cloven (`D2SFib`), pre-split (`PreSplitD2SFib`) and split (`SplitD2SFib`) D2SFibs,
  like the (op)fibrations of `Displayed/`.
* `Map`: maps of D2SFibs over an opcartesian functor `H : B ⟶ B'` (`D2SFibMap`), which preserve
  the chosen lifts, and the reindexing of a D2SFib along `H`.
* `Category`: the category `D2SFibCat B` of split D2SFibs, whose morphisms are the maps of
  D2SFibs over the identity of `B`.
* `DProfStr`: the dependent profunctors over all split opfibrations, doubly displayed over
  `SplitOpfibStr`, a split fibration by precomposition.
* `D2SFibStr`: the split D2SFibs over all split opfibrations, doubly displayed over
  `SplitOpfibStr`, a split fibration by reindexing.
* `Straightening/`: the equivalence `(Bᵒᵖ.Total ⥤ Cat) ≌ D2SFibCat B`, and its extension to an
  equivalence `DProfStr ≃ D2SFibStr` of fibred categories over `SplitOpfibStr`, and over
  `ICatStr`.
-/
