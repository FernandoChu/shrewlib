import DoubleDisplayed.D2SFib.Basic
import DoubleDisplayed.D2SFib.Map
import DoubleDisplayed.D2SFib.Category
import DoubleDisplayed.D2SFib.DProf
import DoubleDisplayed.D2SFib.D2SFibStr
import DoubleDisplayed.D2SFib.Straightening.Readme

/-!
# Dependent 2-sided fibrations

In this folder we define dependent 2-sided fibrations (D2SFibs) over a split opfibration `B` over
`A`: categories doubly displayed over `B` with chosen cartesian lifts of the vertical morphisms of
`B`, chosen opcartesian lifts over those of `B`, and a strict interchange between the two. The
split ones form a category `D2SFibCat B`. Over all split opfibrations, with the opcartesian
functors between them, the split D2SFibs form a split fibration over `SplitOpfibStr`. Over all
indexed categories `F : A ⥤ Cat`, with the strict transformations between them, the dependent
profunctors, the functors from the total category of the dual of `∫ F` to `Cat`, form a split
fibration over `ICatStr`. Straightening is an equivalence between the two, over the equivalence
`ICatStr ≃ SplitOpfibStr`.

The files are:

* `Basic`: cloven (`D2SFib`), pre-split (`PreSplitD2SFib`) and split (`SplitD2SFib`) D2SFibs,
  like the (op)fibrations of `Displayed/`.
* `Map`: maps of D2SFibs over an opcartesian functor `H : B ⟶ B'` (`D2SFibMap`), which preserve
  the chosen lifts, and the reindexing of a D2SFib along `H`.
* `Category`: the category `D2SFibCat B` of split D2SFibs, whose morphisms are the maps of
  D2SFibs over the identity of `B`.
* `DProf`: the dependent profunctors over all indexed categories, doubly displayed over `ICatStr`,
  a split fibration by precomposition.
* `D2SFibStr`: the split D2SFibs over all split opfibrations, doubly displayed over
  `SplitOpfibStr`, a split fibration by reindexing.
* `Straightening/`: the equivalence between `DProf` and `D2SFibStr`, over the equivalence
  `ICatStr ≃ SplitOpfibStr`.
-/
