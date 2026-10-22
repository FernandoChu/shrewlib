import DoubleDisplayed.Basic
import DoubleDisplayed.Cartesian
import DoubleDisplayed.Total
import DoubleDisplayed.D2SFib.Readme

/-!
# Doubly displayed categories

In this folder we define categories doubly displayed over a displayed category `B` over `A`:
their objects are indexed by the objects of `B`, and their morphisms by the morphisms of `B`. They
are developed in parallel with `Displayed/`, and we define and straighten the dependent 2-sided
fibrations among them.

The files are:

* `Basic`: doubly displayed categories over `B`, their fibers and vertical functors.
* `Cartesian`: (op)cartesian morphisms, one level up.
* `Total`: the total displayed category `C.total : Displayed A`, whose objects over `a` are pairs
  of objects of `B` and `C`.
* `D2SFib/`: dependent 2-sided fibrations and their straightening.
-/
