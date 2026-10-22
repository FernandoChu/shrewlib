import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.TypeFormers.Sigma

/-!
# The category model

In this folder we define the category model: the comprehension category `ICat` over `Cat`, whose
types in context `Γ` are the functors `Γ ⥤ Cat`, and whose context extension `Γ ▹ A` is the
Grothendieck construction `Γ ⋉ A`. Its comprehension is the unstraightening of
`Displayed/Opfibration/Straightening`. It is full and split, and it has Σ-types: `Σ[A] B` sends
`γ` to the Grothendieck construction `A γ ⋉ B(γ, −)`.

The files give its ingredients:

* `Basic`: the comprehension structure on `ICat`, which is full and split.
* `TypeFormers/Sigma`: Σ-types, with their pairing and unpairing.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory Opfibration.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **The category model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.CatModel.splitComprehension : SplitComprehension ICat.{u}

recall ComprehensionCategory.CatModel.fullComprehension : FullComprehension ICat.{u}

/-- **The category model has Σ-types.** -/
recall ComprehensionCategory.CatModel.hasSigma : HasSigma ICat.{u}
