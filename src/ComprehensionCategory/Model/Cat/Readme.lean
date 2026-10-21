import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.TypeFormers.Sigma

/-!
# The category model

The full split comprehension category `ICat = Cat ⋉⁻ [−, Cat]_lax` over `Cat`, whose
comprehension is the unstraightening `F ↦ π : A ⋉ F ⥤ A` of `Displayed/Opfibration/Straightening`.

* `Basic`: `ICat` is a full split comprehension category.
* `TypeFormers/Sigma`: Σ-types, `Σ[A] B = γ ↦ A γ ⋉ B(γ, −)`.
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
