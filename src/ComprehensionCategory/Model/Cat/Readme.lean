import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.TypeFormers.Sigma

/-!
# The category model

In this folder we define the category model: the comprehension category `ICat` over `Cat`, whose
types in context `Γ` are the functors `Γ ⥤ Cat`, and whose context extension `Γ ▹ A` is the
total category `Γ ⋉ A` of the unstraightening of `A`. It is full and split, and it has Σ-types:
`Σ[A] B` is the straightening of the composite of the split opfibrations `∫ A` over
`Γ` and `∫ B` over `Γ ⋉ A`.

The files give its ingredients:

* `Extension`: the context extension `Γ ⋉ A`.
* `Basic`: the comprehension functor `compr : ICat ⟶ cod Cat`, the unstraightening followed by
  forgetting the opcleavage and taking total categories, which sends the chosen lifts to pullbacks
  and is fully faithful, so that `ICat` is a full split comprehension category.
* `TypeFormers/Sigma`: Σ-types, whose pairing is the inverse of the counit of
  straightening–unstraightening at the composite.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory Opfibration.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **The category model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.CatModel.splitComprehension : SplitComprehension ICat.{u}

recall ComprehensionCategory.CatModel.fullComprehension : FullComprehension ICat.{u}

/-- The chosen lifts go to pullbacks: `A ⋉ ICat.pull u G` is the pullback of `B ⋉ G` along `u`. -/
recall ComprehensionCategory.CatModel.isCartesianComprClift {A B : Cat.{u, u}}
    (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : IsCartesian (CatModel.compr.map (ICat.clift u G))

/-- The comprehension functor is fully faithful: functors `A ⋉ F ⥤ B ⋉ G` over `u` are lax
transformations `LaxTrans F (u ⋙ G)`. -/
recall ComprehensionCategory.CatModel.comprFullyFaithful : CatModel.compr.{u}.FullyFaithful

/-- **The category model has Σ-types.** -/
recall ComprehensionCategory.CatModel.hasSigma : HasSigma ICat.{u}
