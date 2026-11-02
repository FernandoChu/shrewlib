import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.TypeFormers.Sigma
import ComprehensionCategory.Model.Cat.TypeFormers.Op
import ComprehensionCategory.Model.Cat.TypeFormers.Hom

/-!
# The category model

In this folder we define the category model: the comprehension category `ICat` over `Cat`, whose
types in context `Γ` are the functors `Γ ⥤ Cat`, and whose context extension `Γ ▹ A` is the
total category `Γ ⋉ A` of the unstraightening of `A`. It is full and split, and it has Σ-types:
`Σ[A] B` is the straightening of the composite of the split opfibrations `∫ A` over
`Γ` and `∫ B` over `Γ ⋉ A`. It has opposite types: `Aᵒᵖ` is the pointwise opposite of `A`. It has
Hom-types: `Hom[A]` sends `((γ, a), b)` to the discrete category on the morphisms `a ⟶ b` of
`A γ`.

The files give its ingredients:

* `Extension`: the context extension `Γ ⋉ A`.
* `Basic`: the comprehension functor `compr : ICat ⟶ cod Cat`, the unstraightening followed by
  forgetting the opcleavage and taking total categories, which sends the chosen lifts to pullbacks
  and is fully faithful, so that `ICat` is a full split comprehension category.
* `TypeFormers/Sigma`: Σ-types, whose pairing is the inverse of the counit of
  straightening–unstraightening at the composite.
* `OpFunctor`: the opposite functor `opFunctor' : Cat ⥤ Cat`, involutive on the nose, by taking
  the opposite category structure on the same objects, and discrete categories `discrete' S`,
  which are their own opposites, by `propext`. It imports no rewrite rules.
* `TypeFormers/Op`: opposite types, `A ⋙ opFunctor'`, whose rules hold by `rfl`.
* `TypeFormers/Hom`: Hom-types, whose stability holds by `rfl` and Hom-op by `propext`.
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

/-- The opposite functor is involutive on the nose, and is Mathlib's `Cat.opFunctor` up to
isomorphism. -/
recall ComprehensionCategory.CatModel.opFunctor'_comp_opFunctor' :
    CatModel.opFunctor'.{u} ⋙ CatModel.opFunctor' = 𝟭 _

recall ComprehensionCategory.CatModel.opFunctor'Iso : CatModel.opFunctor'.{u} ≅ Cat.opFunctor

/-- **The category model has opposite types.** -/
recall ComprehensionCategory.CatModel.hasOp : HasOp ICat.{u}

/-- A discrete category is its own opposite. -/
recall ComprehensionCategory.CatModel.opFunctor'_obj_discrete' (S : Type u) :
    CatModel.opFunctor'.obj (CatModel.discrete' S) = CatModel.discrete' S

/-- **The category model has Hom-types.** -/
recall ComprehensionCategory.CatModel.hasHom : HasHom ICat.{u}
