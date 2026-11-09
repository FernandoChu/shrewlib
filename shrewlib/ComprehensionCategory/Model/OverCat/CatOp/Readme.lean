import ComprehensionCategory.Model.OverCat.CatOp.Basic
import ComprehensionCategory.Model.OverCat.CatOp.Small
import ComprehensionCategory.Model.OverCat.CatOp.Term
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Unit

/-!
# The contravariant category model

In this folder we define the contravariant category model: the comprehension category `ICatOpLax`
over `Cat`, whose types in context `Γ` are the functors `Γᵒᵖ ⥤ Cat`, and whose context extension
`Γ ▹ A` is the total category `Γ ⋉⁻ A` of the unstraightening of `A`, a split fibration over `Γ`.
It is full and split, and it has Σ-types: `Σ[A] B` is the straightening of the composite of the
split fibrations `∫⁻ A` over `Γ` and `∫⁻ B` over `Γ ⋉⁻ A`. It has unit types, the constant types at
the terminal category. It has opposite types: `Aᵒᵖ` is the
pointwise opposite of `A`. The terms `Tm(Γ, A)` of a constant type at a category `K` are the
functors `Γ ⥤ K`.

The morphisms of `ICatOpLax` are called lax transformations, after the displayed functors they
unstraighten to (`Lax` in the names of the categories of (op)fibrations). Their 2-cells
`F f ⋙ app a ⟶ app a' ⋙ G f` go the other way from those of `ICatLax` relative to the morphisms
`f.op` of `Γᵒᵖ`: they are the oplax transformations of the paper's `[Γᵒᵖ, Cat]_oplax`.

The folder mirrors `OverCat/Cat/`, file by file:

* `Extension`: the context extension `Γ ⋉⁻ A`.
* `Basic`: the comprehension functor `compr : ICatOpLax ⟶ cod Cat`, the unstraightening followed by
  forgetting the cleavage and taking total categories, which sends the chosen lifts to pullbacks
  and is fully faithful, so that `ICatOpLax` is a full split comprehension category.
* `Term`: terms `Tm(Γ, A)` from values `γ ↦ A γ` and transports `obj γ ⟶ A f (obj γ')` (`tmMk`);
  the variable `var A` and the diagonal `diag A`; the constant types `constTy Γ K`, whose terms are
  the functors `Γ ⥤ K` (`Tm.constEquiv`), naturally in `Γ`.
* `TypeFormers/Sigma`: Σ-types, whose pairing is the inverse of the counit of
  straightening–unstraightening at the composite.
* `TypeFormers/Op`: opposite types, `A ⋙ opFunctor'`, whose rules hold by `rfl`.
* `TypeFormers/Unit`: unit types, the constant types at `discrete' PUnit`, whose η holds by `rfl`.
* `Small`: at level `v + 1`, the contravariant types of level `v`, the functors
  `Γᵒᵖ ⥤ Cat.{v, v}`, as a full split comprehension category `SmallICatOp`, along their lift into
  the contravariant category model.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory Fibration.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **The contravariant category model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.CatOpModel.splitComprehension :
    SplitComprehension ICatOpLax.{u, u, u, u}

recall ComprehensionCategory.CatOpModel.fullComprehension :
    FullComprehension ICatOpLax.{u, u, u, u}

/-- The chosen lifts go to pullbacks: `A ⋉⁻ ICatOpLax.pull u G` is the pullback of `B ⋉⁻ G` along
`u`. -/
recall ComprehensionCategory.CatOpModel.isCartesianComprClift {A B : Cat.{u, u}}
    (u : A ⟶ B) (G : Bᵒᵖ ⥤ Cat.{u, u}) :
    IsCartesian (CatOpModel.compr.map (ICatOpLax.clift u G))

/-- **The contravariant category model has Σ-types.** -/
recall ComprehensionCategory.CatOpModel.hasSigma : HasSigma ICatOpLax.{u, u, u, u}

/-- **The contravariant category model has unit types.** -/
recall ComprehensionCategory.CatOpModel.hasUnit : HasUnit ICatOpLax.{u, u, u, u}

/-- **The contravariant category model has opposite types**, involutive by `rfl`. -/
recall ComprehensionCategory.CatOpModel.op_op {Γ : Cat.{u, u}} (A : ICatOpLax.{u, u}.Ty Γ) :
    CatOpModel.op (CatOpModel.op A) = A

/-- The terms of the constant type at `K` are the functors `Γ ⥤ K`. -/
recall ComprehensionCategory.CatOpModel.Tm.constEquiv {Γ K : Cat.{u, u}} :
    Tm(Γ, CatOpModel.constTy Γ K) ≃ (Γ ⥤ K)

section Small

universe v

/-- **The contravariant types of level `v`** form a full split comprehension category. -/
recall ComprehensionCategory.CatOpModel.SmallICatOp.fullComprehension :
    FullComprehension CatOpModel.SmallICatOp.{v}

end Small
