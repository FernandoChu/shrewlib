import ComprehensionCategory.Model.OverCat.Cat.Basic
import ComprehensionCategory.Model.OverCat.Cat.Small
import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Unit
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Universe

/-!
# The category model

In this folder we define the category model: the comprehension category `ICatLax` over `Cat`, whose
types in context `Γ` are the functors `Γ ⥤ Cat`, and whose context extension `Γ ▹ A` is the
total category `Γ ⋉ A` of the unstraightening of `A`. It is full and split, and it has Σ-types:
`Σ[A] B` is the straightening of the composite of the split opfibrations `∫ A` over
`Γ` and `∫ B` over `Γ ⋉ A`. It has unit types, the constant types at the terminal category. It
has opposite types: `Aᵒᵖ` is the pointwise opposite of `A`. The terms `Tm(Γ, A)` of a constant
type at a category `K` are the functors `Γ ⥤ K`. At level `v + 1`,
it has a Coquand-style universe `U Γ`, the constant type at the category of small categories,
whose terms are exactly the functors `Γ ⥤ Cat.{v, v}`. Its Hom-types are types of the discrete
model, and it has a universe of the discrete types too (`OverCat/Shared`).

The files give its ingredients:

* `Extension`: the context extension `Γ ⋉ A`.
* `Basic`: the comprehension functor `compr : ICatLax ⟶ cod Cat`, the unstraightening followed by
  forgetting the opcleavage and taking total categories, which sends the chosen lifts to pullbacks
  and is fully faithful, so that `ICatLax` is a full split comprehension category.
* `Term`: terms `Tm(Γ, A)` from values `γ ↦ A γ` and transports (`tmMk`); the variable
  `var A : Tm(Γ ▹ A, A⦃𝐩 A⦄)` and the diagonal `diag A`; the constant types `constTy Γ K`, whose
  terms are the functors `Γ ⥤ K` (`Tm.constEquiv`), naturally in `Γ`; the terms are the sections
  of the unstraightening (`Tm.sectionEquiv`), substitution is their reindexing, and the variable
  substituted along the section of a term is the term (`var_pull_sec`).
* `TypeFormers/Sigma`: Σ-types, whose pairing is the inverse of the counit of
  straightening–unstraightening at the composite.
* `TypeFormers/Op`: opposite types, `A ⋙ opFunctor'`, whose rules hold by `rfl`, with the
  opposite functor `opFunctor' : Cat ⥤ Cat` of `CategoryTheory/Opposite`, involutive on the nose.
* `TypeFormers/Unit`: unit types, the constant types at the terminal category `discrete' PUnit`,
  whose η holds by `rfl`.
* `Small`: at level `v + 1`, the types of level `v`, the functors `Γ ⥤ Cat.{v, v}`, as a full
  split comprehension category `SmallICat`, along their lift into the category model.
* `TypeFormers/Universe`: the universe `U Γ` of the types of level `v`, with inverse maps `El` and
  `code` between its terms and the functors `Γ ⥤ Cat.{v, v}`, stable under substitution:
  `HasUniverse ICatLax SmallICat`, decoding along the lift.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory Opfibration.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **The category model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.CatModel.splitComprehension : SplitComprehension ICatLax.{u, u, u, u}

recall ComprehensionCategory.CatModel.fullComprehension : FullComprehension ICatLax.{u, u, u, u}

/-- The chosen lifts go to pullbacks: `A ⋉ ICatLax.pull u G` is the pullback of `B ⋉ G` along `u`.
-/
recall ComprehensionCategory.CatModel.isCartesianComprClift {A B : Cat.{u, u}}
    (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : IsCartesian (CatModel.compr.map (ICatLax.clift u G))

/-- The comprehension functor is fully faithful: functors `A ⋉ F ⥤ B ⋉ G` over `u` are lax
transformations `LaxTrans F (u ⋙ G)`. -/
recall ComprehensionCategory.CatModel.comprFullyFaithful : CatModel.compr.{u}.FullyFaithful

/-- **The category model has Σ-types.** -/
recall ComprehensionCategory.CatModel.hasSigma : HasSigma ICatLax.{u, u, u, u}

/-- **The category model has unit types.** -/
recall ComprehensionCategory.CatModel.hasUnit : HasUnit ICatLax.{u, u, u, u}

/-- **The category model has opposite types**, involutive by `rfl`. -/
recall ComprehensionCategory.CatModel.op_op {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) :
    CatModel.op (CatModel.op A) = A

/-- The terms of the constant type at `K` are the functors `Γ ⥤ K`. -/
recall ComprehensionCategory.CatModel.Tm.constEquiv {Γ K : Cat.{u, u}} :
    Tm(Γ, CatModel.constTy Γ K) ≃ (Γ ⥤ K)

section Universe

universe v

/-- **The universe is Coquand-style**: its terms are the functors into `Cat.{v, v}`. -/
recall ComprehensionCategory.CatModel.El_code {Γ : Cat.{v + 1, v + 1}} (A : Γ ⥤ Cat.{v, v}) :
    CatModel.El (CatModel.code A) = A

recall ComprehensionCategory.CatModel.code_El {Γ : Cat.{v + 1, v + 1}}
    (t : Tm(Γ, CatModel.U Γ)) : CatModel.code (CatModel.El t) = t

/-- The universe is closed, and `El` commutes with substitution. -/
recall ComprehensionCategory.CatModel.pull_U {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (CatModel.U Γ)⦃σ⦄ = CatModel.U Δ

recall ComprehensionCategory.CatModel.El_pull {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    (t : Tm(Γ, CatModel.U Γ)) :
    CatModel.El (Γ := Δ) t⦃σ⦄ = σ.toFunctor ⋙ CatModel.El t

/-- **The category model has a universe of the types of level `v`**, along their lift. -/
recall ComprehensionCategory.CatModel.hasUniverse :
    HasUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1} CatModel.SmallICat.{v}

/-- The universe and its maps are those of the category model. -/
example {Γ : Cat.{v + 1, v + 1}} :
    univ ICatLax.{v + 1, v + 1, v + 1, v + 1} CatModel.SmallICat.{v} Γ = CatModel.U Γ :=
  rfl

example {Γ : Cat.{v + 1, v + 1}} (t : Tm(Γ, CatModel.U Γ)) :
    El ICatLax.{v + 1, v + 1, v + 1, v + 1} CatModel.SmallICat.{v} t = CatModel.El t :=
  rfl

end Universe
