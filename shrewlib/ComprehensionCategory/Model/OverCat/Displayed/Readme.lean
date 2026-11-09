import ComprehensionCategory.Model.OverCat.Displayed.Basic
import ComprehensionCategory.Model.OverCat.Displayed.Term
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Unit

/-!
# The displayed category model

In this folder we define the displayed category model: the comprehension category `LaxNormalCat`
over `Cat`, whose types in context `Γ` are the lax normal functors from `Γ` to profunctors, the
categories displayed over `Γ` in Bénabou's sense. Its comprehension functor is the composite
equivalence `LaxNormalCat ≃ DisplayedCat ≃ cod Cat` over `Cat`, so the context extension `Γ ▹ F` is
the total category of the unstraightening of `F`. It is full and split: a split replacement of the
codomain comprehension category `cod Cat`. It has Σ-types: `Σ[F] G` is the straightening of the
composite of the unstraightenings of `F` and `G`. It has unit types, the straightenings of the
terminal displayed categories.

* `Basic`: the comprehension functor `unstraighten ⋙ᵥ DisplayedCat.total`, which preserves cartesian
  morphisms and is fully faithful, as a composite of equivalences.
* `Term`: terms of the type `straightenObj D` of a displayed category `D`, the sections of `D`
  (`Tm.sectionEquiv`), from objects of `D` and morphisms of `D` between them (`tmMk`); the
  substitution of `straightenObj D` is the straightening of the reindexing of `D`, by `rfl`.
* `TypeFormers/Sigma`: Σ-types, whose pairing reassociates the pairs, since unstraightening undoes
  straightening on the nose.
* `TypeFormers/Unit`: unit types, the straightenings of the terminal displayed categories
  `unitDisp Γ`, whose η holds by `rfl`.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory Straightening

/-! ## Main results -/

/-- **The displayed category model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.DisplayedModel.splitComprehension :
    SplitComprehension LaxNormalCat.{u, u, u}

recall ComprehensionCategory.DisplayedModel.fullComprehension :
    FullComprehension LaxNormalCat.{u, u, u}

/-- Its comprehension functor is the composite equivalence `LaxNormalCat ≃ DisplayedCat ≃ cod Cat`.
-/
recall ComprehensionCategory.DisplayedModel.compr :
    VertFunctor LaxNormalCat.{u, u, u} (cod Cat.{u, u})

/-- **The displayed category model has Σ-types.** -/
recall ComprehensionCategory.DisplayedModel.hasSigma : HasSigma LaxNormalCat.{u, u, u}

/-- **The displayed category model has unit types.** -/
recall ComprehensionCategory.DisplayedModel.hasUnit : HasUnit LaxNormalCat.{u, u, u}
