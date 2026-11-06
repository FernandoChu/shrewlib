import Displayed.Discrete.Basic
import Displayed.Discrete.DiscreteCat
import Displayed.Discrete.Sigma
import Displayed.Discrete.Straightening.Readme

/-!
# Discrete opfibrations

* `DiscreteCat`: discrete categories `discrete' S`, whose morphisms are the proofs of equalities,
  and functions between them as functors. It imports no rewrite rules.
* `Basic`: discrete opfibrations (`DiscOpfibOb`), split opfibrations whose fibres are discrete
  categories, and the category `DiscOpfibCat` of them displayed over `Cat`, with a fully faithful
  functor forgetting the discreteness into `SplitOpfibLax`.
* `Sigma`: discrete opfibrations compose, as split opfibrations with discrete fibres.
* `Straightening/`: functors `A ⥤ Cat` into discrete categories and their unstraightenings, an
  equivalence with the discrete opfibrations over `Cat` (see its `Readme.lean`).
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory Displayed

/-! ## Main results -/

/-- The fibres of the composite of displayed categories with discrete fibres are discrete. -/
recall Displayed.isDiscrete_sigmaDisp {A : Type u₁} [Category.{v₁} A] {D : Displayed A}
    {E : Displayed D.Total} [∀ a, IsDiscrete (D.Fiber a)] [∀ p, IsDiscrete (E.Fiber p)] (a : A) :
    IsDiscrete ((D.sigmaDisp E).Fiber a)

/-- Discrete opfibrations compose. -/
recall Displayed.DiscOpfibOb.sigma {A : Cat.{v₁, u₁}} (X : DiscOpfibOb.{v₂, u₂} A)
    (Y : DiscOpfibOb.{v₂, u₂} (Cat.of X.toDisplayed.Total)) : DiscOpfibOb.{v₂, u₂} A
