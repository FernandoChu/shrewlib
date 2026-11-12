import TwoCategory.Basic
import TwoCategory.StrictPseudofunctor
import TwoCategory.Adjunction
import TwoCategory.Constructions.Readme
import TwoCategory.Limits.Readme
import TwoCategory.Monad.Readme
import TwoCategory.Factorization.Readme

/-!
# 2-categories

Strict bicategories, whose laws are rules and hold by `rfl`. Each folder has a `Readme.lean`.

* `Basic`: `TwoCategory`, a bicategory with Mathlib's `Bicategory.Strict`, whose laws are rules:
  composition of 1-cells is right-associated without identities, unitors and associators are
  `Iso.refl`, and whiskering is functorial, unital and associative, so the coherence laws hold by
  `rfl`. (Rules can't be stated for `[Bicategory B] [Bicategory.Strict B]`, since the `Strict`
  instance would not occur in their left-hand sides.) `Cat` is a 2-category (`Cat.twoCategory`).
* `StrictPseudofunctor`: the whiskered forms of the laws of strict pseudofunctors, as rules.
* `Adjunction`: adjunctions in a 2-category, whose triangle laws lose their unitors and
  associators; an adjunction is determined by its counit.
* `Constructions/`: the arrow 2-category `Arr B`, the strict slice `Slice b`, and spans.
* `Limits/`: 2-pullbacks, comma objects and finitely complete 2-categories.
* `Monad/`: monads in a bicategory, strict 2-monads with their 2-categories of algebras,
  pseudo-algebras, lax idempotent 2-monads, whose pseudo-, normal pseudo- and strict algebras are
  left adjoints of the units, colax idempotent 2-comonads, whose strict coalgebras are right
  adjoints of the counits, and distributive laws of a 2-comonad over a 2-monad.
* `Factorization/`: AWFSs, with their chosen diagonal fillers, functorial in coalgebras and
  algebras, and in `Comma/` the comma factorization `f = Lf ≫ Rf` through `f/B`, an AWFS whose
  2-monad `R` is lax idempotent and whose 2-comonad `L` is colax idempotent, with coalgebras the
  left adjoint right inverses; on `Cat`, through comma categories.
-/

universe v u

open CategoryTheory Bicategory

/-! ## Main results -/

/-- `Cat` is a 2-category. -/
example : TwoCategory Cat.{v, u} :=
  inferInstance

/-- The coherence laws of a 2-category hold by `rfl`, checked in the kernel. -/
example {B : Type u} [TwoCategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (i : d ⟶ e) :
    (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom =
      (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom := by
  kernel_rfl
