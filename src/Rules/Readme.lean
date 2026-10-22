import Rules.Category
import Rules.Functor
import Rules.Bicategory
import Rules.Pullback
import Rules.StrictPseudofunctor

/-!
# Rules on Mathlib's lemmas

Rules on Mathlib's lemmas are declared only here, and each file imports only those it needs.

* `Category`: the category laws, `𝟙 x ≫ f ↦ f`, `f ≫ 𝟙 y ↦ f` and right association.
* `Functor`: the functor laws, `F.map (𝟙 x) ↦ 𝟙 (F.obj x)` and `F.map (f ≫ g) ↦ F.map f ≫ F.map g`.
* `Bicategory`: the laws of locally discrete bicategories and strictly unitary lax functors.
* `Pullback`: the laws of pullback cones and chosen pullbacks.
* `StrictPseudofunctor`: the laws of Mathlib's strict pseudofunctors.
-/
