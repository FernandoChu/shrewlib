import Rules.Category
import Mathlib.CategoryTheory.Functor.Basic

/-!
# The functor laws as rewrite rules

`F.map (𝟙 x) ↦ 𝟙 (F.obj x)` and `F.map (f ≫ g) ↦ F.map f ≫ F.map g`. These are tried on every
application of `Functor.map`, so they are imported only where they are needed.

The unit laws of functor composition, `𝟭 C ⋙ F ↦ F` and `F ⋙ 𝟭 D ↦ F`, are rules too. They
already hold by unfolding, and as rules they make `𝟭 A ⋙ 𝟭 A` reduce to `𝟭 A` directly, so that the
composite of two displayed functors over `𝟭 A` (vertical functors) lies over `𝟭 A`.
-/

open CategoryTheory

attribute [rewrite_rule] Functor.map_id Functor.map_comp Functor.id_comp Functor.comp_id
