import Rules.Category
import Mathlib.CategoryTheory.Functor.Basic

/-!
# The functor laws as rewrite rules

`F.map (𝟙 x) ↦ 𝟙 (F.obj x)` and `F.map (f ≫ g) ↦ F.map f ≫ F.map g`. These are tried on every
application of `Functor.map`, so they are imported only where they are needed.
-/

open CategoryTheory

attribute [rewrite_rule] Functor.map_id Functor.map_comp
