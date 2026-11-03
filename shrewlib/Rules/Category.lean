import Mathlib.CategoryTheory.Category.Basic

/-!
# The category laws as rewrite rules

`𝟙 x ≫ f ↦ f`, `f ≫ 𝟙 y ↦ f` and `(f ≫ g) ≫ h ↦ f ≫ (g ≫ h)`: composites are normalized to be
right-associated, without identities. Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory

attribute [rewrite_rule] Category.id_comp Category.comp_id Category.assoc
