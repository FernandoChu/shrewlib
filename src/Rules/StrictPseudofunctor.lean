import Rules.Category
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# The laws of strict pseudofunctors as rewrite rules

A strict pseudofunctor `F` (a strict 2-functor) preserves identities and composites of 1-cells,
`F.map (𝟙 a) ↦ 𝟙 (F.obj a)` and `F.map (f ≫ g) ↦ F.map f ≫ F.map g`, and identities and composites
of 2-cells. Its comparison isomorphisms are then identities: `F.mapId a ↦ eqToIso _` and
`F.mapComp f g ↦ eqToIso _`, where the equations are between definitionally equal 1-cells.
-/

open CategoryTheory

attribute [rewrite_rule] PrelaxFunctor.map₂_id PrelaxFunctor.map₂_comp
  StrictlyUnitaryPseudofunctor.map_id StrictPseudofunctor.map_comp
  StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso StrictPseudofunctor.mapComp_eq_eqToIso
