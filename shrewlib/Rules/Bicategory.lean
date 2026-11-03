import Rules.Category
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Rules for locally discrete bicategories and strictly unitary lax functors

* Composition of 1-cells in `LocallyDiscrete C` computes in `C`, and so do identities.
* A strictly unitary (lax normal) functor sends identities to identities on the nose, and its unit
  is the identity.
* A prelax functor preserves identity 2-cells. The 2-cells of `LocallyDiscrete C` are built by the
  constructor `⟨p⟩` of `Discrete.Hom`; those from a 1-cell to itself are also sent to identities,
  for 2-cells that are not syntactically identities.

Together, a lax normal functor out of `LocallyDiscrete C` sends every 2-cell between definitionally
equal 1-cells to an identity.
-/

open CategoryTheory Bicategory

universe v u

attribute [rewrite_rule] StrictlyUnitaryLaxFunctor.map_id StrictlyUnitaryLaxFunctor.mapId_eq_eqToHom
  PrelaxFunctor.map₂_id Quiver.Hom.id_toLoc

/-- Composition of 1-cells in `LocallyDiscrete C` computes in `C`. -/
@[rewrite_rule]
theorem CategoryTheory.LocallyDiscrete.comp_eq_toLoc {C : Type u} [Category.{v} C]
    {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = (f.as ≫ g.as).toLoc :=
  rfl

/-- A prelax functor sends a 2-cell `⟨p⟩ : f ⟶ f` of `LocallyDiscrete C` to the identity. -/
@[rewrite_rule]
theorem CategoryTheory.PrelaxFunctor.map₂_mk {C : Type*} [Category C] {B : Type*} [Bicategory B]
    (G : PrelaxFunctor (LocallyDiscrete C) B) {a b : LocallyDiscrete C} (f : a ⟶ b)
    (p : f.as = f.as) : G.map₂ (⟨p⟩ : f ⟶ f) = 𝟙 (G.map f) := by
  rw [show (⟨p⟩ : f ⟶ f) = 𝟙 f from rfl]
