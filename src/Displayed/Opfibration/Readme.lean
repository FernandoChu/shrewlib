import Displayed.Opfibration.Basic
import Displayed.Opfibration.DualOp
import Displayed.Opfibration.Straightening.Readme

/-!
# Opfibrations

* `Basic`: opcartesian morphisms (`IsOpcartesian`), cloven opfibrations (`Opfib`), and basic
  definitions involving these.
* `DualOp`: the dual opfibration of a split opfibration.
* `Straightening/`: functors `A ⥤ Cat` and their Grothendieck construction (see its
  `Readme.lean`).

`Fibration/` is the exact dual.
-/

universe v₁ u₁

open CategoryTheory Displayed

open scoped Displayed

/-! ## Main results -/

/-- A vertical equivalence preserves opcartesian morphisms. -/
recall Displayed.VertEquivalence.isOpcartesian_map {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) {a a' : A} {f : a ⟶ a'} {x : D.Ob a}
    {y : D.Ob a'} {φ : x ⟶[f] y} (H : IsOpcartesian φ) : IsOpcartesian (e.functor.map φ)

/-- An opcleavage transfers along a vertical equivalence. -/
recall Displayed.VertEquivalence.opfib {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) [Opfib D] : Opfib E
