import Displayed.Opfibration.Basic
import Displayed.Opfibration.DualOp
import Displayed.Opfibration.Sigma
import Displayed.Opfibration.SplitOpfibCat
import Displayed.Opfibration.Straightening.Readme

/-!
# Opfibrations

* `Basic`: opcartesian morphisms (`IsOpcartesian`), displayed functors preserving them
  (`DispFunctor.PreservesOpcartesian`), cloven opfibrations (`Opfib`), and basic definitions
  involving these.
* `DualOp`: the dual opfibration of a split opfibration.
* `Sigma`: opfibrations compose, and so do split opfibrations.
* `SplitOpfibCat`: the split opfibrations and displayed functors between them, a category displayed
  over `Cat`.
* `Straightening/`: functors `A ⥤ Cat` and their unstraightenings, an equivalence with the split
  opfibrations over `Cat` (see its `Readme.lean`).

`Fibration/` is the exact dual.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

open scoped Displayed

/-! ## Main results -/

/-- A vertical equivalence preserves opcartesian morphisms. -/
recall Displayed.VertEquivalence.isOpcartesianMap {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) : e.functor.PreservesOpcartesian

/-- An opcleavage transfers along a vertical equivalence. -/
recall Displayed.VertEquivalence.opfib {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) [Opfib D] : Opfib E

/-- Split opfibrations compose: for `D` over `A` and `E` over `D.Total`, the composite is a split
opfibration over `A`. -/
recall Displayed.sigmaSplitOpfib {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
    {E : Displayed.{max v₁ v₂, max u₁ u₂, v₃, u₃} D.Total} [SplitOpfib D] [SplitOpfib E] :
    SplitOpfib (D.sigmaDisp E)
