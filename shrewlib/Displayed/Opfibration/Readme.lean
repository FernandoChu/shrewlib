import Displayed.Opfibration.Basic
import Displayed.Opfibration.OpcartesianFunctor
import Displayed.Opfibration.DualOp
import Displayed.Opfibration.Sigma
import Displayed.Opfibration.SplitOpfibLax
import Displayed.Opfibration.SplitOpfibStr
import Displayed.Opfibration.Straightening.Readme

/-!
# Opfibrations

* `Basic`: opcartesian morphisms (`IsOpcartesian`), displayed functors preserving them
  (`DispFunctor.PreservesOpcartesian`), cloven opfibrations (`Opfib`), and basic definitions
  involving these.
* `DualOp`: the dual opfibration of a split opfibration.
* `OpcartesianFunctor`: displayed functors sending the chosen lifts to the chosen lifts, and the
  functors they induce between the dual opfibrations.
* `Sigma`: opfibrations compose, and so do split opfibrations.
* `SplitOpfibLax` and `SplitOpfibStr`: the split opfibrations, with the displayed functors and with
  the opcartesian functors between them, two categories displayed over `Cat`. The reindexing of a
  split opfibration is a split opfibration, so `SplitOpfibLax` is a split fibration over `Cat`.
* `Straightening/`: functors `A ⥤ Cat` and their unstraightenings, equivalences with the split
  opfibrations over `Cat`, with lax and with strict morphisms (see its `Readme.lean`).

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
recall Displayed.sigmaSplitOpfib {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₂, u₂} A}
    {E : Displayed.{v₃, u₃} D.Total} [SplitOpfib D] [SplitOpfib E] :
    SplitOpfib (D.sigmaDisp E)
