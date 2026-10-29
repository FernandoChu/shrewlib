import Displayed.Fibration.Basic
import Displayed.Fibration.Codomain
import Displayed.Fibration.DisplayedCat
import Displayed.Fibration.DualFib
import Displayed.Fibration.Sigma
import Displayed.Fibration.SplitFibCat
import Displayed.Fibration.Straightening.Readme

/-!
# Fibrations

The exact dual of `Opfibration/`, whose `Readme.lean` explains the design.

* `Basic`: cartesian morphisms (`IsCartesian`), and cloven fibrations (`Fib`), with chosen
  `pull f y` and `clift f y : pull f y ⟶[f] y`, the cartesian factorization, the transport
  `pullMap` and its functors, and split versions (`PreSplitFib`, `SplitFib`). Cleavages transfer
  along equivalences over the base.
* `Codomain`: the cartesian morphisms of the codomain displayed category `cod C` are the pullback
  squares, so `cod C` is a fibration if `C` has chosen pullbacks.
* `DisplayedCat`: taking total categories sends reindexings of displayed categories to pullbacks.
* `DualFib`: the dual fibration of a split fibration.
* `Sigma`: fibrations compose, and so do split fibrations.
* `SplitFibCat`: the split fibrations and displayed functors between them, a category displayed
  over `Cat`.
* `Straightening/`: functors `Aᵒᵖ ⥤ Cat` and their unstraightenings, an equivalence with the split
  fibrations over `Cat` (see its `Readme.lean`).
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v u

open CategoryTheory Limits Displayed

open scoped Displayed

/-! ## Main results -/

/-- A vertical equivalence preserves cartesian morphisms. -/
recall Displayed.VertEquivalence.isCartesianMap {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) {a a' : A} {f : a ⟶ a'} {x : D.Ob a}
    {y : D.Ob a'} {φ : x ⟶[f] y} (H : IsCartesian φ) : IsCartesian (e.functor.map φ)

/-- A cleavage transfers along a vertical equivalence. -/
recall Displayed.VertEquivalence.fib {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) [Fib D] : Fib E

/-- Split fibrations compose: for `D` over `A` and `E` over `D.Total`, the composite is a split
fibration over `A`. -/
recall Displayed.sigmaSplitFib {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
    {E : Displayed.{max v₁ v₂, max u₁ u₂, v₃, u₃} D.Total} [SplitFib D] [SplitFib E] :
    SplitFib (D.sigmaDisp E)

/-- The cartesian morphisms of `cod C` are the pullback squares. -/
recall Displayed.cod.isLimitOfIsCartesian {C : Type u} [Category.{v} C] {a a' : C}
    {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} {φ : x ⟶[f] y} (H : IsCartesian φ) :
    IsLimit (cod.cone φ)

recall Displayed.cod.isCartesianOfIsLimit {C : Type u} [Category.{v} C] {a a' : C}
    {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} {φ : x ⟶[f] y}
    (P : IsLimit (cod.cone φ)) : IsCartesian φ

/-- With chosen pullbacks, `cod C` is a fibration. -/
recall Displayed.cod.fib {C : Type u} [Category.{v} C] [ChosenPullbacks C] : Fib (cod C)
