import DoubleDisplayed.D2SFib.Straightening.Equivalence

/-!
# Straightening for D2SFibs

In this folder we compare two categories, for a split opfibration `B` over `A`:

* the functors `Bᵒᵖ.Total ⥤ Cat` from the total category of the dual opfibration of `B`;
* `D2SFibCat B`, the split D2SFibs over `B`.

There are two functors between them, `unstraighten : (Bᵒᵖ.Total ⥤ Cat) ⥤ D2SFibCat B` and
`straighten` the other way, and they form an equivalence, `straighteningEquiv`.

The files give its ingredients:

* `Straighten`: the functor `straighten`, sending a D2SFib `C` to the functor
  `⟨a, b⟩ ↦ C.Fiber b`, which sends a morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`.
* `Unstraighten`: the functor `unstraighten`, through `Unstraightening F`, the dependent 2-sided
  Grothendieck construction.
* `Counit`: the counit `straighten ⋙ unstraighten ≅ 𝟭`.
* `Equivalence`: the unit `𝟭 ≅ unstraighten ⋙ straighten`, and the equivalence `straighteningEquiv`.

The laws of D2SFibs are rules, so the Grothendieck construction, its `D2SFib` structure and much of
the unit and counit hold by `rfl`. This is a rewrite of a development on Lean and Mathlib
`v4.30.0-rc2` whose laws were stated with `castHom`, `eqToHom` and `HEq` (commit `4b55ea2` of this
repository), at about half its size.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory Displayed

/-! ## Main results -/

/-- **Straightening–unstraightening for D2SFibs.** -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquiv {A : Type u₁} [Category.{v₁} A]
    (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    Bᵒᵖ.Total ⥤ Cat ≌ DoubleDisplayed.D2SFibCat B
