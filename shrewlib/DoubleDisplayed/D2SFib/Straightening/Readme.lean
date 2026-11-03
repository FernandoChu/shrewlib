import DoubleDisplayed.D2SFib.Straightening.Equivalence
import DoubleDisplayed.D2SFib.Straightening.Str.ICatStr

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

The folder `Str/` extends the equivalence to the maps over arbitrary opcartesian functors, as an
equivalence `straighteningEquivStr : DProfStr ≃ D2SFibStr` over `SplitOpfibStr` whose functors are
cartesian, and whose functors over a single `B` are those of `straighteningEquiv B`:

* `Str/Unstraighten` and `Str/Straighten`: the actions of `unstraightenStr` and `straightenStr` on
  the maps over an opcartesian functor `H`, whose components are those of the maps.
* `Str/Equivalence`: the unit and counit, with the components of `straighteningEquiv`, the
  equivalence `straighteningEquivStr`, and its cartesian functors.
* `Str/ICatStr`: its reindexing along the unstraightening `ICatStr ⟶ SplitOpfibStr`, an equivalence
  `DProf ≃ D2SFibICatStr` of fibred categories over `ICatStr`, the indexed categories and strict
  transformations.

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

/-- **Straightening–unstraightening for D2SFibs over `SplitOpfibStr`**, an equivalence of fibred
categories. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquivStr :
    DoubleDisplayed.VertEquivalence DoubleDisplayed.DProfStr.{u₁} DoubleDisplayed.D2SFibStr.{u₁}

recall DoubleDisplayed.DProfStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.DProfStr.{u₁}

recall DoubleDisplayed.D2SFibStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibStr.{u₁}

recall DoubleDisplayed.D2SFib.Straightening.unstraightenStrCartesian :
    DoubleDisplayed.DDCartesianFunctor DoubleDisplayed.DProfStr.{u₁} DoubleDisplayed.D2SFibStr.{u₁}

recall DoubleDisplayed.D2SFib.Straightening.straightenStrCartesian :
    DoubleDisplayed.DDCartesianFunctor DoubleDisplayed.D2SFibStr.{u₁} DoubleDisplayed.DProfStr.{u₁}

/-- **Straightening–unstraightening for D2SFibs over `ICatStr`**, an equivalence of fibred
categories between dependent profunctors and D2SFibs over the unstraightenings of functors
`A ⥤ Cat`. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquivICatStr :
    DoubleDisplayed.VertEquivalence DoubleDisplayed.DProf.{u₁} DoubleDisplayed.D2SFibICatStr.{u₁}

/-- `DProf` and `D2SFibICatStr` are split fibrations over `ICatStr`, as reindexings. -/
example : DoubleDisplayed.SplitDDFib DoubleDisplayed.DProf.{u₁} := inferInstance

example : DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibICatStr.{u₁} := inferInstance
