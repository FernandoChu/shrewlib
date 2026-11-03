import DoubleDisplayed.D2SFib.Straightening.Str.ICatStr

/-!
# Straightening for D2SFibs

In this folder we compare two categories doubly displayed over `SplitOpfibStr`, the split
opfibrations and opcartesian functors:

* `DProfStr`, the dependent profunctors: over a split opfibration `B`, the functors
  `Bᵒᵖ.Total ⥤ Cat` from the total category of its dual opfibration;
* `D2SFibStr`, the split D2SFibs: over `B`, the category `D2SFibCat B`.

The unstraightening `unstraightenStr` and the straightening `straightenStr` form an equivalence
`straighteningEquivStr : DProfStr ≃ D2SFibStr` over `SplitOpfibStr`, whose functors are cartesian,
so an equivalence of fibred categories. Its universes are independent: the base in
`Cat.{v₁, u₁}`, the split opfibrations in `Displayed.{v₁, u₁, v₂, u₂}`, and the fibers in
`Cat.{v₃, u₃}`. Over a single `B`, it is an equivalence `(Bᵒᵖ.Total ⥤ Cat) ≌ D2SFibCat B`.

The files give its ingredients, first for a single `B`:

* `Unstraighten`: the dependent 2-sided Grothendieck construction `Unstraightening F` of a functor
  `F : Bᵒᵖ.Total ⥤ Cat`, and its D2SFib structure.
* `Straighten`: the straightening of a D2SFib `C`, the functor `⟨a, b⟩ ↦ C.Fiber b`, which sends a
  morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`.
* `Unit`: the isomorphism `F ≅ straightenObj (Unstraightening F)`, by identity functors.
* `Counit`: the isomorphism `unstraightenObj (straightenObj C) ≅ C`, by `d2sHomEquiv`.

and then over `SplitOpfibStr`:

* `Str/Unstraighten` and `Str/Straighten`: the actions of `unstraightenStr` and `straightenStr` on
  the maps over an opcartesian functor `H`, whose components are those of the maps.
* `Str/Equivalence`: the unit and counit, with the components of `Unit` and `Counit`, the
  equivalence `straighteningEquivStr`, and its cartesian functors.
* `Str/ICatStr`: its reindexing along the unstraightening `ICatStr ⟶ SplitOpfibStr`, an equivalence
  `DProf ≃ D2SFibICatStr` of fibred categories over `ICatStr`, the indexed categories and strict
  transformations.

The laws of D2SFibs are rules, so the Grothendieck construction, its `D2SFib` structure and much of
the unit and counit hold by `rfl`. This is a rewrite of a development on Lean and Mathlib
`v4.30.0-rc2` whose laws were stated with `castHom`, `eqToHom` and `HEq` (commit `4b55ea2` of this
repository), at about half its size.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u

open CategoryTheory Displayed

/-! ## Main results -/

/-- **Straightening–unstraightening for D2SFibs over `SplitOpfibStr`**, an equivalence of fibred
categories. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquivStr :
    DoubleDisplayed.VertEquivalence DoubleDisplayed.DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}
      DoubleDisplayed.D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}

recall DoubleDisplayed.DProfStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}

recall DoubleDisplayed.D2SFibStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}

recall DoubleDisplayed.D2SFib.Straightening.unstraightenStrCartesian :
    DoubleDisplayed.DDCartesianFunctor DoubleDisplayed.DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}
      DoubleDisplayed.D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}

recall DoubleDisplayed.D2SFib.Straightening.straightenStrCartesian :
    DoubleDisplayed.DDCartesianFunctor DoubleDisplayed.D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}
      DoubleDisplayed.DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}

/-- **Straightening–unstraightening for D2SFibs over `ICatStr`**, an equivalence of fibred
categories between dependent profunctors and D2SFibs over the unstraightenings of functors
`A ⥤ Cat`. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquivICatStr :
    DoubleDisplayed.VertEquivalence DoubleDisplayed.DProf.{u, v₃, u₃}
      DoubleDisplayed.D2SFibICatStr.{u, v₃, u₃}

/-- `DProf` and `D2SFibICatStr` are split fibrations over `ICatStr`, as reindexings. -/
example : DoubleDisplayed.SplitDDFib DoubleDisplayed.DProf.{u, v₃, u₃} := inferInstance

example : DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibICatStr.{u, v₃, u₃} := inferInstance
