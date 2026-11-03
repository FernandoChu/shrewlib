import DoubleDisplayed.D2SFib.Straightening.Str.Equivalence

/-!
# Straightening for D2SFibs

In this folder we compare two doubly displayed categories:

* `DProf`, the dependent profunctors, doubly displayed over `ICatStr`, the indexed categories and
  strict transformations: over a functor `F : A ⥤ Cat`, the functors `(∫ F)ᵒᵖ.Total ⥤ Cat` from
  the total category of the dual of its unstraightening (`DoubleDisplayed/D2SFib/DProf.lean`);
* `D2SFibStr`, the split D2SFibs, doubly displayed over `SplitOpfibStr`, the split opfibrations
  and opcartesian functors: over `B`, the category `D2SFibCat B`.

The unstraightening `unstraighten` and the straightening `straighten` form an equivalence
`straighteningEquiv` between them, lying over the straightening–unstraightening equivalence
`ICatStr ≃ SplitOpfibStr` of split opfibrations. The fibers are in `Cat.{v₃, u₃}`, independently
of the base.

The files give its ingredients, first for a single split opfibration `B`:

* `Unstraighten`: the dependent 2-sided Grothendieck construction `Unstraightening F` of a functor
  `F : Bᵒᵖ.Total ⥤ Cat`, and its D2SFib structure.
* `Straighten`: the straightening of a D2SFib `C`, the functor `⟨a, b⟩ ↦ C.Fiber b`, which sends a
  morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`.
* `Unit`: the isomorphism `F ≅ straightenObj (Unstraightening F)`, by identity functors.
* `Counit`: the isomorphism `unstraightenObj (straightenObj C) ≅ C`, by `d2sHomEquiv`.

and then over all of them:

* `Str/Unstraighten`: the unstraightening of the morphisms of dependent profunctors over an
  opcartesian functor `H`, and the doubly displayed functor `unstraighten : DProf ⟶ D2SFibStr`
  over `unstraightenStr : ICatStr ⟶ SplitOpfibStr`.
* `Str/Straighten`: the doubly displayed functor `straighten : D2SFibStr ⟶ DProf` over
  `straightenStr : SplitOpfibStr ⟶ ICatStr`.
* `Str/Equivalence`: the unit and counit, with the components of `Unit` and `Counit`, and the
  equivalence `straighteningEquiv`.

The laws of D2SFibs are rules, so the Grothendieck construction, its `D2SFib` structure and much of
the unit and counit hold by `rfl`. This is a rewrite of a development on Lean and Mathlib
`v4.30.0-rc2` whose laws were stated with `castHom`, `eqToHom` and `HEq` (commit `4b55ea2` of this
repository), at about half its size.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u

open CategoryTheory Displayed

/-! ## Main results -/

/-- **Straightening–unstraightening for D2SFibs**: an equivalence between dependent profunctors over
`ICatStr` and split D2SFibs over `SplitOpfibStr`, lying over the straightening–unstraightening
equivalence `ICatStr ≃ SplitOpfibStr`. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquiv :
    DoubleDisplayed.EquivalenceOver
      Displayed.Opfibration.Straightening.straighteningEquivStr.{u}
      DoubleDisplayed.DProf.{u, v₃, u₃} DoubleDisplayed.D2SFibStr.{u, u, u, u, v₃, u₃}

recall DoubleDisplayed.DProf.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.DProf.{u, v₃, u₃}

recall DoubleDisplayed.D2SFibStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}
