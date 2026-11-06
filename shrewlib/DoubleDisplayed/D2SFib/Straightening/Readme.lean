import DoubleDisplayed.D2SFib.Straightening.Equivalence

/-!
# Straightening for D2SFibs

In this folder we compare two doubly displayed categories:

* `DProf`, the dependent profunctors, doubly displayed over `ICatStr`, the indexed categories and
  strict transformations: over a functor `F : A ⥤ Cat`, the functors
  `(∫ (F ⋙ opFunctor')).Total ⥤ Cat` from the total category of the unstraightening of its
  pointwise opposite, which is the context extension `Γ ▹ Fᵒᵖ` of the category model;
* `D2SFibStr` (`D2SFib/D2SFibStr.lean`), the split D2SFibs, doubly displayed over
  `SplitOpfibStr`, the split opfibrations and opcartesian functors: over `B`, the category
  `D2SFibCat B`.

The unstraightening `unstraighten` and the straightening `straighten` form an equivalence
`straighteningEquiv` between them, lying over the straightening–unstraightening equivalence
`ICatStr ≃ SplitOpfibStr` of split opfibrations. The fibers are in `Cat.{v₃, u₃}`, independently
of the base.

The files give its ingredients:

* `DProf`: the chosen horizontal and vertical morphisms of `(∫ (F ⋙ opFunctor')).Total`, whose
  laws are rules, the functor `totalMap τ` that a strict transformation `τ` induces between these
  categories, and the split fibration `DProf`, whose reindexing along `τ` sends `P'` to
  `totalMap τ ⋙ P'`.
* `Unstraighten`: the dependent 2-sided Grothendieck construction `Unstraightening P` of a
  dependent profunctor `P` over `F`, a split D2SFib over `∫ F`, the map of D2SFibs over
  `τ.unstraighten` of a morphism of dependent profunctors over `τ`, and the functor
  `unstraighten : DProf ⟶ D2SFibStr`.
* `Straighten`: the straightening of a D2SFib `C` over a split opfibration `B`, the functor
  `⟨a, b⟩ ↦ C.Fiber b`, which sends a morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`, as a
  dependent profunctor over the functor of the fibres of `B`, and the functor
  `straighten : D2SFibStr ⟶ DProf`.
* `Equivalence`: the unit `P ≅ straightenObj (Unstraightening P)`, by identity functors, the
  counit `Unstraightening (straightenDProf E) ⟶ E` over the counit of `ICatStr ≃ SplitOpfibStr`,
  by `d2sHomEquiv`, and the equivalence `straighteningEquiv`.

The laws of D2SFibs are rules, so the Grothendieck construction, its `D2SFib` structure and much of
the unit and counit hold by `rfl`. This is a rewrite of a development on Lean and Mathlib
`v4.30.0-rc2` whose laws were stated with `castHom`, `eqToHom` and `HEq` (commit `4b55ea2` of this
repository), at about half its size.
-/

universe v₃ u₃ v₂ u₂ v₁ u₁

open CategoryTheory Displayed

/-! ## Main results -/

/-- **Straightening–unstraightening for D2SFibs**: an equivalence between dependent profunctors over
`ICatStr` and split D2SFibs over `SplitOpfibStr`, lying over the straightening–unstraightening
equivalence `ICatStr ≃ SplitOpfibStr`. -/
recall DoubleDisplayed.D2SFib.Straightening.straighteningEquiv :
    DoubleDisplayed.EquivalenceOver
      Displayed.Opfibration.Straightening.straighteningEquivStr.{v₂, u₂, v₁, u₁}
      DoubleDisplayed.DProf.{v₃, u₃, v₂, u₂, v₁, u₁}
      DoubleDisplayed.D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁}

recall DoubleDisplayed.DProf.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.DProf.{v₃, u₃, v₂, u₂, v₁, u₁}

recall DoubleDisplayed.D2SFibStr.splitDDFib :
    DoubleDisplayed.SplitDDFib DoubleDisplayed.D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁}
