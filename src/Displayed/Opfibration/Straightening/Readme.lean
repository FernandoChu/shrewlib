import Displayed.Opfibration.Straightening.Equivalence

/-!
# Straightening for opfibrations

In this folder we compare two categories displayed over `Cat`:

* `ICat`: which has as objects over a category `A` the functors `A ⥤ Cat`; a morphism over
  `u : A ⟶ B` is a lax transformation `F ⇒ u ⋙ G`;
* `SplitOpfibCat`, the subcategory of the arrow category `Cat^→` (equipped with its codomain
  functor) spanned by the split opfibrations: an object over `A` is a functor `p : E ⥤ A` with a
  split opcleavage, and a morphism over `u` is any functor `w` with `w ⋙ p' = p ⋙ u`.

The vertical functor `unstraighten : ICat ⟶ cod Cat`, sending `F` to the projection
`A ⋉ F ⥤ A` of its Grothendieck construction, lands in `SplitOpfibCat`, and induces an
equivalence over `Cat`, `straighteningEquiv`. It also sends the chosen cartesian lifts of `ICat`
to pullbacks.

The files give its ingredients:

* `ICat`: lax transformations between functors into `Cat`, and the split fibration `ICat`, whose
  reindexing along `u` sends `G` to `u ⋙ G`.
* `Unstraighten`: the functor `unstraighten`, through Mathlib's Grothendieck construction, and the
  inverse of its action on morphisms.
* `SplitOpfibCat`: the split opfibrations, and the unstraightening into them.
* `Straighten`: the straightening of a split opfibration `p : E ⥤ A`, the functor `A ⥤ Cat` of
  its fibres.
* `Equivalence`: the counit, and the equivalence `straighteningEquiv`.
-/

universe u

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening for split opfibrations** is an equivalence over `Cat`. -/
recall Displayed.Opfibration.Straightening.straighteningEquiv :
    VertEquivalence ICat.{u} SplitOpfibCat.{u}

recall Displayed.Opfibration.Straightening.ICat.splitFib : SplitFib ICat.{u}

/-- The projection `π : A ⋉ F ⥤ A` is a split opfibration. -/
recall Displayed.Opfibration.Straightening.Groth.splitOpfib {A : Cat.{u, u}}
    (F : A ⥤ Cat.{u, u}) : SplitOpfib (Displayed.Straightening.fibres (unstraightenObj F))

/-- The chosen lifts go to pullbacks: `A ⋉ u^* G` is the pullback of `B ⋉ G` along `u`. -/
recall Displayed.Opfibration.Straightening.isCartesianUnstraightenClift {A B : Cat.{u, u}}
    (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : IsCartesian (unstraighten.map (ICat.clift u G))

/-- The unstraightening is fully faithful: functors `A ⋉ F ⥤ B ⋉ G` over `u` are lax
transformations `F ⇒ u ⋙ G`. -/
recall Displayed.Opfibration.Straightening.unstraightenFullyFaithful :
    unstraighten.{u}.FullyFaithful
