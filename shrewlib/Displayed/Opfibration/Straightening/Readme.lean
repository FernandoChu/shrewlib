import Displayed.Opfibration.Straightening.Equivalence

/-!
# Straightening for opfibrations

In this folder we compare two categories displayed over `Cat`:

* `ICat`: which has as objects over a category `A` the functors `A ⥤ Cat`; a morphism over
  `u : A ⟶ B` is a lax transformation `LaxTrans F (u ⋙ G)`;
* `SplitOpfibCat` (`Opfibration/SplitOpfibCat.lean`): an object over `A` is a displayed category
  over `A` with a split opcleavage, and a morphism over `u` is any displayed functor over `u`, not
  necessarily preserving the chosen lifts.

The vertical functor `unstraighten : ICat ⟶ SplitOpfibCat` sends `F` to the displayed category
`∫ F` whose fibre over `a` is `F a`, with morphisms `x ⟶[f] y` the morphisms
`F f x ⟶ y`, pushing forward along `F`. It is an equivalence over `Cat`, `straighteningEquiv`.

The files give its ingredients:

* `ICat`: lax transformations between functors into `Cat`, and the split fibration `ICat`, whose
  reindexing along `u` sends `G` to `u ⋙ G`.
* `Unstraighten`: the functor `unstraighten`, and the inverse of its action on morphisms. Transport
  in `∫ F` along `f` is `F f`, as a rule (`unstraightenPushMap`).
* `Straighten`: the straightening of a split opfibration `D`, the functor `A ⥤ Cat` of its fibres.
* `Equivalence`: the counit, and the equivalence `straighteningEquiv`.
-/

universe v₁ u₁ v u

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening for split opfibrations** is an equivalence over `Cat`. -/
recall Displayed.Opfibration.Straightening.straighteningEquiv :
    VertEquivalence ICat.{u} SplitOpfibCat.{u}

recall Displayed.Opfibration.Straightening.ICat.splitFib : SplitFib ICat.{u}

/-- The unstraightening `∫ F` of `F : A ⥤ Cat` is a split opfibration. -/
recall Displayed.Opfibration.Straightening.unstraightenSplitOpfib {A : Type u₁}
    [Category.{v₁} A] (F : A ⥤ Cat.{v, u}) : SplitOpfib (∫ F)

/-- The unstraightening is fully faithful: displayed functors from `∫ F` to
`∫ G` over `u` are lax transformations `LaxTrans F (u ⋙ G)`. -/
recall Displayed.Opfibration.Straightening.unstraightenFullyFaithful :
    unstraighten.{u}.FullyFaithful
