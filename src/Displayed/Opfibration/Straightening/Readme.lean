import Displayed.Opfibration.Straightening.Unstraighten

/-!
# Straightening for opfibrations

In this folder we compare two categories displayed over `Cat`:

* `ICat`: which has as objects over a category `A` the functors `A ⥤ Cat`; a morphism over
  `u : A ⟶ B` is a lax transformation `F ⇒ u ⋙ G`;
* `cod Cat`, the arrow category `Cat^→` equipped with its codomain functor.

There is a vertical functor `unstraighten : ICat ⟶ cod Cat`, sending `F` to the projection
`A ⋉ F ⥤ A` of its Grothendieck construction. It is fully faithful, and it sends the chosen
cartesian lifts of `ICat` to pullbacks. There is no equivalence yet: the image of `unstraighten`
is the split opfibrations, with arbitrary functors over the base as morphisms.

The files give its ingredients:

* `ICat`: lax transformations between functors into `Cat`, and the split fibration `ICat`, whose
  reindexing along `u` sends `G` to `u ⋙ G`.
* `Unstraighten`: the functor `unstraighten`, through Mathlib's Grothendieck construction.
-/

universe u

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-! ## Main results -/

recall Displayed.Opfibration.Straightening.ICat.splitFib : SplitFib ICat.{u}

/-- The chosen lifts go to pullbacks: `A ⋉ u^* G` is the pullback of `B ⋉ G` along `u`. -/
recall Displayed.Opfibration.Straightening.isCartesian_unstraighten_clift {A B : Cat.{u, u}}
    (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : IsCartesian (unstraighten.map (ICat.clift u G))

/-- The unstraightening is fully faithful: functors `A ⋉ F ⥤ B ⋉ G` over `u` are lax
transformations `F ⇒ u ⋙ G`. -/
recall Displayed.Opfibration.Straightening.unstraighten_map_bijective {A B : Cat.{u, u}}
    (u : A ⟶ B) (F : A ⥤ Cat.{u, u}) (G : B ⥤ Cat.{u, u}) :
    Function.Bijective (unstraighten.map : ICat.Hom u F G → _)
