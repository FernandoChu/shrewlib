import Displayed.Straightening.Equivalence

/-!
# Straightening for displayed categories

In this folder we compare two categories displayed over `Cat`:

* `LaxNormalCat`: which has as objects over a category `A`, the lax normal functors from `A` to the
  bicategory of profunctors; a morphism over `u : A ⟶ B` from `F` to `G` is a lax transformation
  from `F` to `G` restricted along `u`, whose components are representable profunctors;
* `DisplayedCat` (`Displayed/Displayed/DisplayedCat.lean`): the displayed categories over `A`, and
  the displayed functors over `u`.

There are two vertical functors over `Cat` between them,
`unstraighten : LaxNormalCat ⟶ DisplayedCat` and `straighten : DisplayedCat ⟶ LaxNormalCat`, and
they are inverse to each other, an isomorphism of categories over `Cat`, which is Bénabou's
correspondence. As an equivalence over `Cat`, it is `straighteningEquiv`. Both functors preserve
cartesian morphisms.
That `DisplayedCat` is in turn equivalent to `cod Cat`, the functors into the base, is
`DisplayedCat.codEquiv` (`Displayed/CodCatEquiv`).

The files give its ingredients:

* `LaxNormalCat`: the domain of the unstraightening functor.
* `Unstraighten`: the functor `unstraighten`, sending `F` to the displayed category of the elements
  of the profunctors `F f`, whose total category is a Grothendieck construction on profunctors.
* `Straighten`: the functor `straighten`, sending `D` to the lax normal functor `a ↦ D.Fiber a`,
  with the profunctors of the morphisms of `D` over each `f`.
* `Equivalence`: the unit and counit, the equivalence `straighteningEquiv`, and the isomorphism.
  The counit is the identity: `unstraightenObj (straightenObj D)` is `D` by `rfl`. The unit is the
  identity propositionally: `straightenObj (unstraightenObj F) = F`.
-/

universe u

open CategoryTheory Displayed Displayed.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening** is an equivalence over `Cat`. -/
recall Displayed.Straightening.straighteningEquiv :
    VertEquivalence LaxNormalCat.{u} DisplayedCat.{u}

/-- **Straightening–unstraightening is an isomorphism of categories over `Cat`**: the two vertical
functors are inverse to each other, on the nose in one direction and propositionally in the
other. -/
recall Displayed.Straightening.straighten_comp_unstraighten :
    straighten ⋙ᵥ unstraighten = VertFunctor.id DisplayedCat.{u}

recall Displayed.Straightening.unstraighten_comp_straighten :
    unstraighten ⋙ᵥ straighten = VertFunctor.id LaxNormalCat.{u}

/-- On objects. -/
recall Displayed.Straightening.unstraightenObj_straightenObj {A : Cat.{u, u}}
    (D : Displayed.{u, u, u, u} A) : unstraightenObj (straightenObj D) = D

recall Displayed.Straightening.straightenObj_unstraightenObj {A : Cat.{u, u}} (F : LaxNormal A) :
    straightenObj (unstraightenObj F) = F

/-- `LaxNormalCat` and `DisplayedCat` are split fibrations over `Cat`, by restriction. -/
recall Displayed.Straightening.splitFibLaxNormalCat : SplitFib LaxNormalCat.{u}

recall Displayed.DisplayedCat.splitFib : SplitFib DisplayedCat.{u}

/-- Both functors are cartesian functors: they preserve the chosen cartesian lifts strictly. -/
recall Displayed.Straightening.unstraightenCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) LaxNormalCat.{u} DisplayedCat.{u}

recall Displayed.Straightening.straightenCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) DisplayedCat.{u} LaxNormalCat.{u}

/-- Both functors preserve cartesian morphisms. -/
recall Displayed.Straightening.isCartesianUnstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B}
    {F : LaxNormal A} {G : LaxNormal B} {φ : LaxNormalCat.Hom u F G} (H : IsCartesian φ) :
    IsCartesian (unstraighten.map φ)

recall Displayed.Straightening.isCartesianStraightenMap {A B : Cat.{u, u}} {u : A ⟶ B}
    {X : DisplayedCat.{u}.Ob A} {Y : DisplayedCat.{u}.Ob B} {w : DisplayedCat.Hom u X Y}
    (H : IsCartesian w) : IsCartesian (straighten.map w)
