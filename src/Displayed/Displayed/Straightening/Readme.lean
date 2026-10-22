import Displayed.Displayed.Straightening.Equivalence

/-!
# Straightening for displayed categories

In this folder we compare two categories displayed over `Cat`:

* `DCat`: which has as objects over a category `A`, the lax normal functors from `A` to the
  bicategory of profunctors; a morphism over `u : A ⟶ B` is a lax transformation `F ⇒ G ∘ u` whose
  components are representable profunctors;
* `cod Cat`, the arrow category `Cat^→` equipped its codomain functor.

There are two vertical functors over `Cat` between them, `unstraighten : DCat ⟶ cod Cat` and
`straighten : cod Cat ⟶ DCat`, and they form an equivalence over `Cat`, `straighteningEquiv`.
Both functors preserve cartesian morphisms.

The files give its ingredients:

* `DCat`: the domain of the unstraightening functor.
* `Unstraighten`: the functor `unstraighten`, which acts as a sort of Grothendieck construction
  on profunctors.
* `Straighten`: the functor `straighten`, sending `p : E ⥤ A` to the lax normal functor from `A` to
  `Prof` that sends `a : A` to the fibre of `p` over `a`.
* `Equivalence`: the unit and counit, and the equivalence `straighteningEquiv`.
-/

universe u

open CategoryTheory Displayed Displayed.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening** is an equivalence over `Cat`. -/
recall Displayed.Straightening.straighteningEquiv : VertEquivalence DCat.{u} (cod Cat.{u, u})

recall Displayed.Straightening.splitFibDCat : SplitFib DCat.{u}

/-- `cod Cat` is a fibration, by transfer along the equivalence. -/
recall Displayed.Straightening.fibCodCat : Fib (cod Cat.{u, u})

/-- Both functors preserve cartesian morphisms. -/
recall Displayed.Straightening.isCartesian_unstraighten_map {A B : Cat.{u, u}} {u : A ⟶ B}
    {F : LaxNormal A} {G : LaxNormal B} {φ : DCat.Hom u F G} (H : IsCartesian φ) :
    IsCartesian (unstraighten.map φ)

recall Displayed.Straightening.isCartesian_straighten_map {A B : Cat.{u, u}} {u : A ⟶ B}
    {X : (cod Cat.{u, u}).Ob A} {Y : (cod Cat.{u, u}).Ob B} {w : (cod Cat.{u, u}).Hom u X Y}
    (H : IsCartesian w) : IsCartesian (straighten.map w)
