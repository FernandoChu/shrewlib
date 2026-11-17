import Displayed.Discrete.Straightening.Equivalence

/-!
# Straightening for discrete opfibrations

In this folder we compare two categories displayed over `Cat`:

* `IDisc`: which has as objects over a category `A` the functors `A ⥤ Cat` into discrete
  categories; a morphism over `u : A ⟶ B` is a lax transformation `LaxTrans F (u ⋙ G)`, as in
  `ICatLax`, of which it is the full subcategory;
* `DiscOpfibCat` (`Discrete/Basic.lean`): an object over `A` is a discrete opfibration over `A`, a
  split opfibration whose fibres are discrete categories, and a morphism over `u` is any displayed
  functor over `u`.

The vertical functor `unstraighten : IDisc ⟶ DiscOpfibCat` sends `F` to the displayed category
`∫ F`, whose fibre over `a` is `F a`, with morphisms `x ⟶[f] y` the morphisms `F f x ⟶ y`. It is
an equivalence over `Cat`, `straighteningEquiv`. All of it is straightening–unstraightening for
split opfibrations (`Opfibration/Straightening`), restricted to the full subcategories of the
discrete ones on both sides.

The files give its ingredients:

* `IDisc`: the split fibration `IDisc`, with the reindexing and the lifts of `ICatLax`, and the
  fully faithful cartesian functor `IDisc.forget : IDisc ⟶ ICatLax`. Natural transformations
  and isomorphisms between functors into discrete categories are vertical morphisms and
  isomorphisms of `IDisc` (`IDisc.homOfNatTrans`, `IDisc.isoOfNatIso`), compatibly with reindexing.
* `Unstraighten`: the unstraightening of a functor into discrete categories has discrete fibres;
  the functor `unstraighten`, which is `IDisc.forget` followed by the unstraightening of the split
  opfibrations, and is fully faithful.
* `Straighten`: the straightening `straighten`, sending a discrete opfibration `X` to the functor of
  its fibres, and a displayed functor to its straightening as one between split opfibrations.
* `Equivalence`: the unit, which is the identity, the counit, and the equivalence
  `straighteningEquiv`.
-/

universe v₂ u₂ v₁ u₁

open CategoryTheory Displayed Displayed.Discrete.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening for discrete opfibrations** is an equivalence over `Cat`. -/
recall Displayed.Discrete.Straightening.straighteningEquiv :
    VertEquivalence IDisc.{v₂, u₂, v₁, u₁} DiscOpfibCat.{v₂, u₂, v₁, u₁}

/-- Straightening undoes unstraightening on the nose. -/
recall Displayed.Discrete.Straightening.straightenObj_unstraightenObj {A : Cat.{v₁, u₁}}
    (X : IDiscOb A) : straightenObj (unstraightenObj X) = X

/-- The unstraightening is fully faithful. -/
recall Displayed.Discrete.Straightening.unstraightenFullyFaithful :
    unstraighten.{v₂, u₂, v₁, u₁}.FullyFaithful

recall Displayed.Discrete.Straightening.IDisc.splitFib : SplitFib IDisc.{v₂, u₂, v₁, u₁}

/-- Forgetting the discreteness of the functors into discrete categories is a fully faithful
cartesian functor. -/
recall Displayed.Discrete.Straightening.IDisc.forget :
    CartesianFunctor (𝟭 Cat.{v₁, u₁}) IDisc.{v₂, u₂, v₁, u₁}
    Opfibration.Straightening.ICatLax.{v₂, u₂, v₁, u₁}

recall Displayed.Discrete.Straightening.IDisc.forgetFullyFaithful :
    VertFunctor.FullyFaithful IDisc.forget.{v₂, u₂, v₁, u₁}.toDispFunctor
