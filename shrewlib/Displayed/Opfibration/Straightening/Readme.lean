import Displayed.Opfibration.Straightening.Equivalence
import Displayed.Opfibration.Straightening.Str

/-!
# Straightening for opfibrations

In this folder we compare two categories displayed over `Cat`:

* `ICatLax`: which has as objects over a category `A` the functors `A ⥤ Cat`; a morphism over
  `u : A ⟶ B` is a lax transformation `LaxTrans F (u ⋙ G)`;
* `SplitOpfibLax` (`Opfibration/SplitOpfibLax.lean`): an object over `A` is a displayed category
  over `A` with a split opcleavage, and a morphism over `u` is any displayed functor over `u`, not
  necessarily preserving the chosen lifts.

The vertical functor `unstraighten : ICatLax ⟶ SplitOpfibLax` sends `F` to the displayed category
`∫ F` whose fibre over `a` is `F a`, with morphisms `x ⟶[f] y` the morphisms
`F f x ⟶ y`, pushing forward along `F`. It is an equivalence over `Cat`, `straighteningEquivLax`.

The files give its ingredients:

* `ICatLax`: lax transformations between functors into `Cat`, and the split fibration `ICatLax`,
  whose reindexing along `u` sends `G` to `u ⋙ G`.
* `Unstraighten`: the functor `unstraighten`, and the inverse of its action on morphisms. Transport
  in `∫ F` along `f` is `F f`, as a rule (`unstraightenPushMap`).
* `Straighten`: the straightening `straighten`, sending a split opfibration `D` to the functor
  `A ⥤ Cat` of its fibres, and a displayed functor `H` to the lax transformation with components
  `H` and 2-cells the opcartesian factorizations of the images of the chosen lifts.
* `Equivalence`: the unit, which is the identity, the counit, and the equivalence
  `straighteningEquivLax`.

The same holds with strict morphisms, between `ICatStr`, whose morphisms are the strict
transformations, and `SplitOpfibStr` (`Opfibration/SplitOpfibStr.lean`), whose morphisms are the
opcartesian functors:

* `ICatStr`: strict transformations, `ICatStr`, and its inclusion into `ICatLax`. A strict
  transformation `τ` unstraightens to an opcartesian functor `τ.unstraighten`, and to the functor
  `τ.dualTotal` between the total categories of the dual opfibrations.
* `Str`: the equivalence `straighteningEquivStr`, whose functors are those of
  `straighteningEquivLax` on the underlying lax morphisms, whose unit is the identity and whose
  counit is that of `straighteningEquivLax`.
-/

universe v₁ u₁ v u

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening for split opfibrations** is an equivalence over `Cat`. -/
recall Displayed.Opfibration.Straightening.straighteningEquivLax :
    VertEquivalence ICatLax.{u} SplitOpfibLax.{u}

recall Displayed.Opfibration.Straightening.ICatLax.splitFib : SplitFib ICatLax.{u}

/-- **Straightening–unstraightening for split opfibrations, with strict morphisms**. -/
recall Displayed.Opfibration.Straightening.straighteningEquivStr :
    VertEquivalence ICatStr.{u} SplitOpfibStr.{u}

/-- With strict morphisms, the unstraightening and the straightening are those of the underlying
lax morphisms. -/
recall Displayed.Opfibration.Straightening.unstraightenStr_comp_forget :
    unstraightenStr.{u} ⋙ᵥ SplitOpfibStr.forget = ICatStr.forget ⋙ᵥ unstraighten

recall Displayed.Opfibration.Straightening.straightenStr_comp_forget :
    straightenStr.{u} ⋙ᵥ ICatStr.forget = SplitOpfibStr.forget ⋙ᵥ straighten

/-- The unstraightening `∫ F` of `F : A ⥤ Cat` is a split opfibration. -/
recall Displayed.Opfibration.Straightening.unstraightenSplitOpfib {A : Type u₁}
    [Category.{v₁} A] (F : A ⥤ Cat.{v, u}) : SplitOpfib (∫ F)

/-- The unstraightening is fully faithful: displayed functors from `∫ F` to
`∫ G` over `u` are lax transformations `LaxTrans F (u ⋙ G)`. -/
recall Displayed.Opfibration.Straightening.unstraightenFullyFaithful :
    unstraighten.{u}.FullyFaithful
