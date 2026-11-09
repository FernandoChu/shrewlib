import Displayed.Fibration.Straightening.Equivalence
import Displayed.Fibration.Straightening.Pi

/-!
# Straightening for fibrations

The dual of `Opfibration/Straightening/`. In this folder we compare two categories displayed over
`Cat`:

* `ICatOpLax`: which has as objects over a category `A` the functors `Aᵒᵖ ⥤ Cat`; a morphism over
  `u : A ⟶ B` is a lax transformation `LaxTrans F (reindex u G)`, where `reindex u G` is
  `u.op ⋙ G` written out;
* `SplitFibLax` (`Fibration/SplitFibLax.lean`): an object over `A` is a displayed category over
  `A` with a split cleavage, and a morphism over `u` is any displayed functor over `u`, not
  necessarily preserving the chosen lifts.

The vertical functor `unstraighten : ICatOpLax ⟶ SplitFibLax` sends `F` to the displayed category
`∫⁻ F` whose fibre over `a` is `F (op a)`, with morphisms `x ⟶[f] y` the morphisms
`x ⟶ F.map f.op y`, pulling back along `F`. It is an equivalence over `Cat`,
`straighteningEquivLax`.

The functor laws of `F` on the opposites `(𝟙 a).op` and `(f ≫ g).op` are rules
(`Rules.Opposite`). Reindexing is not `u.op ⋙ G`, since through `Functor.op` these rules and those
of `Rules.Functor` do not terminate.

The files give its ingredients:

* `ICatOpLax`: lax transformations between functors `Aᵒᵖ ⥤ Cat`, and the split fibration
  `ICatOpLax`, whose reindexing along `u` sends `G` to `reindex u G`.
* `Unstraighten`: the functor `unstraighten`, and the inverse of its action on morphisms. Transport
  in `∫⁻ F` along `f` is `F.map f.op`, as a rule (`unstraightenPullMap`).
* `Straighten`: the straightening `straighten`, sending a split fibration `D` to the functor
  `Aᵒᵖ ⥤ Cat` of its fibres, and a displayed functor `H` to the lax transformation with components
  `H` and 2-cells the cartesian factorizations of the images of the chosen lifts.
* `Equivalence`: the unit, which is the identity, the counit, and the equivalence
  `straighteningEquivLax`.
* `Pi`: the dependent product `piDisp A E` along `∫⁻ A` of a displayed category `E` over its total
  category, whose objects over `γ` are the sections of `E` over the fibre `A γ`, and whose
  sections are those of `E` (`piSectionEquiv`). It has no dual in `Opfibration/Straightening/`.
-/

universe v u v₁ u₁

open CategoryTheory Displayed Displayed.Fibration.Straightening

/-! ## Main results -/

/-- **Straightening–unstraightening for split fibrations** is an equivalence over `Cat`. -/
recall Displayed.Fibration.Straightening.straighteningEquivLax :
    VertEquivalence ICatOpLax.{v, u, v₁, u₁} SplitFibLax.{v, u, v₁, u₁}

recall Displayed.Fibration.Straightening.ICatOpLax.splitFib : SplitFib ICatOpLax.{v, u, v₁, u₁}

/-- The unstraightening `∫⁻ F` of `F : Aᵒᵖ ⥤ Cat` is a split fibration. -/
recall Displayed.Fibration.Straightening.unstraightenSplitFib {A : Type u₁}
    [Category.{v₁} A] (F : Aᵒᵖ ⥤ Cat.{v, u}) : SplitFib (∫⁻ F)

/-- The unstraightening is fully faithful: displayed functors from `∫⁻ F` to `∫⁻ G` over `u` are
lax transformations `LaxTrans F (reindex u G)`. -/
recall Displayed.Fibration.Straightening.unstraightenFullyFaithful :
    unstraighten.{v, u, v₁, u₁}.FullyFaithful

/-- The sections of the dependent product along `∫⁻ A` are those of `E`. -/
recall Displayed.Fibration.Straightening.piSectionEquiv {Γ : Cat.{u, u}} {A : Γᵒᵖ ⥤ Cat.{u, u}}
    {E : Displayed.{u, u} (∫⁻ A).Total} : (piDisp A E).Section ≃ E.Section
