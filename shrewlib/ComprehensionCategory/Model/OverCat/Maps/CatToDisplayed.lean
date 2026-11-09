import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Unit
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Unit
import Displayed.Straightening.Equivalence

/-!
# From the category model to the displayed category model

A type `C : Γ ⥤ Cat` of the category model is a type of the displayed category model
(`catToDisp C`), the straightening of its unstraightening `∫ C`, seen as a displayed category over
`Γ`. On morphisms, a lax transformation goes to the straightening of its unstraightening: this is
the vertical functor `catToDispFunctor`, the composite of the unstraightening
`ICatLax ⟶ SplitOpfibLax`, forgetting the opcleavage, and the straightening
`DisplayedCat ⟶ LaxNormalCat`.

It is a strict map of comprehension categories over the identity of `Cat`
(`catToDispComprehensionMap`): since unstraightening undoes straightening on the nose
(`Straightening.straighten_comp_unstraighten`), the context extension `Γ ▹ catToDisp C` of the
displayed model is the total category `Γ ⋉ C` of `∫ C`, that of the category model, and both
axioms hold by `rfl`. It preserves cartesian morphisms since the comprehension functor of the
displayed model is fully faithful, and so reflects them, and sends the image of a cartesian
morphism to the image of that morphism under the comprehension functor of the category model,
which is cartesian.

So the terms of `C` are those of `catToDisp C`, with the same sections (`tmEquiv`), the rules
Lift-Intro and Lift-Elim, and `Γ ▹ catToDisp C = Γ ▹ C` is Lift-Ext.

It preserves unit types strictly, by `rfl`: the terminal displayed category of the displayed model
is the unstraightening of the constant functor at `discrete' PUnit`
(`OverCat/Displayed/TypeFormers/Unit`).

It does not preserve Σ-types on the nose. The context `Γ ▹ Σ[A] B` of the category model has, as
the second component of a morphism over `(f, φ)`, a morphism `B(𝟙, φ) (B(f, 𝟙) b) ⟶ b'`, from the
pushforward in the fibre, and that of the displayed model a morphism `B(f, φ) b ⟶ b'`. These types
are equal by the functoriality of `B`, but not definitionally: the rules expand `B` of a composite,
and `(f, φ)` is not one.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Opfibration.Straightening

open scoped Displayed

/-- The vertical functor from the category model to the displayed category model: unstraighten,
forget the opcleavage, and straighten. -/
def catToDispFunctor : VertFunctor ICatLax.{u, u, u, u} Straightening.LaxNormalCat.{u, u, u} :=
  unstraighten ⋙ᵥ SplitOpfibLax.forget ⋙ᵥ Straightening.straighten

/-- A type `C` of the category model as a type of the displayed model: the straightening of its
unstraightening `∫ C`. -/
def catToDisp {Γ : Cat.{u, u}} (C : ICatLax.{u, u}.Ty Γ) :
    Straightening.LaxNormalCat.{u, u, u}.Ty Γ :=
  Straightening.straightenObj (∫ C)

/-- `catToDisp` is the action of `catToDispFunctor` on objects. -/
theorem catToDispFunctor_obj {Γ : Cat.{u, u}} (C : ICatLax.{u, u}.Ty Γ) :
    catToDispFunctor.obj C = catToDisp C :=
  rfl

/-- **The inclusion of the category model into the displayed model is a strict map of
comprehension categories**: the comprehension functors commute on the nose. -/
def catToDispComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ICatLax.{u, u, u, u}
      Straightening.LaxNormalCat.{u, u, u} where
  toPre.toDispFunctor := catToDispFunctor
  toPre.isCartesianMap H :=
    DisplayedModel.comprFullyFaithful.isCartesianOfMap (isCartesianComprMap ICatLax H)
  toPre.compr_obj _ := rfl

/-- **Lift-Intro and Lift-Elim**: the terms of `C` are those of `catToDisp C`. -/
def tmEquivCatToDisp {Γ : Cat.{u, u}} (C : ICatLax.{u, u}.Ty Γ) :
    Tm(Γ, C) ≃ Tm(Γ, catToDisp C) :=
  catToDispComprehensionMap.tmEquiv

/-- **Lift-Ext**: the context extensions by `C` and by `catToDisp C` are the same. -/
theorem ext_catToDisp {Γ : Cat.{u, u}} (C : ICatLax.{u, u}.Ty Γ) :
    Γ ▹ catToDisp C = Γ ▹ C :=
  rfl

/-- **The inclusion preserves unit types strictly**, by `rfl`. -/
theorem catToDispComprehensionMap_preservesUnit :
    catToDispComprehensionMap.{u}.PreservesUnit where
  obj_unit _ := rfl

end ComprehensionCategory.OverCat
