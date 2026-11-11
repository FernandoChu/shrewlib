import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.CatOp.TypeFormers.Unit
import ComprehensionCategory.Model.OverCat.Maps.CatToDisplayed

/-!
# From the contravariant category model to the displayed category model

A type `C : Γᵒᵖ ⥤ Cat` of the contravariant category model is a type of the displayed category
model (`catOpToDisp C`), the straightening of its unstraightening `∫⁻ C`, seen as a displayed
category over `Γ`. This is the action on objects of the vertical functor `catOpToDispFunctor`, the
composite of the unstraightening `ICatOpLax ⟶ SplitFibLax`, forgetting the cleavage, and the
straightening `DisplayedCat ⟶ IProf`.

As for the category model (`OverCat/Maps/CatToDisplayed`), it is a strict map of comprehension
categories over the identity of `Cat` (`catOpToDispComprehensionMap`), whose axioms hold by `rfl`,
which gives the rules Lift-Intro, Lift-Elim and Lift-Ext, and it preserves unit types strictly, by
`rfl`. It preserves Σ-types strictly, propositionally, as there: over `(f, φ)`, a morphism of the
unstraightening of the straightening of `sigmaOb A B` has as second component a morphism
`b ⟶ B(𝟙, φ) (B(f, 𝟙) b')`, into the pullback in the fibre, and one of `sigmaOb A B` a morphism
`b ⟶ B(f, φ) b'`, and the inverse of the counit casts along the equality of these types.

This is the dual of `OverCat/Maps/CatToDisplayed.lean`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Fibration.Straightening

open scoped Displayed

/-- The vertical functor from the contravariant category model to the displayed category model:
unstraighten, forget the cleavage, and straighten. -/
def catOpToDispFunctor :
    VertFunctor ICatOpLax.{u, u, u, u} Straightening.IProf.{u, u, u} :=
  unstraighten ⋙ᵥ SplitFibLax.forget ⋙ᵥ Straightening.straighten

/-- A type `C` of the contravariant category model as a type of the displayed model: the
straightening of its unstraightening `∫⁻ C`. -/
def catOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Straightening.IProf.{u, u, u}.Ty Γ :=
  Straightening.straightenObj (∫⁻ C)

/-- `catOpToDisp` is the action of `catOpToDispFunctor` on objects. -/
theorem catOpToDispFunctor_obj {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    catOpToDispFunctor.obj C = catOpToDisp C :=
  rfl

/-- **The inclusion of the contravariant category model into the displayed model is a strict map
of comprehension categories**: the comprehension functors commute on the nose. -/
def catOpToDispComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ICatOpLax.{u, u, u, u}
      Straightening.IProf.{u, u, u} where
  toPre.toDispFunctor := catOpToDispFunctor
  toPre.isCartesianMap H :=
    DisplayedModel.comprFullyFaithful.isCartesianOfMap (isCartesianComprMap ICatOpLax H)
  toPre.compr_obj _ := rfl

/-- **Lift-Intro and Lift-Elim**: the terms of `C` are those of `catOpToDisp C`. -/
def tmEquivCatOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Tm(Γ, C) ≃ Tm(Γ, catOpToDisp C) :=
  catOpToDispComprehensionMap.tmEquiv

/-- **Lift-Ext**: the context extensions by `C` and by `catOpToDisp C` are the same. -/
theorem ext_catOpToDisp {Γ : Cat.{u, u}} (C : ICatOpLax.{u, u}.Ty Γ) :
    Γ ▹ catOpToDisp C = Γ ▹ C :=
  rfl

/-- **The inclusion preserves unit types strictly**, by `rfl`. -/
theorem catOpToDispComprehensionMap_preservesUnit :
    catOpToDispComprehensionMap.{u}.PreservesUnit where
  obj_unit _ := rfl

/-! ## Σ-types -/

section Sigma

open CatOpModel

-- Functors rather than types of the contravariant model, on which no instance applies.
variable {Γ : Cat.{u, u}} (A : Γᵒᵖ ⥤ Cat.{u, u}) (B : (Γ ⋉⁻ A)ᵒᵖ ⥤ Cat.{u, u})

/-- The second components of the morphisms of `sigmaOb A B` over `f` and of its counit image: over
`φ`, the morphisms `b ⟶ B(f, φ) b'` and `b ⟶ B(𝟙, φ) (B(f, 𝟙) b')`, equal by `B.map_comp`. -/
theorem catOpSigmaOb_hom_snd_eq {a a' : Γ} (f : a ⟶ a') (x : (sigmaOb A B).toDisplayed.Ob a)
    (y : (sigmaOb A B).toDisplayed.Ob a') :
    (fun φ : (∫⁻ A).Hom f x.1 y.1 => (∫⁻ B).Hom ((∫⁻ A).totalMk f φ) x.2 y.2) =
      fun φ =>
        (∫⁻ B).Hom ((∫⁻ A).totalMk (𝟙 a) φ) x.2 ((∫⁻ B).pull ((∫⁻ A).totalClift f y.1) y.2) :=
  funext fun φ => by
    kernel_exact @congrArg _ _ ((∫⁻ A).totalMk f φ)
      ((∫⁻ A).totalMk (𝟙 a) φ ≫ (∫⁻ A).totalClift f y.1)
      (fun g : (∫⁻ A).tot x.1 ⟶ (∫⁻ A).tot y.1 => (∫⁻ B).Hom g x.2 y.2) rfl

/-- The hom-types of `sigmaOb A B` and of the unstraightening of its straightening are equal. -/
theorem catOpSigmaOb_hom_eq {a a' : Γ} (f : a ⟶ a') (x : (sigmaOb A B).toDisplayed.Ob a)
    (y : (sigmaOb A B).toDisplayed.Ob a') :
    (sigmaOb A B).toDisplayed.Hom f x y =
      (∫⁻ (straightenObj (sigmaOb A B))).Hom f ((counitInv (sigmaOb A B)).obj x)
        ((counitInv (sigmaOb A B)).obj y) :=
  congrArg Sigma (catOpSigmaOb_hom_snd_eq A B f x y)

/-- The inverse of the counit at `sigmaOb A B` casts along `catOpSigmaOb_hom_eq`. -/
theorem counitInv_catOpSigmaOb_map_eq_cast {a a' : Γ} {f : a ⟶ a'}
    {x : (sigmaOb A B).toDisplayed.Ob a} {y : (sigmaOb A B).toDisplayed.Ob a'}
    (χ : (sigmaOb A B).toDisplayed.Hom f x y) :
    (counitInv (sigmaOb A B)).map χ = cast (catOpSigmaOb_hom_eq A B f x y) χ := by
  obtain ⟨h₁, h₂⟩ := cast_sigma (catOpSigmaOb_hom_snd_eq A B f x y) χ
  refine Sigma.ext h₁.symm (HEq.trans ?_ h₂.symm)
  kernel_exact @cast_heq ((∫⁻ B).Hom ((∫⁻ A).totalMk f χ.1) x.2 y.2)
    ((∫⁻ B).Hom ((∫⁻ A).totalMk (𝟙 _) χ.1 ≫ (∫⁻ A).totalClift f y.1) x.2 y.2)
    (@congrArg _ _ ((∫⁻ A).totalMk f χ.1) ((∫⁻ A).totalMk (𝟙 _) χ.1 ≫ (∫⁻ A).totalClift f y.1)
      (fun g : (∫⁻ A).tot x.1 ⟶ (∫⁻ A).tot y.1 => (∫⁻ B).Hom g x.2 y.2) rfl) χ.2

/-- **Unstraightening the straightening of `sigmaOb A B` gives it back**, and the counit is the
identity. -/
theorem unstraighten_straighten_catOpSigmaOb :
    (sigmaOb A B).toDisplayed = ∫⁻ (straightenObj (sigmaOb A B)) ∧
      counitInv (sigmaOb A B) ≍ VertFunctor.id (sigmaOb A B).toDisplayed :=
  VertFunctor.eq_of_map_cast (counitInv (sigmaOb A B)) rfl (fun _ => rfl)
    (catOpSigmaOb_hom_eq A B) (counitInv_catOpSigmaOb_map_eq_cast A B)

end Sigma

/-- **The inclusion preserves Σ-types strictly**, propositionally: the image of `Σ[A] B` is the
straightening of `sigmaOb A B`, and its pairing the reassociation of the pairs. -/
theorem catOpToDispComprehensionMap_preservesSigma :
    catOpToDispComprehensionMap.{u}.PreservesSigma where
  obj_sigma A B :=
    congrArg Straightening.straightenObj (unstraighten_straighten_catOpSigmaOb A B).1.symm
  map_pair {Γ} A B := by
    kernel_exact (comp_total_toCatHom_heq (unstraighten_straighten_catOpSigmaOb A B).1
      (unstraighten_straighten_catOpSigmaOb A B).2 ((∫⁻ A).sigmaUnassoc (∫⁻ B))).trans
      (DisplayedModel.pairHom_straightenObj (∫⁻ A) (∫⁻ B)).symm

end ComprehensionCategory.OverCat
