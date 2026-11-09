import ComprehensionCategory.Map
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Unit
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Displayed.TypeFormers.Unit
import Displayed.Straightening.Equivalence
import Tactic.KernelTactic

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

It preserves Σ-types strictly (`catToDispComprehensionMap_preservesSigma`), but only
propositionally. The Σ-type of the category model is the straightening of the composite
`sigmaOb A B` of `∫ A` and `∫ B`, and its image is the straightening of the unstraightening of
that, while the Σ-type of the displayed model is the straightening of the composite itself. So it
comes down to the counit of straightening–unstraightening at `sigmaOb A B`, which is the identity on
objects. Over `(f, φ)`, a morphism of `∫ (straightenObj (sigmaOb A B))` has as second component a
morphism `B(𝟙, φ) (B(f, 𝟙) b) ⟶ b'`, from the pushforward in the fibre, and one of the composite a
morphism `B(f, φ) b ⟶ b'`. These types are equal by the functoriality of `B`, but not
definitionally: the rules expand `B` of a composite, and `(f, φ)` is not one. The counit casts
along these equalities (`counitInv_catSigmaOb_map_eq_cast`), so the two displayed categories are
equal and the counit is the identity (`VertFunctor.eq_of_map_cast`). This gives the equality of
the Σ-types, and the pairing of the category model, the reassociation followed by the counit, is
then that of the displayed model, the reassociation.

The equation `B(f, φ) = B(𝟙, φ) ∘ B(f, 𝟙)` is `B.map_comp`, applied to the composite
`(f, 𝟙) ≫ (𝟙, φ)`, which is `(f, φ)` by `rfl`. It is checked in the kernel (`kernel_exact`): the
elaborator, comparing the two sides, applies the functor rules to `B` of the composite first.
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

/-! ## Σ-types -/

/-- The projections of a cast along an equality of Σ-types with the same first components. -/
theorem cast_sigma {α : Type u} {β β' : α → Type u} (h : β = β') (p : Σ a, β a) :
    (cast (congrArg Sigma h) p).1 = p.1 ∧ (cast (congrArg Sigma h) p).2 ≍ p.2 := by
  subst h
  exact ⟨rfl, HEq.rfl⟩

/-- A vertical functor witnessing an equality of displayed categories over `Γ` (as in
`VertFunctor.eq_of_map_cast`) is the identity on the total categories: precomposed with `G`, it
gives `G`. -/
theorem comp_total_toCatHom_heq {Γ : Cat.{u, u}} {D E : Displayed.{u, u} Γ} (h : D = E)
    {H : VertFunctor D E} (hH : H ≍ VertFunctor.id D) {C : Type u} [Category.{u} C]
    (G : C ⥤ D.Total) : (G ⋙ H.total).toCatHom ≍ G.toCatHom := by
  subst h
  obtain rfl := eq_of_heq hH
  rfl

section Sigma

open CatModel

variable {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) (B : ICatLax.{u, u}.Ty (Γ ▹ A))

/-- The second components of the morphisms of `sigmaOb A B` over `f` and of its counit image: over
`φ`, the morphisms `B(f, φ) b ⟶ b'` and `B(𝟙, φ) (B(f, 𝟙) b) ⟶ b'`, equal by `B.map_comp`. -/
theorem catSigmaOb_hom_snd_eq {a a' : Γ} (f : a ⟶ a') (x : (sigmaOb A B).toDisplayed.Ob a)
    (y : (sigmaOb A B).toDisplayed.Ob a') :
    (fun φ : (∫ A).Hom f x.1 y.1 => (∫ B).Hom ((∫ A).totalMk f φ) x.2 y.2) =
      fun φ => (∫ B).Hom ((∫ A).totalMk (𝟙 a') φ) ((∫ B).push ((∫ A).totalOlift f x.1) x.2) y.2 :=
  funext fun φ => by
    kernel_exact @congrArg _ _ ((∫ A).totalMk f φ)
      ((∫ A).totalOlift f x.1 ≫ (∫ A).totalMk (𝟙 a') φ)
      (fun g : (∫ A).tot x.1 ⟶ (∫ A).tot y.1 => (∫ B).Hom g x.2 y.2) rfl

/-- The hom-types of `sigmaOb A B` and of the unstraightening of its straightening are equal. -/
theorem catSigmaOb_hom_eq {a a' : Γ} (f : a ⟶ a') (x : (sigmaOb A B).toDisplayed.Ob a)
    (y : (sigmaOb A B).toDisplayed.Ob a') :
    (sigmaOb A B).toDisplayed.Hom f x y =
      (∫ (straightenObj (sigmaOb A B))).Hom f ((counitInv (sigmaOb A B)).obj x)
        ((counitInv (sigmaOb A B)).obj y) :=
  congrArg Sigma (catSigmaOb_hom_snd_eq A B f x y)

/-- The inverse of the counit at `sigmaOb A B` casts along `catSigmaOb_hom_eq`. Its second
component is `χ.2`, at a type which the kernel identifies with that of `χ.2` through `B` of a
composite. -/
theorem counitInv_catSigmaOb_map_eq_cast {a a' : Γ} {f : a ⟶ a'}
    {x : (sigmaOb A B).toDisplayed.Ob a} {y : (sigmaOb A B).toDisplayed.Ob a'}
    (χ : (sigmaOb A B).toDisplayed.Hom f x y) :
    (counitInv (sigmaOb A B)).map χ = cast (catSigmaOb_hom_eq A B f x y) χ := by
  obtain ⟨h₁, h₂⟩ := cast_sigma (catSigmaOb_hom_snd_eq A B f x y) χ
  refine Sigma.ext h₁.symm (HEq.trans ?_ h₂.symm)
  kernel_exact @cast_heq ((∫ B).Hom ((∫ A).totalMk f χ.1) x.2 y.2)
    ((∫ B).Hom ((∫ A).totalOlift f x.1 ≫ (∫ A).totalMk (𝟙 _) χ.1) x.2 y.2)
    (@congrArg _ _ ((∫ A).totalMk f χ.1) ((∫ A).totalOlift f x.1 ≫ (∫ A).totalMk (𝟙 _) χ.1)
      (fun g : (∫ A).tot x.1 ⟶ (∫ A).tot y.1 => (∫ B).Hom g x.2 y.2) rfl) χ.2

/-- **Unstraightening the straightening of `sigmaOb A B` gives it back**, and the counit is the
identity. -/
theorem unstraighten_straighten_catSigmaOb :
    (sigmaOb A B).toDisplayed = ∫ (straightenObj (sigmaOb A B)) ∧
      counitInv (sigmaOb A B) ≍ VertFunctor.id (sigmaOb A B).toDisplayed :=
  VertFunctor.eq_of_map_cast (counitInv (sigmaOb A B)) rfl (fun _ => rfl)
    (catSigmaOb_hom_eq A B) (counitInv_catSigmaOb_map_eq_cast A B)

end Sigma

/-- **The inclusion preserves Σ-types strictly**, propositionally: the image of `Σ[A] B` is the
straightening of `sigmaOb A B`, and its pairing the reassociation of the pairs. -/
theorem catToDispComprehensionMap_preservesSigma :
    catToDispComprehensionMap.{u}.PreservesSigma where
  obj_sigma A B :=
    congrArg Straightening.straightenObj (unstraighten_straighten_catSigmaOb A B).1.symm
  map_pair {Γ} A B := by
    kernel_exact (comp_total_toCatHom_heq (unstraighten_straighten_catSigmaOb A B).1
      (unstraighten_straighten_catSigmaOb A B).2 ((∫ A).sigmaUnassoc (∫ B))).trans
      (DisplayedModel.pairHom_straightenObj (∫ A) (∫ B)).symm

end ComprehensionCategory.OverCat
