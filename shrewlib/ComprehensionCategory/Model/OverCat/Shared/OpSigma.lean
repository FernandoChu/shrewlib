import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Sigma
import Tactic.KernelTactic

/-!
# The opposite of a Σ-type

For a type `A` of the category model in context `Γ` and a type `B` in context `Γ ▹ A`, the opposite
`Bᵒᵖ` is a type in context `Γ ▹ (Aᵒᵖ)ᵒᵖ = Γ ▹ A`, so it has a twist `Tw(Bᵒᵖ)`, written
`Bᵒᵖ[ā/a]` in the paper, a type of the displayed model in context `Γ ▹ Aᵒᵖ`. The terms of the
opposite of the Σ-type are the pairs of a term `x` of `Aᵒᵖ` and a term of this twist at `x`:

```
  ⟨fst, snd⟩ : Tm(Γ, (Σ[A] B)ᵒᵖ) ≃ Σ x : Tm(Γ, Aᵒᵖ), Tm(Γ, Tw(Bᵒᵖ)⦃x⦄) : pair
```

naturally in `Γ` (`opSigmaEquiv`, `opFst_pull`, `opSnd_pull`).

As in the paper, the bijection comes from an isomorphism of contexts over `Γ`
(`opSigmaIso`):

```
  Γ ▹ Aᵒᵖ ▹ Tw(Bᵒᵖ) ≅ Γ ▹ (Σ[A] B)ᵒᵖ
```

An object of either side is a triple `(γ, a, b)` of `γ : Γ`, `a : A γ` and `b : B (γ, a)`. A
morphism `(γ, a, b) ⟶ (γ', a', b')` of `Γ ▹ (Σ[A] B)ᵒᵖ` is a pair of `g : γ ⟶ γ'` and a morphism
`(a', b') ⟶ (A g a, B (g, 𝟙) b)` of the fibre of `Σ[A] B` at `γ'`, that is `α : a' ⟶ A g a` and
`B (𝟙, α) b' ⟶ B (g, 𝟙) b`: these are also the morphisms of the twist over `(g, α)`, a morphism of
`Γ ▹ Aᵒᵖ`. The two functors reassociate them, and are inverse by `rfl`, in the kernel. That they
preserve composites needs the unfolding `pushMap_eq_desc` of the transport in the fibres of
`Σ[A] B`, an `irreducible_def`.

The general part is in `ComprehensionCategory/Term`: the terms of `A` across an isomorphism of
contexts over `Γ` (`Tm.equivOfIso`), and the sections of `Γ ▹ A ▹ T ⟶ Γ`, for types `A` and `T`
of two comprehension categories, are the pairs of a term `x` of `A` and a term of `T⦃x⦄`
(`Tm.sigmaEquiv`).

Naturality is stated for any term `t'` over `t` along `𝐪(σ, (Σ[A] B)ᵒᵖ)` (`opFst_pull_of`),
instantiated at `t⦃σ⦄`: the kernel compares the composites with `t⦃σ⦄` much more slowly than with a
variable. The type `((Σ[A] B)ᵒᵖ)⦃σ⦄` of `t⦃σ⦄` is `(Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄)ᵒᵖ` by the rules
`CatModel.pull_op` and `PreSigma.pull_sigma`, and that of the second component by the rule
`pull_twist`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) (B : ICatLax.{u, u}.Ty (Γ ▹ A))

/-- The context `Γ ▹ Aᵒᵖ ▹ Tw(Bᵒᵖ)`, the total category of the twist of `Bᵒᵖ`. -/
abbrev TwExt := (twistDisp (B := Aᵒᵖ) (Bᵒᵖ)).Total

/-- `((γ, a), b) ↦ (γ, (a, b))`. -/
def opSigmaObj (x : TwExt A B) : (Γ ▹ (Σ[A] B)ᵒᵖ : Cat.{u, u}) := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

/-- `((g, α), β) ↦ (g, (α, β))`. -/
def opSigmaMap {x y : TwExt A B} (k : x ⟶ y) : opSigmaObj A B x ⟶ opSigmaObj A B y :=
  ⟨k.1.1, ⟨k.1.2, k.2⟩⟩

/-- `opSigmaMap` preserves composites: the transport in the fibres of `Σ[A] B`, unfolded, is the
composite of the twist. It is stated apart from `opSigmaHom`, since the functor law of `opSigmaHom`
is turned by the rules into a tautology. -/
theorem opSigmaMap_comp {x y z : TwExt A B} (f : x ⟶ y) (g : y ⟶ z) :
    opSigmaMap A B (f ≫ g) = opSigmaMap A B f ≫ opSigmaMap A B g :=
  Total.Hom.ext' rfl (by
    change _ ≍ @CategoryStruct.comp ((sigmaOb A B).toDisplayed.Fiber _) _ _ _ _
      (opSigmaMap A B g).fiber
      ((sigmaOb A B).toDisplayed.pushMap g.base.base (opSigmaMap A B f).fiber)
    refine HEq.trans ?_ (heq_of_eq (congrArg (fun z => @CategoryStruct.comp
      ((sigmaOb A B).toDisplayed.Fiber _) _ _ _ _ (opSigmaMap A B g).fiber z)
      (pushMap_eq_desc (sigmaOb A B).toDisplayed g.base.base (opSigmaMap A B f).fiber)).symm)
    kernel_rfl')

/-- The reassociation `Γ ▹ Aᵒᵖ ▹ Tw(Bᵒᵖ) ⥤ Γ ▹ (Σ[A] B)ᵒᵖ`. -/
def opSigmaHom : TwExt A B ⥤ (Γ ▹ (Σ[A] B)ᵒᵖ : Cat.{u, u}) where
  obj := opSigmaObj A B
  map := opSigmaMap A B
  map_id _ := by kernel_rfl'
  map_comp := opSigmaMap_comp A B

/-- `(γ, (a, b)) ↦ ((γ, a), b)`. -/
def opSigmaInvObj (x : (Γ ▹ (Σ[A] B)ᵒᵖ : Cat.{u, u})) : TwExt A B := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/-- `(g, (α, β)) ↦ ((g, α), β)`. -/
def opSigmaInvMap {x y : (Γ ▹ (Σ[A] B)ᵒᵖ : Cat.{u, u})} (k : x ⟶ y) :
    opSigmaInvObj A B x ⟶ opSigmaInvObj A B y :=
  ⟨⟨k.1, k.2.1⟩, k.2.2⟩

/-- The reassociation `Γ ▹ (Σ[A] B)ᵒᵖ ⥤ Γ ▹ Aᵒᵖ ▹ Tw(Bᵒᵖ)`, inverse to `opSigmaHom`. -/
def opSigmaInv : (Γ ▹ (Σ[A] B)ᵒᵖ : Cat.{u, u}) ⥤ TwExt A B where
  obj := opSigmaInvObj A B
  map := opSigmaInvMap A B
  map_id _ := by kernel_rfl'
  map_comp f g := by
    kernel_exact congrArg (opSigmaInvMap A B)
      (opSigmaMap_comp A B (opSigmaInvMap A B f) (opSigmaInvMap A B g)).symm

/-- **The context extension by the twist of `Bᵒᵖ` is that by the opposite of the Σ-type.** -/
def opSigmaIso : (Γ ▹ Aᵒᵖ ▹ twist (B := Aᵒᵖ) (Bᵒᵖ) : Cat.{u, u}) ≅ Γ ▹ (Σ[A] B)ᵒᵖ where
  hom := (opSigmaHom A B).toCatHom
  inv := (opSigmaInv A B).toCatHom
  hom_inv_id := by kernel_rfl'
  inv_hom_id := by kernel_rfl'

/-- The isomorphism lies over `Γ`. -/
theorem opSigmaIso_proj :
    (opSigmaIso A B).hom ≫ 𝐩 (Σ[A] B)ᵒᵖ = 𝐩 (twist (B := Aᵒᵖ) (Bᵒᵖ)) ≫ 𝐩 Aᵒᵖ := by
  kernel_rfl'

/-- **The terms of the opposite of a Σ-type** are the pairs of a term `x` of `Aᵒᵖ` and a term of
the twist of `Bᵒᵖ` at `x`. -/
def opSigmaEquiv :
    Tm(Γ, (Σ[A] B)ᵒᵖ) ≃ Σ x : Tm(Γ, Aᵒᵖ), Tm(Γ, (twist (B := Aᵒᵖ) (Bᵒᵖ))⦃x.sec⦄) :=
  (Tm.equivOfIso (opSigmaIso A B) (opSigmaIso_proj A B)).symm.trans (Tm.sigmaEquiv _ _).symm

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A B}

/-- **The first projection** `fst t : Tm(Γ, Aᵒᵖ)`. -/
def opFst (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) : Tm(Γ, Aᵒᵖ) where
  sec := (t.sec ≫ (opSigmaIso A B).inv) ≫ 𝐩 (twist (B := Aᵒᵖ) (Bᵒᵖ))
  sec_proj := ((opSigmaEquiv A B t).1).sec_proj

/-- **The second projection** `snd t : Tm(Γ, Tw(Bᵒᵖ)⦃fst t⦄)`, the factorization of
`Γ ⟶ Γ ▹ Aᵒᵖ ▹ Tw(Bᵒᵖ)` through the pullback of `𝐩 Tw(Bᵒᵖ)` along `fst t`. -/
def opSnd (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) : Tm(Γ, (twist (B := Aᵒᵖ) (Bᵒᵖ))⦃(opFst t).sec⦄) :=
  Tm.ofLift (opFst t).sec (t.sec ≫ (opSigmaIso A B).inv) rfl

/-- The bijection is `⟨fst, snd⟩`. -/
theorem opSigmaEquiv_apply (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) : opSigmaEquiv A B t = ⟨opFst t, opSnd t⟩ :=
  rfl

/-- The extension of `fst t` by `snd t` is the section of `t` across the isomorphism. -/
theorem consSec_opSnd (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) :
    consSec (opFst t).sec (opSnd t) = t.sec ≫ (opSigmaIso A B).inv :=
  congrArg Subtype.val
    ((Tm.liftEquiv (opFst t).sec _).right_inv ⟨t.sec ≫ (opSigmaIso A B).inv, rfl⟩)

/-- The isomorphism followed by the first projection commutes with substitution. -/
theorem opSigmaIso_inv_q (s : Δ ⟶ Δ ▹ (Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄)ᵒᵖ) :
    ((s ≫ (opSigmaIso A⦃σ⦄ B⦃𝐪(σ, A)⦄).inv) ≫ 𝐩 (twist (B := A⦃σ⦄ᵒᵖ) (B⦃𝐪(σ, A)⦄ᵒᵖ))) ≫
        𝐪(σ, Aᵒᵖ) =
      ((s ≫ 𝐪(σ, (Σ[A] B)ᵒᵖ)) ≫ (opSigmaIso A B).inv) ≫ 𝐩 (twist (B := Aᵒᵖ) (Bᵒᵖ)) := by
  kernel_rfl'

/-- The inverse of the isomorphism commutes with substitution. -/
theorem opSigmaIso_inv_qq (s : Δ ⟶ Δ ▹ (Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄)ᵒᵖ) :
    (s ≫ (opSigmaIso A⦃σ⦄ B⦃𝐪(σ, A)⦄).inv) ≫ 𝐪(𝐪(σ, Aᵒᵖ), twist (B := Aᵒᵖ) (Bᵒᵖ)) =
      (s ≫ 𝐪(σ, (Σ[A] B)ᵒᵖ)) ≫ (opSigmaIso A B).inv := by
  kernel_rfl'

/-- Reassociation of four composites, in the shape that the kernel compares quickly with
`σ ≫ (opFst t).sec`. -/
theorem assoc3 {C : Type*} [Category C] {W X Y Z V : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (d : Z ⟶ V) : ((a ≫ b) ≫ c) ≫ d = a ≫ ((b ≫ c) ≫ d) := by
  rfl

/-- The first projection of a term over `t` along `𝐪(σ, (Σ[A] B)ᵒᵖ)` is that of `t`, substituted. -/
theorem opFst_pull_of (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) (t' : Tm(Δ, (Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄)ᵒᵖ))
    (h : t'.sec ≫ 𝐪(σ, (Σ[A] B)ᵒᵖ) = σ ≫ t.sec) : opFst t' = (opFst t)⦃σ⦄ :=
  Tm.pull_unique σ (opFst t) _ (((opSigmaIso_inv_q σ t'.sec).trans
    (congrArg (fun F => (F ≫ (opSigmaIso A B).inv) ≫ 𝐩 (twist (B := Aᵒᵖ) (Bᵒᵖ))) h)).trans
      (assoc3 _ _ _ _))

/-- **The first projection commutes with substitution.** -/
theorem opFst_pull (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) :
    opFst (A := A⦃σ⦄) (B := B⦃𝐪(σ, A)⦄) t⦃σ⦄ = (opFst t)⦃σ⦄ :=
  opFst_pull_of σ t t⦃σ⦄ (Tm.pull_sec_q σ t)

/-- The second projection of a term over `t` along `𝐪(σ, (Σ[A] B)ᵒᵖ)` is that of `t`,
substituted. -/
theorem opSnd_pull_of (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) (t' : Tm(Δ, (Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄)ᵒᵖ))
    (h : t'.sec ≫ 𝐪(σ, (Σ[A] B)ᵒᵖ) = σ ≫ t.sec) : (opSnd t').sec ≍ ((opSnd t)⦃σ⦄).sec :=
  Tm.sec_heq_of_consSec (A := twist (B := Aᵒᵖ) (Bᵒᵖ))
    ((congrArg (fun x : Tm(Δ, (Aᵒᵖ)⦃σ⦄) => x.sec ≫ 𝐪(σ, Aᵒᵖ)) (opFst_pull_of σ t t' h)).trans
      (Tm.pull_sec_q σ (opFst t)))
    (y := opSnd t') (y' := (opSnd t)⦃σ⦄)
    ((consSec_comp_q (A := twist (B := Aᵒᵖ) (Bᵒᵖ)) (opFst t').sec 𝐪(σ, Aᵒᵖ)
        (opSnd t')).symm.trans <|
      (congrArg (· ≫ 𝐪(𝐪(σ, Aᵒᵖ), twist (B := Aᵒᵖ) (Bᵒᵖ))) (consSec_opSnd t')).trans <|
      (opSigmaIso_inv_qq σ t'.sec).trans <|
      (congrArg (· ≫ (opSigmaIso A B).inv) h).trans <|
      ((Category.assoc _ _ _).trans (congrArg (σ ≫ ·) (consSec_opSnd t).symm)).trans
      (comp_consSec σ (opFst t).sec (opSnd t)))

/-- **The second projection commutes with substitution**, up to the equality of their types. -/
theorem opSnd_pull (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) :
    (opSnd (A := A⦃σ⦄) (B := B⦃𝐪(σ, A)⦄) t⦃σ⦄).sec ≍ ((opSnd t)⦃σ⦄).sec :=
  opSnd_pull_of σ t t⦃σ⦄ (Tm.pull_sec_q σ t)

/-- **Pairing** of a term `x` of `Aᵒᵖ` and a term of the twist of `Bᵒᵖ` at `x`. -/
def opPair (x : Tm(Γ, Aᵒᵖ)) (y : Tm(Γ, (twist (B := Aᵒᵖ) (Bᵒᵖ))⦃x.sec⦄)) :
    Tm(Γ, (Σ[A] B)ᵒᵖ) :=
  (opSigmaEquiv A B).symm ⟨x, y⟩

end ComprehensionCategory.OverCat
