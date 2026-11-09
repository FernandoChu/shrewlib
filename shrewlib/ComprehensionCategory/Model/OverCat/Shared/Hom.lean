import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Cat.Term
import Tactic.KernelTactic

/-!
# Hom-types

For `A` a type of the category model in context `Γ`, its Hom-type `Hom[A]` is a type of the
discrete model, in the context `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ` of the category model, of the morphisms from
`a : Aᵒᵖ` to `b : A`:

```
                 Γ ⊢ A type
  ------------------------------------------- Hom-Form
    Γ ▹ b : A ▹ a : Aᵒᵖ ⊢ Homₐ(a, b) type

                 Γ ⊢ A type
  ------------------------------------------- Hom-op
    Γ ▹ b : A ▹ a : Aᵒᵖ ⊢ Homₐ(a, b)ᵒᵖ ≡ Homₐ(a, b) type
```

The contravariant variable comes last, so that `Hom[A]` is a dependent profunctor over `A⦃𝐩 A⦄`,
which the twist takes (`Shared/Twist.lean`, `Shared/HomIntro.lean`).

An object of the context `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ` is a triple `((γ, b), a)` with `a b : A γ`, and a
morphism `((γ, b), a) ⟶ ((γ', b'), a')` is a triple `((f, ψ), φ)` with `f : γ ⟶ γ'`,
`ψ : A f b ⟶ b'`, and `φ : A f a ⟶ a'` in the opposite of `A γ'`. The Hom-type `Hom[A]` sends
`((γ, b), a)` to the discrete category on the morphisms `a ⟶ b` of `A γ` (`discrete'`), and
`((f, ψ), φ)` to `h ↦ φ ≫ A f h ≫ ψ` (`homAct`). Its functor laws and its stability under
substitution hold by `rfl` (`pull_hom`).

The composite with `φ` is taken in the opposite of `A γ'`, where `φ` lives, as
`(A f h ≫ ψ) ≫ᵒᵖ φ`. Taken in `A γ'`, the rule `Category.id_comp` would not apply at the identity
of the context, whose `φ` is an identity of the opposite: the two category structures differ, even
though their identities agree.

Hom-op, stated with the opposite types of the discrete model, holds since a discrete category
`discrete' S` is its own opposite, which is a propositional equality
(`opCategory'_discreteCategory'`, by `propext`): `t = s` and `s = t` are different types. So it is
proved, and made judgmental as a rewrite rule (`op_hom`).

The notation `Hom[A]` for `OverCat.hom A` is scoped in `ComprehensionCategory.OverCat`.

## The Hom-type of two terms

`Hom[A]` is the Hom-type in context form, over the two variables, which is the form the twist takes
(`Shared/Twist`, `Shared/HomIntro`). The Hom-type of the paper is that of two terms
`a : Tm(Γ, Aᵒᵖ)` and `b : Tm(Γ, A)`, in context `Γ`:

```
    Γ ⊢ A type      Γ ⊢ a : Aᵒᵖ      Γ ⊢ b : A
  ------------------------------------------------ Hom-Form
              Γ ⊢ Homₐ(a, b) type_s
```

It is `homAt a b`, the substitution of `Hom[A]` along the extension of `b.sec` by `a`
(`consSec`). The type of `a` there is `(A⦃𝐩 A⦄)ᵒᵖ⦃b.sec⦄`, which is `Aᵒᵖ` only propositionally,
by `b.sec ≫ 𝐩 A = 𝟙` (`pull_sec_op_weak`), so `a` is transported to it (`Tm.castTy`). For terms
given by their values (`tmMk`), the value of `homAt a b` at `γ` is the discrete category on the
morphisms `a γ ⟶ b γ`, by `rfl` (`homAt_tmMk_obj`).

`homAt a b` is stable under substitution (`pull_homAt`): both sides substitute `Hom[A]`, the right
one by `pull_hom`, along extensions by `a⦃σ⦄` up to transport, over `σ ≫ b.sec` and over
`b⦃σ⦄.sec ≫ 𝐪(σ, A)`, which are equal (`Tm.pull_sec_q`). It is its own opposite (`op_homAt`), the
substitution of `op_hom`; this is not judgmental, since the rule `op_hom` does not apply to the
opposite of a substitution of `Hom[A]` until it is commuted with the substitution
(`DiscreteModel.pull_op`). The Hom-types of discrete types and Hom-Disc are in `Shared/HomDisc`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The action of a morphism `((f, ψ), φ)` of the context on the morphisms of `A`:
`h ↦ φ ≫ A f h ≫ ψ`, composed with `φ` in the opposite of `A γ'`. -/
def homAct (A : Γ ⥤ Cat.{u, u}) {γ γ' : Γ} (f : γ ⟶ γ') {a b : A.obj γ} {a' b' : A.obj γ'}
    (φ : @Quiver.Hom ((A ⋙ opFunctor').obj γ') _ ((A.map f).toFunctor.obj a) a')
    (ψ : (A.map f).toFunctor.obj b ⟶ b') (h : a ⟶ b) : a' ⟶ b' :=
  @CategoryStruct.comp ((A ⋙ opFunctor').obj γ') _ b' ((A.map f).toFunctor.obj a) a'
    ((A.map f).toFunctor.map h ≫ ψ : (A.map f).toFunctor.obj a ⟶ b') φ

/-- The functor of the Hom-type of `A`: at `((γ, b), a)`, the discrete category on the morphisms
`a ⟶ b` of `A γ`. -/
def homFunctor (A : ICatLax.{u, u}.Ty Γ) : ICatLax.{u, u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) where
  obj X := discrete' (@Quiver.Hom (A.obj X.1.1) _ X.2 X.1.2)
  map g := discreteMap' (homAct A g.base.base g.fiber g.base.fiber)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The Hom-type of `A`** (Hom-Form), a type of the discrete model: its values are discrete
categories. -/
def hom (A : ICatLax.{u, u}.Ty Γ) : IDisc.{u, u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) where
  toFunctor := homFunctor A
  isDiscrete _ := isDiscrete_discrete' _

/-- `Hom[A]` is the Hom-type `OverCat.hom A`. -/
scoped notation:max "Hom[" A "]" => OverCat.hom A

/-- Displays `OverCat.hom A` as `Hom[A]`. -/
@[scoped app_unexpander OverCat.hom]
def unexpandHom : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `(Hom[$A])
  | _ => throw ()

/-- The functor of the Hom-type is its own opposite, since discrete categories are. -/
theorem op_homFunctor (A : ICatLax.{u, u}.Ty Γ) : (homFunctor A)ᵒᵖ = homFunctor A :=
  Functor.hext (fun _ => opFunctor'_obj_discrete' _) fun _ _ _ => opFunctor'_map_discreteMap' _

/-- **Hom-op**: the Hom-type is its own opposite, as a rewrite rule. -/
@[rewrite_rule]
theorem op_hom (A : ICatLax.{u, u}.Ty Γ) : Hom[A]ᵒᵖ = Hom[A] :=
  IDiscOb.ext (op_homFunctor A)

/-- **The Hom-types are stable under substitution**, by `rfl`. -/
theorem pull_hom {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatLax.{u, u}.Ty Γ) :
    Hom[A]⦃𝐪(𝐪(σ, A), (A⦃𝐩 A⦄)ᵒᵖ)⦄ = Hom[A⦃σ⦄] :=
  rfl

/-! ## The Hom-type of two terms -/

/-- The type `(A⦃𝐩 A⦄)ᵒᵖ` of the second variable of the Hom-type, substituted along the section of
a term `b` of `A`, is `Aᵒᵖ`, since `b.sec ≫ 𝐩 A = 𝟙`. -/
theorem pull_sec_op_weak {A : ICatLax.{u, u}.Ty Γ} (b : Tm(Γ, A)) : (A⦃𝐩 A⦄)ᵒᵖ⦃b.sec⦄ = Aᵒᵖ :=
  congrArg (fun σ => (A⦃σ⦄)ᵒᵖ) b.sec_proj

/-- **The Hom-type of two terms** (Hom-Form, as in the paper): for `a : Tm(Γ, Aᵒᵖ)` and
`b : Tm(Γ, A)`, the substitution of `Hom[A]` along the pairing of `b` and `a`. -/
def homAt {A : ICatLax.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) : IDisc.{u, u}.Ty Γ :=
  Hom[A]⦃consSec b.sec (a.castTy (pull_sec_op_weak b).symm)⦄

/-- **Hom-op for the Hom-type of two terms**: it is its own opposite, the substitution of the rule
`op_hom`, after commuting the opposite with the substitution. -/
theorem op_homAt {A : ICatLax.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) :
    (homAt a b)ᵒᵖ = homAt a b := by
  kernel_exact (DiscreteModel.pull_op (consSec b.sec (a.castTy (pull_sec_op_weak b).symm))
    Hom[A]).symm.trans
    (congrArg (fun X => X⦃consSec b.sec (a.castTy (pull_sec_op_weak b).symm)⦄) (op_hom A))

/-- At `γ`, the Hom-type of the terms with values `a γ` and `b γ` is the discrete category on the
morphisms `a γ ⟶ b γ` of `A γ`, by `rfl`. -/
theorem homAt_tmMk_obj {A : ICatLax.{u, u}.Ty Γ} (a : ∀ γ : Γ, A.obj γ)
    (amap : ∀ {γ γ' : Γ} (f : γ ⟶ γ'), (Aᵒᵖ.map f).toFunctor.obj (a γ) ⟶ a γ') amap_id amap_comp
    (b : ∀ γ : Γ, A.obj γ)
    (bmap : ∀ {γ γ' : Γ} (f : γ ⟶ γ'), (A.map f).toFunctor.obj (b γ) ⟶ b γ') bmap_id bmap_comp
    (γ : Γ) :
    (homAt (tmMk (A := Aᵒᵖ) a amap amap_id amap_comp) (tmMk b bmap bmap_id bmap_comp)).toFunctor.obj
      γ = discrete' (@Quiver.Hom (A.obj γ) _ (a γ) (b γ)) :=
  rfl

/-- The type of the second variable of the Hom-type of `A⦃σ⦄`, substituted along `b⦃σ⦄`, is that
of `A`, substituted along `𝐪(σ, A)` and `b⦃σ⦄`. They agree by the rules for substitution, which the
elaborator is slow to apply here, so this is checked in the kernel. -/
theorem pull_q_op_weak {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : ICatLax.{u, u}.Ty Γ} (b : Tm(Γ, A)) :
    ((A⦃σ⦄)⦃𝐩 A⦃σ⦄⦄)ᵒᵖ⦃b⦃σ⦄.sec⦄ = ((A⦃𝐩 A⦄)ᵒᵖ)⦃𝐪(σ, A)⦄⦃b⦃σ⦄.sec⦄ := by
  kernel_rfl'

/-- **The Hom-type of two terms is stable under substitution.** Both sides substitute `Hom[A]`, by
`pull_hom`, along extensions by `a⦃σ⦄` up to transport, over `σ ≫ b.sec` and over
`b⦃σ⦄.sec ≫ 𝐪(σ, A)`, which are equal. -/
theorem pull_homAt {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : ICatLax.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ))
    (b : Tm(Γ, A)) : (homAt a b)⦃σ⦄ = homAt (A := A⦃σ⦄) a⦃σ⦄ b⦃σ⦄ := by
  have h := pull_sec_op_weak (A := A⦃σ⦄) b⦃σ⦄
  have E := (comp_consSec σ b.sec (a.castTy (pull_sec_op_weak b).symm)).trans
    ((consSec_congr (Tm.pull_sec_q σ b).symm
      ((Tm.pull_castTy_sec_heq σ _ a).trans
        ((Tm.castTy_sec_heq (pull_q_op_weak σ b) (a⦃σ⦄.castTy h.symm)).trans
          (Tm.castTy_sec_heq h.symm a⦃σ⦄)).symm)).trans
      (consSec_comp_q b⦃σ⦄.sec 𝐪(σ, A)
        ((a⦃σ⦄.castTy h.symm).castTy (pull_q_op_weak σ b))).symm)
  kernel_exact congrArg (fun ρ => Hom[A]⦃ρ⦄) E

end ComprehensionCategory.OverCat
