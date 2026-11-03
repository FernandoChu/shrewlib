import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Op

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
def homFunctor (A : ICatLax.{u}.Ty Γ) : ICatLax.{u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) where
  obj X := discrete' (@Quiver.Hom (A.obj X.1.1) _ X.2 X.1.2)
  map g := discreteMap' (homAct A g.base.base g.fiber g.base.fiber)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The Hom-type of `A`** (Hom-Form), a type of the discrete model: its values are discrete
categories. -/
def hom (A : ICatLax.{u}.Ty Γ) : IDisc.{u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) where
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
theorem op_homFunctor (A : ICatLax.{u}.Ty Γ) : (homFunctor A)ᵒᵖ = homFunctor A :=
  Functor.hext (fun _ => opFunctor'_obj_discrete' _) fun _ _ _ => opFunctor'_map_discreteMap' _

/-- **Hom-op**: the Hom-type is its own opposite, as a rewrite rule. -/
@[rewrite_rule]
theorem op_hom (A : ICatLax.{u}.Ty Γ) : Hom[A]ᵒᵖ = Hom[A] :=
  IDiscOb.ext (op_homFunctor A)

/-- **The Hom-types are stable under substitution**, by `rfl`. -/
theorem pull_hom {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatLax.{u}.Ty Γ) :
    Hom[A]⦃𝐪(𝐪(σ, A), (A⦃𝐩 A⦄)ᵒᵖ)⦄ = Hom[A⦃σ⦄] :=
  rfl

end ComprehensionCategory.OverCat
