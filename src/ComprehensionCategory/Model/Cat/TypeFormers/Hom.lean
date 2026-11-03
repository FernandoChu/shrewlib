import ComprehensionCategory.Model.Cat.TypeFormers.Op
import ComprehensionCategory.TypeFormers.Hom

/-!
# Hom-types in the category model

For `A : Γ ⥤ Cat`, an object of the context `Γ ▹ Aᵒᵖ ▹ A⦃𝐩 Aᵒᵖ⦄` is a triple `((γ, a), b)` with
`a b : A γ`, and a morphism `((γ, a), b) ⟶ ((γ', a'), b')` is a triple `((f, φ), ψ)` with
`f : γ ⟶ γ'`, `φ : A f a ⟶ a'` in the opposite of `A γ'`, and `ψ : A f b ⟶ b'`. The Hom-type
`Hom[A]` sends `((γ, a), b)` to the discrete category on the morphisms `a ⟶ b` of `A γ`
(`discrete'`), and `((f, φ), ψ)` to `h ↦ φ ≫ A f h ≫ ψ` (`homAct`). Its functor laws and its
stability under substitution hold by `rfl`.

The composite with `φ` is taken in the opposite of `A γ'`, where `φ` lives, as
`(A f h ≫ ψ) ≫ᵒᵖ φ`. Taken in `A γ'`, the rule `Category.id_comp` would not apply at the identity
of the context, whose `φ` is an identity of the opposite: the two category structures differ, even
though their identities agree.

Hom-op holds since a discrete category is its own opposite, which is a propositional equality
(`opCategory'_discreteCategory'`, by `propext`): `t = s` and `s = t` are different types. So
`Hom[A] ⋙ opFunctor' = Hom[A]` is proved (`op_hom_eq`), and the rule `HasHom.op_hom` makes it
judgmental.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The action of a morphism `((f, φ), ψ)` of the context on the morphisms of `A`:
`h ↦ φ ≫ A f h ≫ ψ`, composed with `φ` in the opposite of `A γ'`. -/
def homAct (A : Γ ⥤ Cat.{u, u}) {γ γ' : Γ} (f : γ ⟶ γ') {a b : A.obj γ} {a' b' : A.obj γ'}
    (φ : @Quiver.Hom ((A ⋙ opFunctor').obj γ') _ ((A.map f).toFunctor.obj a) a')
    (ψ : (A.map f).toFunctor.obj b ⟶ b') (h : a ⟶ b) : a' ⟶ b' :=
  @CategoryStruct.comp ((A ⋙ opFunctor').obj γ') _ b' ((A.map f).toFunctor.obj a) a'
    ((A.map f).toFunctor.map h ≫ ψ : (A.map f).toFunctor.obj a ⟶ b') φ

/-- The Hom-type of `A`: at `((γ, a), b)`, the discrete category on the morphisms `a ⟶ b` of
`A γ`. -/
def hom (A : ICat.{u}.Ty Γ) : ICat.{u}.Ty (Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄) where
  obj X := discrete' (@Quiver.Hom (A.obj X.1.1) _ X.1.2 X.2)
  map g := discreteMap' (homAct A g.base.base g.base.fiber g.fiber)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Hom-op**: the Hom-type is its own opposite, since discrete categories are. -/
theorem op_hom_eq (A : ICat.{u}.Ty Γ) : CatModel.op (CatModel.hom A) = CatModel.hom A :=
  Functor.hext (fun _ => opFunctor'_obj_discrete' _) fun _ _ _ => opFunctor'_map_discreteMap' _

/-- **The category model has Hom-types.** Hom-op holds since discrete categories are their own
opposites, and the stability under substitution by `rfl`. -/
instance hasHom : HasHom ICat.{u} where
  hom A := CatModel.hom A
  op_hom A := op_hom_eq A
  pull_hom _ _ := rfl

end ComprehensionCategory.CatModel
