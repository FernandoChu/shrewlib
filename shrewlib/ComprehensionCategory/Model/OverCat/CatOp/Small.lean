import ComprehensionCategory.Model.OverCat.CatOp.Basic
import Displayed.Fibration.CartesianFunctor
import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
# The contravariant types of a lower level

The contravariant category model at level `v + 1` has contexts in `Cat.{v + 1, v + 1}` and types
valued in `Cat.{v + 1, v + 1}`. The contravariant types of level `v` over the same contexts are the
functors `Γᵒᵖ ⥤ Cat.{v, v}`, which are types of the contravariant category model by
`lift A = A ⋙ Cat.asSmallFunctor`, as in the category model (`OverCat/Cat/Small.lean`).

They form a full split comprehension category `SmallICatOp` over `Cat.{v + 1, v + 1}`: a morphism
over `u` from `A` to `B` is a morphism of the contravariant category model from `lift A` to
`lift B`, reindexing is precomposition, and the chosen lifts and the comprehension are those of the
contravariant category model, along the fully faithful cartesian functor
`SmallICatOp.lift : SmallICatOp ⟶ ICatOpLax`.

This is the dual of `OverCat/Cat/Small.lean`.
-/

universe v

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Displayed Displayed.Fibration.Straightening

open scoped Displayed

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- A contravariant type of level `v` as a type of the contravariant category model: each category
replaced by the equivalent `AsSmall` category of `Cat.{v + 1, v + 1}`. -/
def lift (A : Γᵒᵖ ⥤ Cat.{v, v}) : ICatOpLax.{v + 1, v + 1}.Ty Γ :=
  A ⋙ Cat.asSmallFunctor.{v + 1}

/-- `lift` commutes with substitution. -/
theorem lift_pull (σ : Δ ⟶ Γ) (A : Γᵒᵖ ⥤ Cat.{v, v}) :
    lift (σ.toFunctor.op ⋙ A) = (lift A)⦃σ⦄ :=
  rfl

/-- **The contravariant types of level `v`** over the contexts of level `v + 1`, displayed over
`Cat.{v + 1, v + 1}`: the functors `Γᵒᵖ ⥤ Cat.{v, v}`, with the morphisms of the contravariant
category model between their lifts. -/
def SmallICatOp : Displayed.{v + 1, v + 1} Cat.{v + 1, v + 1} where
  Ob Γ := Γᵒᵖ ⥤ Cat.{v, v}
  Hom u A B := ICatOpLax.Hom u (lift A) (lift B)
  id A := ICatOpLax.id (lift A)
  comp φ ψ := ICatOpLax.comp φ ψ

namespace SmallICatOp

/-- The chosen lift of `u` at `A`: that of the contravariant category model at `lift A`. -/
def clift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : Bᵒᵖ ⥤ Cat.{v, v}) :
    SmallICatOp.Hom u (u.toFunctor.op ⋙ X) X :=
  Fib.clift (D := ICatOpLax) u (lift X)

/-- The chosen lift is cartesian, since it is in the contravariant category model and the
morphisms are the same. -/
def isCartesianClift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : Bᵒᵖ ⥤ Cat.{v, v}) :
    IsCartesian (D := SmallICatOp) (clift u X) :=
  let H := Fib.isCartesianClift (D := ICatOpLax) u (lift X)
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end SmallICatOp

/-- **`SmallICatOp` is a split fibration**, reindexing by precomposition, with the chosen lifts of
the contravariant category model. -/
instance SmallICatOp.preSplitFib : PreSplitFib SmallICatOp.{v} where
  pull u X := u.toFunctor.op ⋙ X
  clift u X := SmallICatOp.clift u X
  isCartesianClift u X := SmallICatOp.isCartesianClift u X

instance SmallICatOp.splitFib : SplitFib SmallICatOp.{v} := {}

/-- **The lift into the contravariant category model**, a vertical cartesian functor. -/
def SmallICatOp.lift :
    CartesianFunctor (𝟭 Cat.{v + 1, v + 1}) SmallICatOp.{v}
      ICatOpLax.{v + 1, v + 1, v + 1, v + 1} where
  toPre :=
    { obj A := CatOpModel.lift A
      map φ := φ }

/-- **The lift is fully faithful**, since the morphisms are those of the contravariant category
model. -/
def SmallICatOp.liftFullyFaithful :
    VertFunctor.FullyFaithful SmallICatOp.lift.{v}.toDispFunctor where
  preimage φ := φ

/-- The comprehension structure of the contravariant types of level `v`: that of the
contravariant category model, along the lift. -/
@[instance_reducible]
instance SmallICatOp.comprehension : Comprehension SmallICatOp.{v} :=
  Comprehension.comap SmallICatOp.lift.toDispFunctor SmallICatOp.lift.isCartesianMap

/-- **The contravariant types of level `v`** form a full split comprehension category. -/
instance SmallICatOp.splitComprehension : SplitComprehension SmallICatOp.{v} := {}

@[instance_reducible]
instance SmallICatOp.fullComprehension : FullComprehension SmallICatOp.{v} where
  comprFullyFaithful := SmallICatOp.liftFullyFaithful.comp comprFullyFaithful

end ComprehensionCategory.CatOpModel
