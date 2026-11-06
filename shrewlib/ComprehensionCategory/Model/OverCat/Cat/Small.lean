import ComprehensionCategory.Model.OverCat.Cat.Basic
import Displayed.Fibration.CartesianFunctor
import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
# The types of a lower level

The category model at level `v + 1` has contexts in `Cat.{v + 1, v + 1}` and types valued in
`Cat.{v + 1, v + 1}`. The types of level `v` over the same contexts are the functors
`Γ ⥤ Cat.{v, v}`, which are types of the category model by `lift A = A ⋙ Cat.asSmallFunctor`,
replacing each category by the equivalent `AsSmall` category of `Cat.{v + 1, v + 1}`.

They form a comprehension category `SmallICat` over `Cat.{v + 1, v + 1}`, as the discrete model
does over `Cat`: a morphism over `u` from `A` to `B` is a morphism of the category model from
`lift A` to `lift B`, reindexing is precomposition, and the chosen lifts are those of the category
model, so that `SmallICat` is a split fibration whose laws hold by `rfl`. Its comprehension is that
of the category model along `SmallICat.lift : SmallICat ⟶ ICatLax`, a fully faithful cartesian
functor, so that `SmallICat` is a full split comprehension category, and `lift` is a strict map of
comprehension categories (`OverCat/Maps/SmallToCat`).
-/

universe v

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- A type of level `v` as a type of the category model: each category replaced by the equivalent
`AsSmall` category of `Cat.{v + 1, v + 1}`. -/
def lift (A : Γ ⥤ Cat.{v, v}) : ICatLax.{v + 1}.Ty Γ :=
  A ⋙ Cat.asSmallFunctor.{v + 1}

/-- `lift` commutes with substitution. -/
theorem lift_pull (σ : Δ ⟶ Γ) (A : Γ ⥤ Cat.{v, v}) : lift (σ.toFunctor ⋙ A) = (lift A)⦃σ⦄ :=
  rfl

/-- **The types of level `v`** over the contexts of level `v + 1`, displayed over
`Cat.{v + 1, v + 1}`: the functors `Γ ⥤ Cat.{v, v}`, with the morphisms of the category model
between their lifts. -/
def SmallICat : Displayed.{v + 1, v + 2, v + 1, v + 1} Cat.{v + 1, v + 1} where
  Ob Γ := Γ ⥤ Cat.{v, v}
  Hom u A B := ICatLax.Hom u (lift A) (lift B)
  id A := ICatLax.id (lift A)
  comp φ ψ := ICatLax.comp φ ψ

namespace SmallICat

/-- The chosen lift of `u` at `A`: that of the category model at `lift A`. -/
def clift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : B ⥤ Cat.{v, v}) :
    SmallICat.Hom u (u.toFunctor ⋙ X) X :=
  Fib.clift (D := ICatLax) u (lift X)

/-- The chosen lift is cartesian, since it is in the category model and the morphisms are the
same. -/
def isCartesianClift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : B ⥤ Cat.{v, v}) :
    IsCartesian (D := SmallICat) (clift u X) :=
  let H := Fib.isCartesianClift (D := ICatLax) u (lift X)
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end SmallICat

/-- **`SmallICat` is a split fibration**, reindexing by precomposition, with the chosen lifts of
the category model. -/
instance SmallICat.preSplitFib : PreSplitFib SmallICat.{v} where
  pull u X := u.toFunctor ⋙ X
  clift u X := SmallICat.clift u X
  isCartesianClift u X := SmallICat.isCartesianClift u X

instance SmallICat.splitFib : SplitFib SmallICat.{v} := {}

/-- **The lift into the category model**, a vertical cartesian functor. -/
def SmallICat.lift : CartesianFunctor (𝟭 Cat.{v + 1, v + 1}) SmallICat.{v} ICatLax.{v + 1} where
  toPre :=
    { obj A := CatModel.lift A
      map φ := φ }

/-- **The lift is fully faithful**, since the morphisms are those of the category model. -/
def SmallICat.liftFullyFaithful : VertFunctor.FullyFaithful SmallICat.lift.{v}.toDispFunctor where
  preimage φ := φ

/-- The comprehension structure of the types of level `v`: that of the category model, along the
lift. -/
@[instance_reducible]
instance SmallICat.comprehension : Comprehension SmallICat.{v} :=
  Comprehension.comap SmallICat.lift.toDispFunctor SmallICat.lift.isCartesianMap

/-- **The types of level `v`** form a full split comprehension category. -/
instance SmallICat.splitComprehension : SplitComprehension SmallICat.{v} := {}

@[instance_reducible]
instance SmallICat.fullComprehension : FullComprehension SmallICat.{v} where
  comprFullyFaithful := SmallICat.liftFullyFaithful.comp comprFullyFaithful

end ComprehensionCategory.CatModel
