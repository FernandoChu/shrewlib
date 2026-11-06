import ComprehensionCategory.Model.OverCat.Cat.Small
import ComprehensionCategory.Model.OverCat.Discrete.Basic

/-!
# The discrete types of a lower level

The discrete types of level `v` over the contexts of level `v + 1` are the functors
`Γ ⥤ Cat.{v, v}` into discrete categories (`IDiscOb.{v} Γ`). They are types of the category model
at level `v + 1` by the lift `lift A = A ⋙ Cat.asSmallFunctor` of `Cat/Small`, and of the discrete
model by `liftDisc`, since the categories `AsSmall C` of discrete categories `C` are discrete
(`isDiscrete_asSmall`).

As the types of level `v` (`SmallICat`), they form a comprehension category `SmallIDisc` over
`Cat.{v + 1, v + 1}`: a morphism over `u` from `A` to `B` is a morphism of the category model from
`lift A` to `lift B`, reindexing is precomposition, and the chosen lifts are those of the category
model, so that `SmallIDisc` is a split fibration whose laws hold by `rfl`. Its comprehension is that
of the category model along `SmallIDisc.lift : SmallIDisc ⟶ ICatLax`, a fully faithful cartesian
functor, so that `SmallIDisc` is a full split comprehension category, and its lift is a strict map
of comprehension categories (`OverCat/Maps/SmallToCat`).
-/

universe v

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel

open scoped Displayed

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- The category `AsSmall C` of a discrete category `C` is discrete. -/
theorem isDiscrete_asSmall (C : Cat.{v, v}) [IsDiscrete C] :
    IsDiscrete (Cat.asSmallFunctor.{v + 1}.obj C) where
  subsingleton x y :=
    ⟨fun f g => congrArg ULift.up (Subsingleton.elim (α := ULift.down x ⟶ ULift.down y)
      (ULift.down f) (ULift.down g))⟩
  eq_of_hom f := congrArg ULift.up (IsDiscrete.eq_of_hom (C := C) (ULift.down f))

/-- A discrete type of level `v` as a type of the discrete model: each category replaced by the
equivalent `AsSmall` category of `Cat.{v + 1, v + 1}`. -/
def liftDisc (A : IDiscOb.{v} Γ) : IDisc.{v + 1}.Ty Γ where
  toFunctor := CatModel.lift A.toFunctor
  isDiscrete γ := @isDiscrete_asSmall (A.toFunctor.obj γ) (A.isDiscrete γ)

/-- `liftDisc` commutes with substitution. -/
theorem liftDisc_pull (σ : Δ ⟶ Γ) (A : IDiscOb.{v} Γ) :
    liftDisc ⟨σ.toFunctor ⋙ A.toFunctor, fun δ => A.isDiscrete (σ.toFunctor.obj δ)⟩ =
      (liftDisc A)⦃σ⦄ :=
  rfl

/-- **The discrete types of level `v`** over the contexts of level `v + 1`, displayed over
`Cat.{v + 1, v + 1}`: the functors `Γ ⥤ Cat.{v, v}` into discrete categories, with the morphisms of
the category model between their lifts. -/
def SmallIDisc : Displayed.{v + 1, v + 2, v + 1, v + 1} Cat.{v + 1, v + 1} where
  Ob Γ := IDiscOb.{v} Γ
  Hom u A B := ICatLax.Hom u (CatModel.lift A.toFunctor) (CatModel.lift B.toFunctor)
  id A := ICatLax.id (CatModel.lift A.toFunctor)
  comp φ ψ := ICatLax.comp φ ψ

namespace SmallIDisc

/-- Reindexing `pull u X` of `X` along `u`: precomposition, whose values are those of `X`. -/
def pull {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : IDiscOb.{v} B) : IDiscOb.{v} A where
  toFunctor := u.toFunctor ⋙ X.toFunctor
  isDiscrete a := X.isDiscrete (u.toFunctor.obj a)

/-- The chosen lift of `u` at `X`: that of the category model at its lift. -/
def clift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : IDiscOb.{v} B) :
    SmallIDisc.Hom u (pull u X) X :=
  Fib.clift (D := ICatLax) u (CatModel.lift X.toFunctor)

/-- The chosen lift is cartesian, since it is in the category model and the morphisms are the
same. -/
def isCartesianClift {A B : Cat.{v + 1, v + 1}} (u : A ⟶ B) (X : IDiscOb.{v} B) :
    IsCartesian (D := SmallIDisc) (clift u X) :=
  let H := Fib.isCartesianClift (D := ICatLax) u (CatModel.lift X.toFunctor)
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end SmallIDisc

/-- **`SmallIDisc` is a split fibration**, reindexing by precomposition, with the chosen lifts of
the category model. -/
instance SmallIDisc.preSplitFib : PreSplitFib SmallIDisc.{v} where
  pull u X := SmallIDisc.pull u X
  clift u X := SmallIDisc.clift u X
  isCartesianClift u X := SmallIDisc.isCartesianClift u X

instance SmallIDisc.splitFib : SplitFib SmallIDisc.{v} := {}

/-- **The lift into the category model**, a vertical cartesian functor. -/
def SmallIDisc.lift : CartesianFunctor (𝟭 Cat.{v + 1, v + 1}) SmallIDisc.{v} ICatLax.{v + 1} where
  toPre :=
    { obj A := CatModel.lift A.toFunctor
      map φ := φ }

/-- **The lift is fully faithful**, since the morphisms are those of the category model. -/
def SmallIDisc.liftFullyFaithful : VertFunctor.FullyFaithful SmallIDisc.lift.{v}.toDispFunctor where
  preimage φ := φ

/-- The comprehension structure of the discrete types of level `v`: that of the category model,
along the lift. -/
@[instance_reducible]
instance SmallIDisc.comprehension : Comprehension SmallIDisc.{v} :=
  Comprehension.comap SmallIDisc.lift.toDispFunctor SmallIDisc.lift.isCartesianMap

/-- **The discrete types of level `v`** form a full split comprehension category. -/
instance SmallIDisc.splitComprehension : SplitComprehension SmallIDisc.{v} := {}

@[instance_reducible]
instance SmallIDisc.fullComprehension : FullComprehension SmallIDisc.{v} where
  comprFullyFaithful := SmallIDisc.liftFullyFaithful.comp comprFullyFaithful

end ComprehensionCategory.DiscreteModel
