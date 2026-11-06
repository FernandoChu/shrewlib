import Displayed.Fibration.CartesianFunctor
import Displayed.Opfibration.Straightening.ICatLax
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Indexed discrete categories

The indexed discrete categories are displayed over `Cat` (`IDisc`): an object over `A` is a functor
`A ⥤ Cat` whose values are discrete categories (`IDiscOb A`), and a morphism over `u : A ⟶ B` is a
morphism of `ICatLax` over `u` between the underlying functors, a lax transformation. So `IDisc` is
the full subcategory of `ICatLax` on the functors into discrete categories. Discreteness is
Mathlib's `IsDiscrete`, a proposition, so two objects with the same functor are equal by proof
irrelevance.

Reindexing preserves discreteness, so `IDisc` is a split fibration over `Cat` with the reindexing
and the chosen lifts of `ICatLax`, whose laws hold by `rfl` through the rules for `ICatLax`.
Forgetting the discreteness is a fully faithful cartesian functor `IDisc.forget : IDisc ⟶ ICatLax`,
whose axioms hold by `rfl`.

A discrete category is a set, but the objects are not functors into sets: they keep their
category structure. So a construction on `ICatLax` that preserves discreteness gives one on `IDisc`
that `IDisc.forget` preserves on the nose: it is computed in `ICatLax`, on the same data. This is
how the straightening of discrete opfibrations is that of split opfibrations (`Equivalence`), and
how the discrete model gets its Σ-types (`ComprehensionCategory/Model/OverCat/Discrete`).
-/

universe v₂ u₂ v₁ u₁

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- A functor `A ⥤ Cat` into discrete categories. The categories are in `Cat.{v₂, u₂}`, and `A` in
`Cat.{v₁, u₁}`. -/
structure IDiscOb (A : Cat.{v₁, u₁}) where
  /-- The functor. -/
  toFunctor : A ⥤ Cat.{v₂, u₂}
  /-- Its values are discrete. -/
  isDiscrete : ∀ a, IsDiscrete (toFunctor.obj a)

/-- Two functors into discrete categories are equal if their functors are, since discreteness is a
proposition. -/
theorem IDiscOb.ext {A : Cat.{v₁, u₁}} {X Y : IDiscOb.{v₂, u₂} A} (h : X.toFunctor = Y.toFunctor) :
    X = Y := by
  cases X
  cases Y
  cases h
  rfl

-- The universes of the discrete categories only occur in the levels of `IDisc` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The indexed discrete categories, displayed over `Cat`: the full subcategory of `ICatLax` on the
functors into discrete categories. -/
def IDisc : Displayed Cat.{v₁, u₁} where
  Ob A := IDiscOb.{v₂, u₂} A
  Hom u X Y := ICatLax.Hom u X.toFunctor Y.toFunctor
  id X := ICatLax.id X.toFunctor
  comp φ ψ := ICatLax.comp φ ψ

namespace IDisc

/-- Reindexing `pull u X` of `X` along `u : A ⟶ B`: the reindexing of `ICatLax`, whose values are
those of `X`. -/
def pull {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : IDiscOb.{v₂, u₂} B) : IDiscOb.{v₂, u₂} A where
  toFunctor := Fib.pull (D := ICatLax) u X.toFunctor
  isDiscrete a := X.isDiscrete (u.toFunctor.obj a)

/-- The cartesian lift `pull u X ⟶[u] X`: that of `ICatLax`. -/
def clift {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : IDiscOb.{v₂, u₂} B) : IDisc.Hom u (pull u X) X :=
  Fib.clift (D := ICatLax) u X.toFunctor

/-- The chosen lift is cartesian, since it is in `ICatLax` and the morphisms are the same. -/
def isCartesianClift {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : IDiscOb.{v₂, u₂} B) :
    IsCartesian (clift u X) :=
  let H := Fib.isCartesianClift (D := ICatLax) u X.toFunctor
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end IDisc

/-- **`IDisc` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`ICatLax`. -/
instance IDisc.preSplitFib : PreSplitFib IDisc.{v₂, u₂, v₁, u₁} where
  pull u X := IDisc.pull u X
  clift u X := IDisc.clift u X
  isCartesianClift u X := IDisc.isCartesianClift u X

instance IDisc.splitFib : SplitFib IDisc.{v₂, u₂, v₁, u₁} := {}

/-- **Forgetting the discreteness**, a vertical cartesian functor `IDisc ⟶ ICatLax`: the inclusion
of the full subcategory. -/
def IDisc.forget :
    CartesianFunctor (𝟭 Cat.{v₁, u₁}) IDisc.{v₂, u₂, v₁, u₁} ICatLax.{v₂, u₂, v₁, u₁} where
  toPre :=
    { obj X := X.toFunctor
      map φ := φ }

/-- **Forgetting the discreteness is fully faithful**, since the morphisms are the same. -/
def IDisc.forgetFullyFaithful :
    VertFunctor.FullyFaithful IDisc.forget.{v₂, u₂, v₁, u₁}.toDispFunctor where
  preimage φ := φ

end Displayed.Discrete.Straightening
