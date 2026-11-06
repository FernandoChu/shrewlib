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

universe u w

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- A functor `A ⥤ Cat` into discrete categories. The categories may be smaller than `A`: they are
in `Cat.{u, u}`, and `A` in `Cat.{w, w}`. -/
structure IDiscOb (A : Cat.{w, w}) where
  /-- The functor. -/
  toFunctor : A ⥤ Cat.{u, u}
  /-- Its values are discrete. -/
  isDiscrete : ∀ a, IsDiscrete (toFunctor.obj a)

/-- Two functors into discrete categories are equal if their functors are, since discreteness is a
proposition. -/
theorem IDiscOb.ext {A : Cat.{w, w}} {X Y : IDiscOb.{u} A} (h : X.toFunctor = Y.toFunctor) :
    X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- The indexed discrete categories, displayed over `Cat`: the full subcategory of `ICatLax` on the
functors into discrete categories. -/
def IDisc : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := IDiscOb.{u} A
  Hom u X Y := ICatLax.Hom u X.toFunctor Y.toFunctor
  id X := ICatLax.id X.toFunctor
  comp φ ψ := ICatLax.comp φ ψ

namespace IDisc

/-- Reindexing `pull u X` of `X` along `u : A ⟶ B`: the reindexing of `ICatLax`, whose values are
those of `X`. -/
def pull {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) : IDiscOb.{u} A where
  toFunctor := Fib.pull (D := ICatLax) u X.toFunctor
  isDiscrete a := X.isDiscrete (u.toFunctor.obj a)

/-- The cartesian lift `pull u X ⟶[u] X`: that of `ICatLax`. -/
def clift {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) : IDisc.Hom u (pull u X) X :=
  Fib.clift (D := ICatLax) u X.toFunctor

/-- The chosen lift is cartesian, since it is in `ICatLax` and the morphisms are the same. -/
def isCartesianClift {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) :
    IsCartesian (clift u X) :=
  let H := Fib.isCartesianClift (D := ICatLax) u X.toFunctor
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end IDisc

/-- **`IDisc` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`ICatLax`. -/
instance IDisc.preSplitFib : PreSplitFib IDisc.{u} where
  pull u X := IDisc.pull u X
  clift u X := IDisc.clift u X
  isCartesianClift u X := IDisc.isCartesianClift u X

instance IDisc.splitFib : SplitFib IDisc.{u} := {}

/-- **Forgetting the discreteness**, a vertical cartesian functor `IDisc ⟶ ICatLax`: the inclusion
of the full subcategory. -/
def IDisc.forget : CartesianFunctor (𝟭 Cat.{u, u}) IDisc.{u} ICatLax.{u} where
  toPre :=
    { obj X := X.toFunctor
      map φ := φ }

/-- **Forgetting the discreteness is fully faithful**, since the morphisms are the same. -/
def IDisc.forgetFullyFaithful : VertFunctor.FullyFaithful IDisc.forget.{u}.toDispFunctor where
  preimage φ := φ

end Displayed.Discrete.Straightening
