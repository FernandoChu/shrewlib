import Displayed.Fibration.CartesianFunctor
import Displayed.Opfibration.Straightening.ICat
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Indexed discrete categories

The indexed discrete categories are displayed over `Cat` (`IDisc`): an object over `A` is a functor
`A ⥤ Cat` whose values are discrete categories (`IDiscOb A`), and a morphism over `u : A ⟶ B` is a
morphism of `ICat` over `u` between the underlying functors, a lax transformation. So `IDisc` is the
full subcategory of `ICat` on the functors into discrete categories. Discreteness is Mathlib's
`IsDiscrete`, a proposition, so two objects with the same functor are equal by proof irrelevance.

Reindexing preserves discreteness, so `IDisc` is a split fibration over `Cat` with the reindexing
and the chosen lifts of `ICat`, whose laws hold by `rfl` through the rules for `ICat`. Forgetting
the discreteness is a fully faithful cartesian functor `IDisc.forget : IDisc ⟶ ICat`, whose axioms
hold by `rfl`.

A discrete category is a set, but the objects are not functors into sets: they keep their
category structure. So a construction on `ICat` that preserves discreteness gives one on `IDisc`
that `IDisc.forget` preserves on the nose: it is computed in `ICat`, on the same data. This is how
the straightening of discrete opfibrations is that of split opfibrations (`Equivalence`), and how
the discrete model gets its Σ-types (`ComprehensionCategory/Model/OverCat/Discrete`).
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

/-- The indexed discrete categories, displayed over `Cat`: the full subcategory of `ICat` on the
functors into discrete categories. -/
def IDisc : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := IDiscOb.{u} A
  Hom u X Y := ICat.Hom u X.toFunctor Y.toFunctor
  id X := ICat.id X.toFunctor
  comp φ ψ := ICat.comp φ ψ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace IDisc

/-- Reindexing `pull u X` of `X` along `u : A ⟶ B`: the reindexing of `ICat`, whose values are
those of `X`. -/
def pull {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) : IDiscOb.{u} A where
  toFunctor := Fib.pull (D := ICat) u X.toFunctor
  isDiscrete a := X.isDiscrete (u.toFunctor.obj a)

/-- The cartesian lift `pull u X ⟶[u] X`: that of `ICat`. -/
def clift {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) : IDisc.Hom u (pull u X) X :=
  Fib.clift (D := ICat) u X.toFunctor

/-- The chosen lift is cartesian, since it is in `ICat` and the morphisms are the same. -/
def isCartesianClift {A B : Cat.{u, u}} (u : A ⟶ B) (X : IDiscOb.{u} B) :
    IsCartesian (clift u X) :=
  let H := Fib.isCartesianClift (D := ICat) u X.toFunctor
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end IDisc

/-- **`IDisc` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`ICat`. -/
instance IDisc.preSplitFib : PreSplitFib IDisc.{u} where
  pull u X := IDisc.pull u X
  clift u X := IDisc.clift u X
  isCartesianClift u X := IDisc.isCartesianClift u X
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

instance IDisc.splitFib : SplitFib IDisc.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

/-- **Forgetting the discreteness**, a vertical cartesian functor `IDisc ⟶ ICat`: the inclusion of
the full subcategory. -/
def IDisc.forget : CartesianFunctor (𝟭 Cat.{u, u}) IDisc.{u} ICat.{u} where
  toPre :=
    { obj X := X.toFunctor
      map φ := φ
      map_id _ := rfl
      map_comp _ _ := rfl
      obj_pull _ _ := rfl }
  map_clift _ _ := rfl

/-- **Forgetting the discreteness is fully faithful**, since the morphisms are the same. -/
def IDisc.forgetFullyFaithful : VertFunctor.FullyFaithful IDisc.forget.{u}.toDispFunctor where
  preimage φ := φ
  map_preimage _ := rfl
  preimage_map _ := rfl

end Displayed.Discrete.Straightening
