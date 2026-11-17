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

Into discrete categories, every lax transformation is strict, and the 2-cells are unique: a
natural transformation `e : X ⟶ Y` is a vertical morphism `homOfNatTrans e` of `IDisc`, with the
`eqToHom`s of its naturality as 2-cells, and a natural isomorphism an isomorphism of the fiber
(`isoOfNatIso`). Its transport along `u` is the restriction of `e` along `u`
(`pullMap_homOfNatTrans`).

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

/-! ## Natural transformations as vertical morphisms -/

namespace IDisc

variable {A : Cat.{v₁, u₁}} {X Y Z : IDisc.{v₂, u₂}.Fiber A}

/-- The lax transformation of a natural transformation `e : X ⟶ Y` into discrete categories: its
2-cells are the `eqToHom`s of the naturality of `e`, and its laws hold since the morphisms of the
values of `Y` are unique. -/
def laxTransOfNatTrans (e : X.toFunctor ⟶ Y.toFunctor) : LaxTrans X.toFunctor Y.toFunctor where
  app a := (e.app a).toFunctor
  naturality f x :=
    eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (e.naturality f)) x).symm
  naturality_naturality {_ _} _ {_ _} _ :=
    @Subsingleton.elim _ ((Y.isDiscrete _).subsingleton _ _) _ _
  naturality_id _ := @Subsingleton.elim _ ((Y.isDiscrete _).subsingleton _ _) _ _
  naturality_comp _ _ _ := @Subsingleton.elim _ ((Y.isDiscrete _).subsingleton _ _) _ _

/-- **A natural transformation `e : X ⟶ Y` into discrete categories is a vertical morphism** of
`IDisc` over `A`: into discrete categories, every lax transformation is strict. -/
def homOfNatTrans (e : X.toFunctor ⟶ Y.toFunctor) : X ⟶ Y :=
  laxTransOfNatTrans e

/-- `homOfNatTrans` preserves identities. -/
theorem homOfNatTrans_id : homOfNatTrans (𝟙 X.toFunctor) = 𝟙 X :=
  LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) fun _ _ =>
    heq_of_eq (@Subsingleton.elim _ ((X.isDiscrete _).subsingleton _ _) _ _)

/-- `homOfNatTrans` preserves composites. -/
theorem homOfNatTrans_comp (e : X.toFunctor ⟶ Y.toFunctor) (e' : Y.toFunctor ⟶ Z.toFunctor) :
    homOfNatTrans (e ≫ e') = homOfNatTrans e ≫ homOfNatTrans e' :=
  LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) fun _ _ =>
    heq_of_eq (@Subsingleton.elim _ ((Z.isDiscrete _).subsingleton _ _) _ _)

/-- **A natural isomorphism `e : X ≅ Y` into discrete categories is an isomorphism** in the fiber of
`IDisc` over `A`. -/
def isoOfNatIso (e : X.toFunctor ≅ Y.toFunctor) : X ≅ Y where
  hom := homOfNatTrans e.hom
  inv := homOfNatTrans e.inv
  hom_inv_id := (homOfNatTrans_comp _ _).symm.trans
    ((congrArg homOfNatTrans e.hom_inv_id).trans homOfNatTrans_id)
  inv_hom_id := (homOfNatTrans_comp _ _).symm.trans
    ((congrArg homOfNatTrans e.inv_hom_id).trans homOfNatTrans_id)

/-- Heterogeneously equal natural isomorphisms between equal objects give heterogeneously equal
isomorphisms. -/
theorem isoOfNatIso_hcongr {X' Y' : IDisc.{v₂, u₂}.Fiber A} (hX : X = X') (hY : Y = Y')
    {e : X.toFunctor ≅ Y.toFunctor} {e' : X'.toFunctor ≅ Y'.toFunctor} (he : e ≍ e') :
    isoOfNatIso e ≍ isoOfNatIso e' := by
  subst hX hY
  cases he
  rfl

/-- **The transport of `homOfNatTrans e` along `u` is that of the restriction of `e`** along `u`. -/
theorem pullMap_homOfNatTrans {B : Cat.{v₁, u₁}} (u : B ⟶ A) (e : X.toFunctor ⟶ Y.toFunctor) :
    IDisc.pullMap u (homOfNatTrans e) =
      homOfNatTrans (X := IDisc.pull u X) (Y := IDisc.pull u Y)
        (Functor.whiskerLeft u.toFunctor e) := by
  rw [pullMap_eq_lift]
  exact LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) fun _ _ =>
    heq_of_eq (@Subsingleton.elim _ ((Y.isDiscrete _).subsingleton _ _) _ _)

end IDisc

end Displayed.Discrete.Straightening
