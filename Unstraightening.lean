import Profunctor
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Unstraightening of a lax normal functor into `ProfCat`

A lax normal (strictly unitary) functor `F : C ⥤ᴸ ProfCat` out of a category `C`, viewed as the
locally discrete bicategory `LocallyDiscrete C`, unstraightens to a category `Unstraightening F`
over `C`:

* an object is a pair `(c, x)` of `c : C` and `x : F c`;
* a morphism `(c, x) ⟶ (c', y)` is a pair `(f, u)` of `f : c ⟶ c'` and `u : F f x y`;
* the identity of `(c, x)` is `(𝟙 c, 𝟙 x)`;
* the composite of `(f, u)` and `(g, v)` is `(f ≫ g, μ [u, v])`, where `μ : F f ⊗ F g ⟶ F (f ≫ g)`
  is the composition constraint of `F`.

The rewrite rules below make the structure of `F` computational:

* normality, `F (𝟙 c) = 𝟙 (F c)`, and its unit `F.mapId c = eqToHom _` hold definitionally, so
  `F (𝟙 c) x y` *is* `x ⟶ y` and the unit of `F` is the identity;
* `F.map₂` preserves identities definitionally; since the 2-cells of `LocallyDiscrete C` are
  `eqToHom`s between definitionally equal 1-cells, `F` sends them all to identities;
* composition of 1-cells in `LocallyDiscrete C` computes in `C`, so together with the category
  rules of `Profunctor` the bases of composites such as `(f ≫ g) ≫ h` and `f ≫ g ≫ h`, or
  `𝟙 c ≫ f` and `f`, agree definitionally.

As a result the category laws are exactly the unit and associativity laws of `F` evaluated at
elements, with no `eqToHom` or `cast` anywhere. The projection `π : Unstraightening F ⥤ C` forgets
the second component, and `fiberInclusion c : F c ⥤ Unstraightening F` includes `F c` as the
fibre over `c`. Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory Bicategory Profunctor

attribute [rewrite_rule] StrictlyUnitaryLaxFunctor.map_id StrictlyUnitaryLaxFunctor.mapId_eq_eqToHom
  PrelaxFunctor.map₂_id Quiver.Hom.id_toLoc

universe v₁ u₁ u

variable {C : Type u₁} [Category.{v₁} C]

/-- Composition of 1-cells in `LocallyDiscrete C` computes in `C`. -/
@[rewrite_rule]
theorem LocallyDiscrete.comp_eq_toLoc {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) :
    f ≫ g = (f.as ≫ g.as).toLoc :=
  rfl

/-- The unstraightening of a lax normal functor `F` from `C` to `ProfCat`. -/
structure Unstraightening (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) where
  /-- The object of `C` over which this object lies. -/
  base : C
  /-- The object of the fibre `F base`. -/
  fiber : F.obj ⟨base⟩

namespace Unstraightening

variable {F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}}

/-- The profunctor `F f : F c ⇸ F c'`. -/
abbrev prof (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) {c c' : C}
    (f : c ⟶ c') : Profunctor (F.obj ⟨c⟩) (F.obj ⟨c'⟩) :=
  F.map f.toLoc

/-- Normality: the elements of `F (𝟙 c)` are the morphisms of `F c`, definitionally. -/
theorem prof_id_obj (c : C) (x y : F.obj ⟨c⟩) : (prof F (𝟙 c)).obj x y = (x ⟶ y) :=
  rfl

/-- The composition constraint of `F`, `μ : F f ⊗ F g ⟶ F (f ≫ g)`, on the class of `(u, v)`. -/
abbrev mul {c c' c'' : C} {f : c ⟶ c'} {g : c' ⟶ c''} {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    {z : F.obj ⟨c''⟩} (u : (prof F f).obj x y) (v : (prof F g).obj y z) :
    (prof F (f ≫ g)).obj x z :=
  Profunctor.Hom.app (F.mapComp f.toLoc g.toLoc) x z (CompObj.mk y u v)

theorem id_mul {c c' : C} (f : c ⟶ c') {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    (v : (prof F f).obj x y) : mul (f := 𝟙 c) (𝟙 x) v = v :=
  (congrArg (fun η => Profunctor.Hom.app η x y v) (F.map₂_leftUnitor f.toLoc)).symm

theorem mul_id {c c' : C} (f : c ⟶ c') {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    (u : (prof F f).obj x y) : mul (g := 𝟙 c') u (𝟙 y) = u :=
  (congrArg (fun η => Profunctor.Hom.app η x y u) (F.map₂_rightUnitor f.toLoc)).symm

theorem mul_assoc {c₀ c₁ c₂ c₃ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₂ ⟶ c₃)
    {x : F.obj ⟨c₀⟩} {y : F.obj ⟨c₁⟩} {z : F.obj ⟨c₂⟩} {w : F.obj ⟨c₃⟩}
    (u : (prof F f).obj x y) (v : (prof F g).obj y z) (t : (prof F h).obj z w) :
    mul (mul u v) t = mul u (mul v t) := by
  have e := congrArg
    (fun η => Profunctor.Hom.app η x w
      (CompObj.mk (P := Profunctor.comp (F.map f.toLoc) (F.map g.toLoc)) (Q := F.map h.toLoc) z
        (CompObj.mk y u v) t))
    (F.map₂_associator f.toLoc g.toLoc h.toLoc)
  exact e

/-- On the fibre over `c`, `μ` is the composition of `F c`. -/
theorem mul_eq_comp {c : C} {x y z : F.obj ⟨c⟩} (h : x ⟶ y) (h' : y ⟶ z) :
    mul (f := 𝟙 c) (g := 𝟙 c) h h' = h ≫ h' := by
  -- Writing `h` as `hom.lmap h (𝟙 y)`, which holds by the category rules, lets the naturality
  -- rule of `μ` move `h` out of the coend.
  let μ := F.mapComp (𝟙 c).toLoc (𝟙 c).toLoc
  let P := Profunctor.comp (prof F (𝟙 c)) (prof F (𝟙 c))
  have s₁ : mul (f := 𝟙 c) (g := 𝟙 c) h h' =
      Profunctor.Hom.app μ x z (P.lmap h (CompObj.mk y (𝟙 y) h')) :=
    congrArg (Profunctor.Hom.app μ x z)
      (show CompObj.mk y h h' = P.lmap h (CompObj.mk y (𝟙 y) h') from rfl)
  have s₂ : Profunctor.Hom.app μ x z (P.lmap h (CompObj.mk y (𝟙 y) h')) =
      (prof F (𝟙 c)).lmap h (mul (f := 𝟙 c) (𝟙 y) h') := rfl
  exact s₁.trans (s₂.trans (congrArg ((prof F (𝟙 c)).lmap h) (id_mul (𝟙 c) h')))

/-- A morphism `(c, x) ⟶ (c', y)`: a morphism `f : c ⟶ c'` and an element of `F f x y`. -/
structure Hom (X Y : Unstraightening F) where
  /-- The underlying morphism of `C`. -/
  base : X.base ⟶ Y.base
  /-- The element of `F base` from `X.fiber` to `Y.fiber`. -/
  fiber : (prof F base).obj X.fiber Y.fiber

instance category : Category (Unstraightening F) where
  Hom := Hom
  id X := ⟨𝟙 X.base, 𝟙 X.fiber⟩
  comp φ ψ := ⟨φ.base ≫ ψ.base, mul φ.fiber ψ.fiber⟩
  id_comp φ := congrArg (Hom.mk φ.base) (id_mul φ.base φ.fiber)
  comp_id φ := congrArg (Hom.mk φ.base) (mul_id φ.base φ.fiber)
  assoc φ ψ χ :=
    congrArg (Hom.mk (φ.base ≫ ψ.base ≫ χ.base)) (mul_assoc _ _ _ φ.fiber ψ.fiber χ.fiber)

/-- The projection of the unstraightening onto `C`. -/
def π : Unstraightening F ⥤ C where
  obj X := X.base
  map φ := Hom.base φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The fibres -/

/-- The inclusion of `F c` as the fibre of the unstraightening over `c`. -/
def fiberInclusion (c : C) : F.obj ⟨c⟩ ⥤ Unstraightening F where
  obj x := ⟨c, x⟩
  map h := ⟨𝟙 c, h⟩
  map_id _ := rfl
  map_comp {x _ z} h h' := by
    show Hom.mk (X := ⟨c, x⟩) (Y := ⟨c, z⟩) (𝟙 c) (h ≫ h') = Hom.mk (𝟙 c ≫ 𝟙 c) (mul h h')
    exact congrArg (Hom.mk (X := ⟨c, x⟩) (Y := ⟨c, z⟩) (𝟙 c)) (mul_eq_comp h h').symm

@[simp]
theorem π_obj_fiberInclusion_obj (c : C) (x : F.obj ⟨c⟩) :
    π.obj ((fiberInclusion (F := F) c).obj x) = c :=
  rfl

@[simp]
theorem π_map_fiberInclusion_map (c : C) {x y : F.obj ⟨c⟩} (h : x ⟶ y) :
    π.map ((fiberInclusion (F := F) c).map h) = 𝟙 c :=
  rfl

instance (c : C) : (fiberInclusion (F := F) c).Faithful where
  map_injective {x y} h h' e :=
    eq_of_heq (Hom.mk.inj
      (show Hom.mk (X := ⟨c, x⟩) (Y := ⟨c, y⟩) (𝟙 c) h = Hom.mk (𝟙 c) h' from e)).2

end Unstraightening
