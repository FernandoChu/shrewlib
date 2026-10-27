import Displayed.Displayed.Straightening.DCat
import Displayed.Displayed.Total

/-!
# Unstraightening of a lax normal functor into `ProfCat`

A lax normal functor `F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat` out of a category
`C`, viewed as the locally discrete bicategory `LocallyDiscrete C`, unstraightens to a category
`Unstraightening F` over `C`:

* an object is a pair `(c, x)` of `c : C` and `x : F c`;
* a morphism `(c, x) ⟶ (c', y)` is a pair `(f, u)` of `f : c ⟶ c'` and `u : F f x y`;
* the identity of `(c, x)` is `(𝟙 c, 𝟙 x)`;
* the composite of `(f, u)` and `(g, v)` is `(f ≫ g, mul u v)`, where `mul` is the composition
  constraint `F.mapComp f g` of `F` on elements.

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
fibre over `c`.

Finally, `unstraighten : VertFunctor DCat (cod Cat)` sends `F : LaxNormal A` to the
projection `π : Unstraightening F ⥤ A`, and a transformation with representable components over
`u` to the induced functor `(a, x) ↦ (u a, obj x)`, `(f, s) ↦ (u f, map s)`. The square commutes,
and the functor laws hold, by `rfl`.
-/

open CategoryTheory Bicategory Profunctor

open scoped Displayed

universe v₁ u₁ u

namespace Displayed.Straightening

variable {C : Type u₁} [Category.{v₁} C]

/-- The unstraightening of a lax normal functor `F` from `C` to `ProfCat`. -/
structure Unstraightening (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) where
  /-- The object of `C` over which this object lies. -/
  base : C
  /-- The object of the fibre `F base`. -/
  fiber : F.obj ⟨base⟩

namespace Unstraightening

variable {F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}}

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
    change Hom.mk (X := ⟨c, x⟩) (Y := ⟨c, z⟩) (𝟙 c) (h ≫ h') = Hom.mk (𝟙 c ≫ 𝟙 c) (mul h h')
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

/-! ## Unstraightening -/

/-- `unstraighten` on objects: the projection of the unstraightening. -/
def unstraightenObj {A : Cat.{u, u}} (F : LaxNormal A) : (cod Cat.{u, u}).Ob A :=
  ⟨Cat.of (Unstraightening F), Unstraightening.π.toCatHom⟩

/-- `unstraighten` on morphisms: the functor induced by a transformation with representable
components. -/
def unstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A} {G : LaxNormal B}
    (φ : ReprHom u F G) : Unstraightening F ⥤ Unstraightening G where
  obj X := ⟨u.toFunctor.obj X.base, φ.obj X.fiber⟩
  map g := ⟨u.toFunctor.map g.base, φ.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `unstraighten` on morphisms, as a commuting square over `u`. -/
def unstraightenHom {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A} {G : LaxNormal B}
    (φ : ReprHom u F G) : unstraightenObj F ⟶[u] unstraightenObj G :=
  ⟨(unstraightenMap φ).toCatHom, rfl⟩

/-- **The unstraightening functor `unstraighten : VertFunctor DCat (cod Cat)`.** -/
def unstraighten : VertFunctor DCat.{u} (cod Cat.{u, u}) where
  obj F := unstraightenObj F
  map φ := unstraightenHom φ
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Straightening
