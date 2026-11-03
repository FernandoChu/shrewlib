import Displayed.Straightening.LaxNormalCat
import Displayed.Displayed.DisplayedCat

/-!
# Unstraightening of a lax normal functor into `ProfCat`

A lax normal functor `F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat` out of a category
`C`, viewed as the locally discrete bicategory `LocallyDiscrete C`, unstraightens to a category
`unstraightenObj F` displayed over `C`:

* the objects over `c` are the objects of `F c`;
* the morphisms over `f : c ⟶ c'` from `x` to `y` are the elements `u : F f x y`;
* the identity of `x` is `𝟙 x`;
* the composite of `u` over `f` and `v` over `g` is `mul u v`, where `mul` is the composition
  constraint `F.mapComp f g` of `F` on elements.

The rewrite rules below make the structure of `F` computational:

* normality, `F (𝟙 c) = 𝟙 (F c)`, and its unit `F.mapId c = eqToHom _` hold definitionally, so
  `F (𝟙 c) x y` *is* `x ⟶ y` and the unit of `F` is the identity;
* `F.map₂` preserves identities definitionally; since the 2-cells of `LocallyDiscrete C` are
  `eqToHom`s between definitionally equal 1-cells, `F` sends them all to identities;
* composition of 1-cells in `LocallyDiscrete C` computes in `C`, so together with the category
  rules of `Profunctor` the bases of composites such as `(f ≫ g) ≫ h` and `f ≫ g ≫ h`, or
  `𝟙 c ≫ f` and `f`, agree definitionally.

As a result the laws of the displayed category are exactly the unit and associativity laws of `F`
evaluated at elements, with no `eqToHom` or `cast` anywhere. Its total category is the
Grothendieck construction of `F` on profunctors.

Finally, `unstraighten : VertFunctor LaxNormalCat DisplayedCat` sends `F : LaxNormal A` to
`unstraightenObj F`, and a transformation with representable components over `u` to the displayed
functor over `u` with the same components. Its laws hold by `rfl`.
-/

open CategoryTheory Bicategory Profunctor

open scoped Displayed

universe v₁ u₁ u

namespace Displayed.Straightening

/-- **The unstraightening of a lax normal functor** `F` from `C` to `ProfCat`, displayed over
`C`. -/
def unstraightenObj {C : Type u₁} [Category.{v₁} C]
    (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) :
    Displayed.{v₁, u₁, u, u} C where
  Ob c := F.obj ⟨c⟩
  Hom f x y := (prof F f).obj x y
  id x := 𝟙 x
  comp u v := mul u v
  id_comp u := id_mul _ u
  comp_id u := mul_id _ u
  assoc u v w := mul_assoc _ _ _ u v w

/-- `unstraighten` on morphisms: the displayed functor of a transformation with representable
components. -/
def unstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A} {G : LaxNormal B}
    (φ : ReprHom u F G) : DisplayedCat.Hom u (unstraightenObj F) (unstraightenObj G) where
  obj x := φ.obj x
  map s := φ.map s
  map_id x := φ.map_id x
  map_comp s t := φ.map_mul s t

/-- **The unstraightening functor `unstraighten : VertFunctor LaxNormalCat DisplayedCat`.** -/
def unstraighten : VertFunctor LaxNormalCat.{u} DisplayedCat.{u} where
  obj F := unstraightenObj F
  map φ := unstraightenMap φ
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Straightening
