import TwoCategory.Factorization.Comma.Algebras
import TwoCategory.Factorization.Comma.Coalgebras
import TwoCategory.Factorization.Lifting

/-!
# The comma AWFS on `Cat`

Mathlib's comma categories are comma objects in `Cat.{u, u}` (`Comma.isComma`, in
`TwoCategory.Limits.Comma`), so `Cat.{u, u}` has chosen comma objects (`Cat.hasCommas`) and the
comma factorization is an AWFS on it (`catAWFS`): a functor `f : A ⥤ B` factors through the comma
category `f/B = Comma f (𝟭 B)`, whose objects are the triples `(a, b, φ : f a ⟶ b)`, as

* `Lf : A ⥤ f/B`, `a ↦ (a, f a, 𝟙)`, and
* `Rf : f/B ⥤ B`, `(a, b, φ) ↦ b`,

and a square `m = (u, v) : f ⟶ g` acts on comma categories by
`commaMap m : (a, b, φ) ↦ (u a, v b, v φ)`. These hold by `rfl`, on objects and on morphisms
(`lMap_obj`, `commaMap_obj`, …), since the universal property of `Comma f g` holds on the nose.

Comma objects need the objects and morphisms of the categories in the same universe, as do the
comprehension models, which use `Cat.{u, u}`.
-/

open CategoryTheory Bicategory

universe u

namespace CategoryTheory.TwoCategory

/-- **`Cat` has comma objects**: Mathlib's comma categories. -/
instance Cat.hasCommas : HasCommas Cat.{u, u} where
  comma f g := Cat.of (Comma f.toFunctor g.toFunctor)
  commaCone f g := Comma.commaCone f.toFunctor g.toFunctor
  isComma f g := Comma.isComma f.toFunctor g.toFunctor

/-- **The comma AWFS on `Cat`**, whose `L`-coalgebras are the LARIs (`lcoalgEquiv`) and whose
`R`-algebras are the split opfibrations (`Displayed.Opfibration.RAlgebra`). -/
abbrev catAWFS : AWFS Cat.{u, u} :=
  commaAWFS Cat.{u, u}

namespace Arr

variable (f : Arr Cat.{u, u})

/-! ## The factorization on objects and morphisms -/

/-- The comma object `f/B` is the comma category `Comma f (𝟭 B)`. -/
theorem commaObj_eq : f.commaObj = Cat.of (Comma f.hom.toFunctor (𝟭 f.cod)) :=
  rfl

/-- `Lf` on objects: `a ↦ (a, f a, 𝟙)`. -/
@[simp]
theorem lMap_obj (a : f.dom) : f.lMap.toFunctor.obj a = ⟨a, f.hom.toFunctor.obj a, 𝟙 _⟩ :=
  rfl

/-- `Lf` on morphisms: `k ↦ (k, f k)`. -/
@[simp]
theorem lMap_map {a a' : f.dom} (k : a ⟶ a') :
    f.lMap.toFunctor.map k = ⟨k, f.hom.toFunctor.map k, by simp⟩ :=
  rfl

/-- The first leg `q_f : f/B ⥤ A`, `(a, b, φ) ↦ a`. -/
@[simp]
theorem commaCone_left_obj (x : Comma f.hom.toFunctor (𝟭 f.cod)) :
    (HasCommas.commaCone f.hom (𝟙 f.cod)).left.toFunctor.obj x = x.left :=
  rfl

/-- The second leg `Rf : f/B ⥤ B`, `(a, b, φ) ↦ b`. -/
@[simp]
theorem commaCone_right_obj (x : Comma f.hom.toFunctor (𝟭 f.cod)) :
    (HasCommas.commaCone f.hom (𝟙 f.cod)).right.toFunctor.obj x = x.right :=
  rfl

/-- The universal 2-cell `ν_f`, `(a, b, φ) ↦ φ`. -/
@[simp]
theorem commaCone_hom_app (x : Comma f.hom.toFunctor (𝟭 f.cod)) :
    (HasCommas.commaCone f.hom (𝟙 f.cod)).hom.toNatTrans.app x = x.hom :=
  rfl

variable {f} {g : Arr Cat.{u, u}} (m : f ⟶ g)

/-- `commaMap (u, v)` on objects, first component: `(a, b, φ) ↦ u a`. -/
@[simp]
theorem commaMap_obj_left (x : Comma f.hom.toFunctor (𝟭 f.cod)) :
    ((commaMap m).toFunctor.obj x).left = m.left.toFunctor.obj x.left :=
  rfl

/-- `commaMap (u, v)` on objects, second component: `(a, b, φ) ↦ v b`. -/
@[simp]
theorem commaMap_obj_right (x : Comma f.hom.toFunctor (𝟭 f.cod)) :
    ((commaMap m).toFunctor.obj x).right = m.right.toFunctor.obj x.right :=
  rfl

/-- `commaMap (u, v)` on morphisms, first component. -/
@[simp]
theorem commaMap_map_left {x y : Comma f.hom.toFunctor (𝟭 f.cod)} (k : x ⟶ y) :
    ((commaMap m).toFunctor.map k).left = m.left.toFunctor.map k.left :=
  rfl

/-- `commaMap (u, v)` on morphisms, second component. -/
@[simp]
theorem commaMap_map_right {x y : Comma f.hom.toFunctor (𝟭 f.cod)} (k : x ⟶ y) :
    ((commaMap m).toFunctor.map k).right = m.right.toFunctor.map k.right :=
  rfl

end Arr

end CategoryTheory.TwoCategory
