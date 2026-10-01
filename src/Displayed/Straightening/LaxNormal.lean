import Profunctor
import Rules.Bicategory
import Mathlib.CategoryTheory.Category.Cat

/-!
# Lax normal functors into `ProfCat`, on elements

A lax normal (strictly unitary) functor `F : LocallyDiscrete C ⥤ᴸ ProfCat` gives, for each
`f : c ⟶ c'`, a profunctor `prof F f : F c ⇸ F c'`, and its composition constraint acts on
elements as `mul : prof F f x y → prof F g y z → prof F (f ≫ g) x z`. With the rules of
`Rules.Bicategory`, `prof F (𝟙 c) x y` is `x ⟶ y` on the nose, and `mul` satisfies the unit and
associativity laws (`id_mul`, `mul_id`, `mul_assoc`) and restricts to composition on the fibers
(`mul_eq_comp`).
-/

open CategoryTheory Bicategory Profunctor

universe v₁ u₁ u

namespace Displayed.Straightening

/-- Lax normal functors from `A` to the bicategory of categories and profunctors. -/
abbrev LaxNormal (A : Cat.{u, u}) : Type (u + 1) :=
  StrictlyUnitaryLaxFunctor (LocallyDiscrete A) ProfCat.{u}

variable {C : Type u₁} [Category.{v₁} C] {F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}}

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

end Displayed.Straightening
