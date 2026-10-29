import Displayed.Displayed.Functor

/-!
# The codomain displayed category

The arrow category of `C`, displayed over `C` by the codomain: an object over `a` is a morphism
`p : X ⟶ a`, and a morphism over `f : a ⟶ a'` from `p : X ⟶ a` to `q : Y ⟶ a'` is a morphism
`h : X ⟶ Y` with `h ≫ q = p ≫ f`. The laws hold by `rfl`, since the category laws of `C` are rules
and the equation is a proposition. For `C = Cat` it is the arrow
category of `Cat` used in `Displayed/Straightening`. Its cartesian morphisms, the pullback
squares, are in `Displayed/Fibration/Codomain`.

A functor `F : C ⥤ C'` acts on the codomain displayed categories (`codMap F`), by `F.map`.
-/

universe v u v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable (C : Type u) [Category.{v} C]

/-- An object of the codomain displayed category over `a`: a morphism into `a`. -/
@[ext]
structure CodOb (a : C) where
  /-- The domain. -/
  dom : C
  /-- The morphism into `a`. -/
  hom : dom ⟶ a

variable {C}

/-- A morphism of the codomain displayed category over `f : a ⟶ a'`: a commutative square. -/
def CodHom {a a' : C} (f : a ⟶ a') (x : CodOb C a) (y : CodOb C a') : Type v :=
  { h : x.dom ⟶ y.dom // h ≫ y.hom = x.hom ≫ f }

theorem CodHom.ext {a a' : C} {f : a ⟶ a'} {x : CodOb C a} {y : CodOb C a'} {φ ψ : CodHom f x y}
    (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

variable (C)

/-- The codomain displayed category: the arrow category of `C`, displayed over `C` by the
codomain. -/
def cod : Displayed.{v, u, v, max u v} C where
  Ob := CodOb C
  Hom := CodHom
  id x := ⟨𝟙 x.dom, rfl⟩
  comp {_ _ _ f g x y z} φ ψ := ⟨φ.1 ≫ ψ.1, by
    obtain ⟨φ, hφ⟩ := φ
    obtain ⟨ψ, hψ⟩ := ψ
    change φ ≫ ψ ≫ z.hom = x.hom ≫ f ≫ g
    rw [hψ, ← Category.assoc, hφ, Category.assoc]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {C}

namespace cod

@[simp] theorem id_val {a : C} (x : (cod C).Ob a) : (𝟙ᵈ x : x ⟶[𝟙 a] x).1 = 𝟙 x.dom := rfl

@[simp] theorem comp_val {a a' a'' : C} {f : a ⟶ a'} {g : a' ⟶ a''} {x : (cod C).Ob a}
    {y : (cod C).Ob a'} {z : (cod C).Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    (φ ≫ᵈ ψ).1 = φ.1 ≫ ψ.1 := rfl

/-- The commutative square of a morphism of `cod C`. -/
theorem w {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} (φ : x ⟶[f] y) :
    φ.1 ≫ y.hom = x.hom ≫ f :=
  φ.2

end cod

/-! ## Functoriality -/

variable {C' : Type u₂} [Category.{v₂} C']

/-- The action of a functor `F : C ⥤ C'` on the codomain displayed categories, sending `p : X ⟶ a`
to `F.map p`, and a square to its image. -/
def codMap (F : C ⥤ C') : DispFunctor F (cod C) (cod C') where
  obj x := ⟨F.obj x.dom, F.map x.hom⟩
  map φ := ⟨F.map φ.1, (congrArg F.map (cod.w φ) :)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed
