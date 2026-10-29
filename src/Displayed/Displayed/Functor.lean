import Displayed.Displayed.Total
import Rules.Functor
import Mathlib.CategoryTheory.EqToHom

/-!
# Displayed functors over a functor

For a functor `u : A ⥤ B`, a displayed functor `DispFunctor u D E` from `D` over `A` to `E` over
`B` sends objects over `a` to objects over `u a`, and morphisms over `f` to morphisms over `u f`,
functorially. Its laws are stated with the functor laws of `u` as rules, so that `u (𝟙 a)` is
`𝟙 (u a)` and `u (f ≫ g)` is `u f ≫ u g`; this file imports `Rules.Functor`.

Over the identity, these are the vertical functors `VertFunctor`. Displayed functors compose over
the composite functor (`DispFunctor.comp`), with laws holding by `rfl`, and induce functors
between the total categories over `u` (`DispFunctor.total`).

A functor `Z ⥤ E.Total` over `v : Z ⥤ B` is given by its displayed components (`TotalLift`); those
of a functor `W` with `W ⋙ π = v` are obtained by substituting this equation
(`TotalLift.ofFunctor`). Over `D.π ⋙ u`, such a lift is a displayed functor from `D` to `E` over
`u` (`TotalLift.toDispFunctor`).
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A displayed functor over `u : A ⥤ B`: objects over `a` go to objects over `u a`, and
morphisms over `f` to morphisms over `u f`. -/
structure DispFunctor (u : A ⥤ B) (D : Displayed.{v₁, u₁, v₃, u₃} A)
    (E : Displayed.{v₂, u₂, v₄, u₄} B) where
  /-- The action on objects. -/
  obj : {a : A} → D.Ob a → E.Ob (u.obj a)
  /-- The action on morphisms, over the image of the base morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : D.Ob a} → {y : D.Ob a'} → (x ⟶[f] y) →
    (obj x ⟶[u.map f] obj y)
  map_id : ∀ {a : A} (x : D.Ob a), map (𝟙ᵈ x) = 𝟙ᵈ (obj x)
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z), map (φ ≫ᵈ ψ) = map φ ≫ᵈ map ψ

attribute [rewrite_rule] DispFunctor.map_id DispFunctor.map_comp

namespace DispFunctor

variable {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₃, u₃} A} {E : Displayed.{v₂, u₂, v₄, u₄} B}

/-- Displayed functors are determined by their actions on objects and morphisms. -/
theorem ext {H K : DispFunctor u D E} (hobj : ∀ {a : A} (x : D.Ob a), H.obj x = K.obj x)
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
      H.map φ ≍ K.map φ) : H = K := by
  obtain ⟨obj, map, _, _⟩ := H
  obtain ⟨obj', map', _, _⟩ := K
  obtain rfl : @obj = @obj' := by
    funext a x
    exact hobj x
  obtain rfl : @map = @map' := by
    funext a a' f x y φ
    exact eq_of_heq (hmap φ)
  rfl

/-- The identity displayed functor, over the identity functor. -/
protected def id (D : Displayed.{v₁, u₁, v₃, u₃} A) : DispFunctor (𝟭 A) D D where
  obj x := x
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of displayed functors, over the composite functor. -/
def comp {C : Type u₅} [Category.{v₅} C] {v : B ⥤ C} {E' : Displayed.{v₅, u₅, v₆, u₆} C}
    (H : DispFunctor u D E) (K : DispFunctor v E E') : DispFunctor (u ⋙ v) D E' where
  obj x := K.obj (H.obj x)
  map φ := K.map (H.map φ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor between total categories induced by a displayed functor over `u`. -/
def total (H : DispFunctor u D E) : D.Total ⥤ E.Total where
  obj X := ⟨u.obj X.1, H.obj X.2⟩
  map g := ⟨u.map g.base, H.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor induced by a displayed functor over `u` lies over `u`, strictly. -/
theorem total_comp_π (H : DispFunctor u D E) : H.total ⋙ E.π = D.π ⋙ u :=
  rfl

end DispFunctor

/-! ## Functors into a total category over a given base -/

section TotalLift

variable {Z : Type u₅} [Category.{v₅} Z]

/-- A functor `Z ⥤ E.Total` over `v : Z ⥤ B`, given by its displayed components:
`obj X : E (v X)` and `map k : obj X ⟶[v k] obj Y`, functorially. -/
structure TotalLift (v : Z ⥤ B) (E : Displayed.{v₂, u₂, v₃, u₃} B) where
  /-- The displayed components of the objects. -/
  obj : ∀ X, E.Ob (v.obj X)
  /-- The displayed components of the morphisms. -/
  map : ∀ {X Y : Z} (k : X ⟶ Y), obj X ⟶[v.map k] obj Y
  map_id : ∀ X, map (𝟙 X) = 𝟙ᵈ (obj X)
  map_comp : ∀ {X Y W : Z} (k : X ⟶ Y) (l : Y ⟶ W), map (k ≫ l) = map k ≫ᵈ map l

namespace TotalLift

variable {v : Z ⥤ B} {E : Displayed.{v₂, u₂, v₃, u₃} B}

/-- The functor `Z ⥤ E.Total` of a lift, `X ↦ ⟨v X, obj X⟩`. -/
def functor (s : TotalLift v E) : Z ⥤ E.Total where
  obj X := ⟨v.obj X, s.obj X⟩
  map k := ⟨v.map k, s.map k⟩
  map_id X := congrArg (Total.Hom.mk (x := ⟨v.obj X, s.obj X⟩) (y := ⟨v.obj X, s.obj X⟩)
    (v.map (𝟙 X))) (s.map_id X)
  map_comp {X _ W} k l := congrArg (Total.Hom.mk (x := ⟨v.obj X, s.obj X⟩)
    (y := ⟨v.obj W, s.obj W⟩) (v.map (k ≫ l))) (s.map_comp k l)

theorem functor_comp_π (s : TotalLift v E) : s.functor ⋙ E.π = v := rfl

/-- The lift of a functor `W : Z ⥤ E.Total` over `v`: its displayed components, once the equation
`W ⋙ π = v` is substituted. -/
def ofFunctor (W : Z ⥤ E.Total) (h : W ⋙ E.π = v) : TotalLift v E := by
  subst h
  exact { obj X := (W.obj X).2
          map k := (W.map k).fiber
          map_id _ := rfl
          map_comp _ _ := rfl }

/-- Every functor over `v` is the functor of its lift. -/
theorem functor_ofFunctor (W : Z ⥤ E.Total) (h : W ⋙ E.π = v) : (ofFunctor W h).functor = W := by
  subst h
  rfl

/-- A lift over `D.π ⋙ u` is a displayed functor over `u`. -/
def toDispFunctor {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₃, u₃} A}
    {E : Displayed.{v₂, u₂, v₄, u₄} B} (s : TotalLift (D.π ⋙ u) E) : DispFunctor u D E where
  obj x := s.obj (D.tot x)
  map {_ _ f _ _} φ := s.map (D.totalMk f φ)
  map_id x := s.map_id (D.tot x)
  map_comp {_ _ _ f g _ _ _} φ ψ := s.map_comp (D.totalMk f φ) (D.totalMk g ψ)

theorem toDispFunctor_total {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₃, u₃} A}
    {E : Displayed.{v₂, u₂, v₄, u₄} B} (s : TotalLift (D.π ⋙ u) E) :
    s.toDispFunctor.total = s.functor :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end TotalLift

end TotalLift

end Displayed
