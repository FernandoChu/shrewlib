import Displayed.Displayed.Total
import Rules.Functor
import Mathlib.CategoryTheory.EqToHom

/-!
# Displayed functors and total categories

Displayed functors `DispFunctor u D E` over a functor `u : A ⥤ B`, with their identities and
composites, are in `Displayed/Displayed/Basic.lean`. A displayed functor induces a functor between
the total categories over `u` (`DispFunctor.total`).

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

namespace DispFunctor

variable {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₃, u₃} A} {E : Displayed.{v₂, u₂, v₄, u₄} B}

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
