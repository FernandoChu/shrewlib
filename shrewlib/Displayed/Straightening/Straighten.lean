import Displayed.Straightening.LaxNormalCat
import Displayed.Displayed.DisplayedCat

/-!
# Straightening of a displayed category

`straighten : VertFunctor DisplayedCat LaxNormalCat` sends `D` over `A` to the lax normal functor of
its fibres, `a ↦ D.Fiber a`, with `dispProf D f` the profunctor of the morphisms of `D` over `f` and
the displayed composition as the composition constraint (`dispMul`). A displayed functor over `u`
is sent to the transformation with the same components.

Its normality holds by `rfl`, since the profunctor of the morphisms over `𝟙 a` is the hom-profunctor
of the fiber, and so does its functoriality.
-/

universe u v₁ u₁

namespace Displayed.Straightening

open CategoryTheory Bicategory Displayed

open scoped Displayed Profunctor

section Straighten

variable {A : Cat.{v₁, u₁}} (D : Displayed.{u, u} A)

/-- The profunctor `D.Fiber a ⇸ D.Fiber a'` of the morphisms over `f`, on which the vertical
morphisms act by displayed composition. -/
def dispProf {a a' : A} (f : a ⟶ a') : D.Fiber a ⇸ D.Fiber a' where
  obj x y := x ⟶[f] y
  lmap k s := k ≫ᵈ s
  rmap k s := s ≫ᵈ k
  lmap_id := by intros; rfl
  lmap_comp := by intros; rfl
  rmap_id := by intros; rfl
  rmap_comp := by intros; rfl
  rmap_lmap _ _ _ := rfl

/-- The composition constraint `Profunctor.comp (dispProf D f) (dispProf D g) ⟶ dispProf D (f ≫ g)`:
displayed composition. -/
def dispMul {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    Profunctor.Hom (Profunctor.comp (dispProf D f) (dispProf D g)) (dispProf D (f ≫ g)) where
  app _ _ := Profunctor.CompObj.lift (fun _ s t => s ≫ᵈ t) (fun _ _ _ => rfl)
  app_lmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl
  app_rmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl

/-- **The straightening of `D`**: the lax normal functor of its fibres. -/
def straightenObj : LaxNormal A where
  obj a := ProfCat.of (D.Fiber a.as)
  map f := dispProf D f.as
  map₂ η := eqToHom (congrArg (fun k => dispProf D k.as) (LocallyDiscrete.eq_of_hom η))
  map₂_id _ := rfl
  map₂_comp η θ := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := LocallyDiscrete.eq_of_hom θ
    rfl
  mapId _ := 𝟙 _
  mapComp f g := dispMul D f.as g.as
  mapComp_naturality_left η g := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    refine Profunctor.hom_ext fun _ _ x => ?_
    induction x using Profunctor.CompObj.ind
    rfl
  mapComp_naturality_right f _ _ η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    refine Profunctor.hom_ext fun _ _ x => ?_
    induction x using Profunctor.CompObj.ind
    rfl
  map₂_associator f g h := by
    refine Profunctor.hom_ext fun _ _ x => ?_
    induction x using Profunctor.CompObj.ind with
    | h _ x _ => induction x using Profunctor.CompObj.ind; rfl
  map₂_leftUnitor f := Profunctor.hom_ext fun _ _ _ => rfl
  map₂_rightUnitor f := Profunctor.hom_ext fun _ _ _ => rfl
  map_id _ := rfl
  mapId_eq_eqToHom _ := rfl

/-- The composition constraint of `straightenObj D` is displayed composition. -/
theorem straightenObj_mul {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (s : x ⟶[f] y) (t : y ⟶[g] z) : mul (F := straightenObj D) s t = s ≫ᵈ t :=
  rfl

variable {D}

/-- The straightening of a displayed functor over `u`: the transformation with the same
components. -/
def straightenMap {B : Cat.{v₁, u₁}} {u : A ⟶ B} {E : Displayed.{u, u} B}
    (H : DisplayedCat.Hom u D E) : ReprHom u (straightenObj D) (straightenObj E) where
  obj x := H.obj x
  map s := H.map s

end Straighten

/-- **The straightening functor `straighten : VertFunctor DisplayedCat LaxNormalCat`.** -/
def straighten : VertFunctor DisplayedCat.{u, u, v₁, u₁} LaxNormalCat.{u, v₁, u₁} where
  obj D := straightenObj D
  map H := straightenMap H

end Displayed.Straightening
