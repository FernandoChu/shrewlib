import Straightening.DCat

/-!
# Unstraightening and straightening as displayed functors over `Cat`

* `unstraighten : DFunctor DCat Arr` is `(▷ᵈ)*`: it sends `F : LaxNormal A` to the projection
  `π : Unstraightening F ⥤ A`, and a transformation with representable components over `u` to
  the induced functor `(a, x) ↦ (u a, h x)`, `(f, s) ↦ (u f, map s)`. The square commutes by `rfl`.
* `straighten : DFunctor Arr DCat` sends `p : E ⥤ A` to the lax normal functor of its fibres,
  `a ↦ Fib p a = {e // p e = a}`, with `F_p f x y` the morphisms of `E` over `f` and composition as
  the composition constraint. A commuting square `w ⋙ p' = p ⋙ u` is sent to the restriction of
  `w` to the fibres.

The functoriality of both holds by `rfl`.
-/

universe u

namespace Straightening

open CategoryTheory Bicategory Nfib Displayed Unstraightening

open scoped Displayed

/-! ## Unstraightening -/

/-- `(▷ᵈ)*` on objects: the projection of the unstraightening. -/
def unstraightenObj {A : Cat.{u, u}} (F : LaxNormal A) : ArrOb A :=
  ⟨Cat.of (Unstraightening F), Unstraightening.π⟩

/-- `(▷ᵈ)*` on morphisms: the functor induced by a transformation with representable components. -/
def unstraightenFunctor {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A} {G : LaxNormal B}
    (φ : ReprHom u F G) : Unstraightening F ⥤ Unstraightening G where
  obj X := ⟨u.toFunctor.obj X.base, φ.obj X.fiber⟩
  map g := ⟨u.toFunctor.map g.base, φ.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The unstraightening functor `(▷ᵈ)* : DCat → Cat^→` over `Cat`.** -/
def unstraighten : DFunctor DCat.{u} Arr.{u} where
  obj F := unstraightenObj F
  map φ := ⟨unstraightenFunctor φ, rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## Straightening -/

section Straighten

variable {A : Cat.{u, u}} (X : ArrOb A)

/-- The fibre of `p : E ⥤ A` over `a`, on objects. -/
def Fib (a : A) : Type u := { e : X.dom // X.proj.obj e = a }

/-- The morphisms of `E` over `f`, between objects of the fibres. -/
def FibHom {a a' : A} (f : a ⟶ a') (x : Fib X a) (y : Fib X a') : Type u :=
  { g : x.1 ⟶ y.1 // X.proj.map g ≫ eqToHom y.2 = eqToHom x.2 ≫ f }

variable {X}

/-- Composition of morphisms over base morphisms. -/
def FibHom.comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fib X a} {y : Fib X a'}
    {z : Fib X a''} (s : FibHom X f x y) (t : FibHom X g y z) : FibHom X (f ≫ g) x z :=
  ⟨s.1 ≫ t.1, ((congrArg (X.proj.map s.1 ≫ ·) t.2).trans (congrArg (· ≫ g) s.2) :)⟩

/-- A morphism over `f` lies over `f` up to the identifications of the fibres. -/
theorem FibHom.proj_map {a a' : A} {f : a ⟶ a'} {x : Fib X a} {y : Fib X a'}
    (s : FibHom X f x y) : X.proj.map s.1 = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  exact s.2

instance (a : A) : SmallCategory (Fib X a) where
  Hom := FibHom X (𝟙 a)
  id x := ⟨𝟙 x.1, rfl⟩
  comp s t := FibHom.comp s t
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- The profunctor `F_p f : Fib p a ⇸ Fib p a'` of morphisms over `f`. -/
def fibProf {a a' : A} (f : a ⟶ a') : Profunctor (Fib X a) (Fib X a') where
  obj := FibHom X f
  lmap k s := FibHom.comp k s
  rmap k s := FibHom.comp s k
  lmap_id := by intros; rfl
  lmap_comp := by intros; rfl
  rmap_id := by intros; rfl
  rmap_comp := by intros; rfl
  rmap_lmap _ _ _ := rfl

/-- The composition constraint `F_p f ⊗ F_p g ⟶ F_p (f ≫ g)`: composition in `E`. -/
def fibMul {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    Profunctor.Hom (Profunctor.comp (fibProf (X := X) f) (fibProf g)) (fibProf (f ≫ g)) where
  app _ _ := Profunctor.CompObj.lift (fun _ s t => FibHom.comp s t) (fun _ _ _ => rfl)
  app_lmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl
  app_rmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl

variable (X) in
/-- **The straightening of `p : E ⥤ A`**: the lax normal functor of its fibres. -/
def straightenObj : LaxNormal A where
  obj a := ProfCat.of (Fib X a.as)
  map f := fibProf f.as
  map₂ η := eqToHom (congrArg (fun k => fibProf (X := X) k.as) (LocallyDiscrete.eq_of_hom η))
  map₂_id _ := rfl
  map₂_comp η θ := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := LocallyDiscrete.eq_of_hom θ
    rfl
  mapId _ := 𝟙 _
  mapComp f g := fibMul f.as g.as
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

/-- The composition constraint of `straightenObj X` is composition in `E`. -/
theorem straightenObj_mul {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fib X a}
    {y : Fib X a'} {z : Fib X a''} (s : FibHom X f x y) (t : FibHom X g y z) :
    mul (F := straightenObj X) s t = FibHom.comp s t :=
  rfl

/-- A commuting square `w ⋙ p' = p ⋙ u` restricts to the fibres. -/
theorem proj_map_map {B : Cat.{u, u}} {u : A ⟶ B} {Y : ArrOb B} (w : ArrHom u X Y) {a a' : A}
    {f : a ⟶ a'} {x : Fib X a} {y : Fib X a'} (s : FibHom X f x y)
    (hx : Y.proj.obj (w.1.obj x.1) = u.toFunctor.obj a)
    (hy : Y.proj.obj (w.1.obj y.1) = u.toFunctor.obj a') :
    Y.proj.map (w.1.map s.1) ≫ eqToHom hy = eqToHom hx ≫ u.toFunctor.map f := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  obtain ⟨s, hs⟩ := s
  obtain rfl : X.proj.map s = f := hs
  have := Functor.congr_hom w.2 s
  rw [Functor.comp_map] at this
  rw [this]
  exact congrArg (fun t => eqToHom hx ≫ u.toFunctor.map (X.proj.map s) ≫ t)
    ((eqToHom_trans _ hy).trans (eqToHom_refl _ _))

/-- The straightening of a commuting square, on the fibres. -/
def straightenMap {B : Cat.{u, u}} {u : A ⟶ B} {Y : ArrOb B} (w : ArrHom u X Y) :
    ReprHom u (straightenObj X) (straightenObj Y) where
  obj x := ⟨w.1.obj x.1, (Functor.congr_obj w.2 x.1).trans (congrArg u.toFunctor.obj x.2)⟩
  map s := ⟨w.1.map s.1, proj_map_map w s _ _⟩
  map_id _ := rfl
  map_mul _ _ := rfl

end Straighten

/-- **The straightening functor `Cat^→ → DCat` over `Cat`.** -/
def straighten : DFunctor Arr.{u} DCat.{u} where
  obj X := straightenObj X
  map w := straightenMap w
  map_id _ := rfl
  map_comp _ _ := rfl

end Straightening
