import Displayed.Displayed.Straightening.DCat
import Displayed.Displayed.Total

/-!
# Unstraightening and straightening as displayed functors over `Cat`

* `unstraighten : VertFunctor DCat (cod Cat)` sends `F : LaxNormal A` to the
  projection `π : Unstraightening F ⥤ A`, and a transformation with representable components over
  `u` to the induced functor `(a, x) ↦ (u a, obj x)`, `(f, s) ↦ (u f, map s)`. The square commutes
  by `rfl`.
* `straighten : VertFunctor (cod Cat) DCat` sends `p : E ⥤ A` to the lax normal functor of its
  fibres, `a ↦ Fibre X a` of the objects `e` with `p e = a`, with `fibProf f` the profunctor of the
  morphisms of `E` over `f` and composition as the composition constraint. A commuting square
  `w ⋙ p' = p ⋙ u` is sent to the restriction of `w` to the fibres.

The functoriality of both holds by `rfl`.
-/

universe u

namespace Displayed.Straightening

open CategoryTheory Bicategory Displayed

open scoped Displayed Profunctor

/-! ## Straightening -/

section Straighten

variable {A : Cat.{u, u}} (X : (cod Cat.{u, u}).Ob A)

/-- The fibre of `p : E ⥤ A` over `a`, on objects. -/
def Fibre (a : A) : Type u := { e : X.dom // X.hom.toFunctor.obj e = a }

/-- The morphisms of `E` over `f`, between objects of the fibres. -/
def FibreHom {a a' : A} (f : a ⟶ a') (x : Fibre X a) (y : Fibre X a') : Type u :=
  { g : x.1 ⟶ y.1 // X.hom.toFunctor.map g ≫ eqToHom y.2 = eqToHom x.2 ≫ f }

variable {X}

/-- Composition of morphisms over base morphisms. -/
def FibreHom.comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fibre X a} {y : Fibre X a'}
    {z : Fibre X a''} (s : FibreHom X f x y) (t : FibreHom X g y z) : FibreHom X (f ≫ g) x z :=
  ⟨s.1 ≫ t.1, ((congrArg (X.hom.toFunctor.map s.1 ≫ ·) t.2).trans (congrArg (· ≫ g) s.2) :)⟩

/-- A morphism over `f` lies over `f` up to the identifications of the fibres. -/
theorem FibreHom.proj_map {a a' : A} {f : a ⟶ a'} {x : Fibre X a} {y : Fibre X a'}
    (s : FibreHom X f x y) : X.hom.toFunctor.map s.1 = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  exact s.2

instance (a : A) : SmallCategory (Fibre X a) where
  Hom := FibreHom X (𝟙 a)
  id x := ⟨𝟙 x.1, rfl⟩
  comp s t := FibreHom.comp s t
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

variable (X) in
/-- The fibres of `p : E ⥤ A`, displayed over `A`: the objects over `a` are those of
`Fibre p a`, and the morphisms over `f` are the morphisms of `E` over `f`. -/
def fibres : Displayed.{u, u, u, u} A where
  Ob a := Fibre X a
  Hom f x y := FibreHom X f x y
  id x := ⟨𝟙 x.1, rfl⟩
  comp s t := FibreHom.comp s t
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem fibres.comp_val {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fibre X a}
    {y : Fibre X a'} {z : Fibre X a''} (s : (fibres X).Hom f x y) (t : (fibres X).Hom g y z) :
    Subtype.val (s ≫ᵈ t : FibreHom X (f ≫ g) x z) =
      Subtype.val (s : FibreHom X f x y) ≫ Subtype.val (t : FibreHom X g y z) :=
  rfl

/-- Morphisms over equal base morphisms with the same underlying morphism of `E` are
heterogeneously equal. -/
theorem FibreHom.heq_of_val {a a' : A} {f f' : a ⟶ a'} (h : f = f') {x : Fibre X a}
    {y : Fibre X a'} (s : FibreHom X f x y) (t : FibreHom X f' x y) (hv : s.1 = t.1) : s ≍ t := by
  subst h
  exact heq_of_eq (Subtype.ext hv)

/-- The profunctor `Fibre X a ⇸ Fibre X a'` of the morphisms over `f`. -/
def fibProf {a a' : A} (f : a ⟶ a') : Fibre X a ⇸ Fibre X a' where
  obj := FibreHom X f
  lmap k s := FibreHom.comp k s
  rmap k s := FibreHom.comp s k
  lmap_id := by intros; rfl
  lmap_comp := by intros; rfl
  rmap_id := by intros; rfl
  rmap_comp := by intros; rfl
  rmap_lmap _ _ _ := rfl

/-- The composition constraint `Profunctor.comp (fibProf f) (fibProf g) ⟶ fibProf (f ≫ g)`:
composition in `E`. -/
def fibMul {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    Profunctor.Hom (Profunctor.comp (fibProf (X := X) f) (fibProf g)) (fibProf (f ≫ g)) where
  app _ _ := Profunctor.CompObj.lift (fun _ s t => FibreHom.comp s t) (fun _ _ _ => rfl)
  app_lmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl
  app_rmap := by intros; rename_i x; induction x using Profunctor.CompObj.ind; rfl

variable (X) in
/-- **The straightening of `p : E ⥤ A`**: the lax normal functor of its fibres. -/
def straightenObj : LaxNormal A where
  obj a := ProfCat.of (Fibre X a.as)
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
theorem straightenObj_mul {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fibre X a}
    {y : Fibre X a'} {z : Fibre X a''} (s : FibreHom X f x y) (t : FibreHom X g y z) :
    mul (F := straightenObj X) s t = FibreHom.comp s t :=
  rfl

/-- A commuting square `w ⋙ p' = p ⋙ u` restricts to the fibres. -/
theorem proj_map_map {B : Cat.{u, u}} {u : A ⟶ B} {Y : (cod Cat.{u, u}).Ob B} (w : X ⟶[u] Y)
    {a a' : A}
    {f : a ⟶ a'} {x : Fibre X a} {y : Fibre X a'} (s : FibreHom X f x y)
    (hx : Y.hom.toFunctor.obj (w.1.toFunctor.obj x.1) = u.toFunctor.obj a)
    (hy : Y.hom.toFunctor.obj (w.1.toFunctor.obj y.1) = u.toFunctor.obj a') :
    Y.hom.toFunctor.map (w.1.toFunctor.map s.1) ≫ eqToHom hy = eqToHom hx ≫ u.toFunctor.map f := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  obtain ⟨s, hs⟩ := s
  obtain rfl : X.hom.toFunctor.map s = f := hs
  have := Functor.congr_hom (show w.1.toFunctor ⋙ Y.hom.toFunctor = X.hom.toFunctor ⋙ u.toFunctor
    from congrArg Cat.Hom.toFunctor w.2) s
  rw [Functor.comp_map] at this
  rw [this]
  exact congrArg (fun t => eqToHom hx ≫ u.toFunctor.map (X.hom.toFunctor.map s) ≫ t)
    ((eqToHom_trans _ hy).trans (eqToHom_refl _ _))

/-- The straightening of a commuting square, on the fibres. -/
def straightenMap {B : Cat.{u, u}} {u : A ⟶ B} {Y : (cod Cat.{u, u}).Ob B} (w : X ⟶[u] Y) :
    ReprHom u (straightenObj X) (straightenObj Y) where
  obj x := ⟨w.1.toFunctor.obj x.1, (Functor.congr_obj (congrArg Cat.Hom.toFunctor w.2) x.1).trans
    (congrArg u.toFunctor.obj x.2)⟩
  map s := ⟨w.1.toFunctor.map s.1, proj_map_map w s _ _⟩
  map_id _ := rfl
  map_mul _ _ := rfl

end Straighten

/-- **The straightening functor `Cat^→ → DCat` over `Cat`.** -/
def straighten : VertFunctor (cod Cat.{u, u}) DCat.{u} where
  obj X := straightenObj X
  map w := straightenMap w
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Straightening
