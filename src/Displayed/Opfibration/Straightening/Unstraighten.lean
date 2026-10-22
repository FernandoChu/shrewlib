import Displayed.Opfibration.Straightening.ICat
import Tactic.KernelTactic
import Mathlib.CategoryTheory.Grothendieck

/-!
# Unstraightening functors into `Cat`

The unstraightening of `F : A ⥤ Cat` is the projection `π : A ⋉ F ⥤ A` of its Grothendieck
construction, a split opfibration. It is a functor `unstraighten : ICat ⟶ cod Cat` over `Cat`
(`ICat` in `ICat.lean`).

* `A ⋉ F` is Mathlib's `Grothendieck F`: objects are pairs `(a, x)` with `x : F a`, and a morphism
  `(a, x) ⟶ (a', y)` is a pair `(f, φ)` with `φ : F f x ⟶ y`. Its identities and composites carry
  `eqToHom`s along `F (𝟙 a) x = x` and `F (f ≫ g) x = F g (F f x)`, which the functor rules make
  identities, so that, with the category laws as rules too, they are `(𝟙, 𝟙)` and
  `(f ≫ g, F g φ ≫ ψ)` by `rfl`. The projection `π` is `Grothendieck.forget`.
* `Groth.map α`: the functor `A ⋉ F ⥤ B ⋉ G` over `u : A ⥤ B` induced by a lax transformation
  `α : F ⇒ u ⋙ G`, sending `(f, φ)` to `(u f, α_f x ≫ α φ)`.
* `unstraighten : VertFunctor ICat (cod Cat)`, whose functor laws hold by `rfl`.
* It sends the chosen lifts, the identities `u^* G ⟶[u] G`, to cartesian morphisms of `cod Cat`
  (`isCartesianUnstraightenClift`): `A ⋉ u^* G` is the pullback of `B ⋉ G` along `u`.
* A functor `Z ⥤ B ⋉ G` over `v : Z ⥤ B` is given by its fibres (`Groth.Lift`). Those of a
  functor `W` with `W ⋙ π = v` are transported along this equation (`Groth.Lift.ofFunctor`), and
  their laws hold by `rfl` once `v` is substituted.
* It is fully faithful (`unstraightenFullyFaithful`), with an explicit inverse on morphisms
  (`unstraightenPreimage`): a functor `A ⋉ F ⥤ B ⋉ G` over `u` is `Groth.map` of the lax
  transformation read off its fibres on the morphisms `(f, 𝟙)` and `(𝟙, φ)`.
* Transport in `A ⋉ F`: the morphisms `(f, 𝟙)` (`Groth.transport`), as rules, and their action
  under functors out of `A ⋉ F`.

The notation `A ⋉ F` is scoped in `Displayed.Opfibration.Straightening`, as in the paper.

That the unstraightening is faithful is proved without transport: a functor `W` into `B ⋉ G`
whose composite with `π` is known is taken apart into its components, whose bases are then
substituted by the known ones.
-/

universe v₁ u₁ v₂ u₂ v u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open Grothendieck (Hom)

open scoped Displayed

/-! ## The Grothendieck construction -/

section Groth

variable {A : Type u₁} [Category.{v₁} A]

/-- `A ⋉ F` is Mathlib's Grothendieck construction `Grothendieck F` of `F : A ⥤ Cat`. -/
scoped notation:65 Γ:65 " ⋉ " F:66 => Grothendieck (C := Γ) F

open Lean PrettyPrinter Delaborator SubExpr in
/-- Displays `Grothendieck F`, for `F : A ⥤ Cat`, as `A ⋉ F`. -/
@[scoped delab app.CategoryTheory.Grothendieck]
def delabGroth : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let A ← withNaryArg 0 delab
  let F ← withNaryArg 2 delab
  `($A ⋉ $F)

namespace Groth

variable {F : A ⥤ Cat.{v, u}}

/-- Equal morphisms with the same base have equal fibres. -/
theorem fiber_eq_of_eq {X Y : Grothendieck F} {f : X.base ⟶ Y.base}
    {φ ψ : (F.map f).toFunctor.obj X.fiber ⟶ Y.fiber}
    (h : (Hom.mk f φ : X ⟶ Y) = Hom.mk f ψ) : φ = ψ :=
  eq_of_heq (Hom.mk.inj h).2

theorem hom_mk_congr {X Y : Grothendieck F} {f : X.base ⟶ Y.base}
    {φ ψ : (F.map f).toFunctor.obj X.fiber ⟶ Y.fiber} (h : φ = ψ) :
    (Hom.mk f φ : X ⟶ Y) = Hom.mk f ψ :=
  congrArg (Hom.mk f) h

/-- Heterogeneously equal morphisms have heterogeneously equal fibres. -/
theorem fiber_heq {X X' Y Y' : Grothendieck F} (hX : X = X') (hY : Y = Y') {φ : X ⟶ Y} {ψ : X' ⟶ Y'}
    (h : φ ≍ ψ) : Hom.fiber φ ≍ Hom.fiber ψ := by
  subst hX hY
  cases eq_of_heq h
  rfl

/-- Morphisms of `A ⋉ F` are determined by their bases and fibres. -/
theorem Hom.ext' {X Y : Grothendieck F} {φ ψ : X ⟶ Y} (hb : Hom.base φ = Hom.base ψ)
    (hf : Hom.fiber φ ≍ Hom.fiber ψ) : φ = ψ := by
  obtain ⟨b, f⟩ := φ
  obtain ⟨b', f'⟩ := ψ
  dsimp only at hb
  subst hb
  cases eq_of_heq hf
  rfl

/-- Heterogeneous extensionality for morphisms of `A ⋉ F`. -/
theorem Hom.hext {X X' Y Y' : Grothendieck F} (hX : X = X') (hY : Y = Y') {φ : X ⟶ Y} {ψ : X' ⟶ Y'}
    (hb : Hom.base φ ≍ Hom.base ψ) (hf : Hom.fiber φ ≍ Hom.fiber ψ) : φ ≍ ψ := by
  subst hX hY
  exact heq_of_eq (Hom.ext' (eq_of_heq hb) hf)

/-- The projection `π : A ⋉ F ⥤ A`, Mathlib's `Grothendieck.forget`. -/
abbrev π (F : A ⥤ Cat.{v, u}) : A ⋉ F ⥤ A := Grothendieck.forget F

variable {B : Type u₂} [Category.{v₂} B] {G : B ⥤ Cat.{v, u}}

/-- The functor `A ⋉ F ⥤ B ⋉ G` over `u : A ⥤ B` induced by a lax transformation
`α : F ⇒ u ⋙ G`. -/
def map (u : A ⥤ B) (α : LaxTrans F (u ⋙ G)) : A ⋉ F ⥤ B ⋉ G where
  obj X := ⟨u.obj X.base, (α.app X.base).obj X.fiber⟩
  map {X Y} φ := ⟨u.map φ.base, α.naturality φ.base X.fiber ≫ (α.app Y.base).map φ.fiber⟩
  map_id _ := rfl
  map_comp {X _ Z} φ ψ :=
    congrArg (Hom.mk (X := ⟨u.obj X.base, (α.app X.base).obj X.fiber⟩)
      (Y := ⟨u.obj Z.base, (α.app Z.base).obj Z.fiber⟩) (u.map (φ.base ≫ ψ.base)))
      (congrArg (fun t => (G.map (u.map ψ.base)).toFunctor.map
          (α.naturality φ.base X.fiber) ≫ t ≫ (α.app Z.base).map ψ.fiber)
        (α.naturality_naturality ψ.base φ.fiber).symm)

/-- `Groth.map` of the identity transformation is the identity. -/
theorem map_id' (F : A ⥤ Cat.{v, u}) : Groth.map (𝟭 A) (LaxTrans.id F) = 𝟭 (Grothendieck F) :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- `Groth.map` of a composite transformation is the composite. -/
theorem map_vcomp {C : Type*} [Category C] {H : C ⥤ Cat.{v, u}} (u : A ⥤ B) (v : B ⥤ C)
    (α : LaxTrans F (u ⋙ G)) (β : LaxTrans G (v ⋙ H)) :
    Groth.map (u ⋙ v) (α.vcomp (β.whiskerLeft u)) = Groth.map u α ⋙ Groth.map v β :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end Groth

end Groth

/-! ## Functors into `B ⋉ G` over a given base -/

namespace Groth

variable {Z : Type u₁} [Category.{v₁} Z] {B : Type u₂} [Category.{v₂} B] {G : B ⥤ Cat.{v, u}}

/-- A functor `Z ⥤ B ⋉ G` over `v : Z ⥤ B`, given by its fibres: `obj X : G (v X)`, and
`map k : G (v k) (obj X) ⟶ obj Y`, functorially. -/
structure Lift (v : Z ⥤ B) (G : B ⥤ Cat.{v, u}) where
  /-- The fibres of the objects. -/
  obj : ∀ X, G.obj (v.obj X)
  /-- The fibres of the morphisms. -/
  map : ∀ {X Y : Z} (k : X ⟶ Y), (G.map (v.map k)).toFunctor.obj (obj X) ⟶ obj Y
  map_id : ∀ X, map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {X Y W : Z} (k : X ⟶ Y) (l : Y ⟶ W),
    map (k ≫ l) = (G.map (v.map l)).toFunctor.map (map k) ≫ map l

namespace Lift

variable {v : Z ⥤ B}

/-- The functor `Z ⥤ B ⋉ G` of a lift, `X ↦ (v X, obj X)`. -/
def functor (s : Lift v G) : Z ⥤ B ⋉ G where
  obj X := ⟨v.obj X, s.obj X⟩
  map k := ⟨v.map k, s.map k⟩
  map_id X := hom_mk_congr (s.map_id X)
  map_comp k l := hom_mk_congr (s.map_comp k l)

theorem functor_comp_π (s : Lift v G) : s.functor ⋙ π G = v := rfl

/-- The lift of a functor `W : Z ⥤ B ⋉ G` over `v`: its fibres, transported along the bases
`W ⋙ π = v`. Since `v` is a variable, the laws hold by `rfl` once `v` is substituted. -/
def ofFunctor (W : Z ⥤ B ⋉ G) (h : W ⋙ π G = v) : Lift v G where
  obj X := (G.map (eqToHom (Functor.congr_obj h X))).toFunctor.obj (W.obj X).fiber
  map {X Y} k := eqToHom (by subst h; rfl) ≫
    (G.map (eqToHom (Functor.congr_obj h Y))).toFunctor.map (W.map k).fiber
  map_id _ := by subst h; rfl
  map_comp _ _ := by subst h; rfl

/-- Every functor over `v` is the functor of its lift. -/
theorem functor_ofFunctor (W : Z ⥤ B ⋉ G) (h : W ⋙ π G = v) : (ofFunctor W h).functor = W := by
  subst h
  rfl

end Lift

end Groth

/-! ## The unstraightening functor -/

/-- The unstraightening of `F : A ⥤ Cat`: the projection `π : A ⋉ F ⥤ A`. -/
def unstraightenObj {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) : (cod Cat.{u, u}).Ob A :=
  ⟨Cat.of (A ⋉ F), (Groth.π F).toCatHom⟩

/-- The unstraightening of a lax transformation over `u`: the induced functor `Groth.map u α`. -/
def unstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}} {G : B ⥤ Cat.{u, u}}
    (α : LaxTrans F (u.toFunctor ⋙ G)) : (unstraightenObj F ⟶[u] unstraightenObj G) :=
  ⟨(Groth.map u.toFunctor α).toCatHom, rfl⟩

/-- The unstraightening functor: `F : A ⥤ Cat` goes to `π : A ⋉ F ⥤ A`, and a
lax transformation over `u` to the induced functor `Groth.map u α`. -/
def unstraighten : VertFunctor ICat.{u} (cod Cat.{u, u}) where
  obj F := unstraightenObj F
  map α := unstraightenMap α
  map_id _ := rfl
  -- By `rfl` in the elaborator; the kernel needs the functors compared pointwise.
  map_comp _ _ := Subtype.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl))

/-- A lift over `v ⋙ u` into `G` is a lift over `v` into `u ⋙ G`. -/
def Groth.Lift.toComp {Z : Type u₁} [Category.{v₁} Z] {A : Type u₂} [Category.{v₂} A]
    {B : Type*} [Category B] {v : Z ⥤ A} {u : A ⥤ B} {G : B ⥤ Cat.{v, u}}
    (s : Lift (v ⋙ u) G) : Lift v (u ⋙ G) :=
  ⟨s.obj, s.map, s.map_id, s.map_comp⟩

/-- Followed by `A ⋉ u^* G ⥤ B ⋉ G`, the functor of a lift over `v` into `u ⋙ G` is that of the
same lift over `v ⋙ u` into `G`. -/
theorem Groth.Lift.toComp_functor_comp_map {Z : Type u₁} [Category.{v₁} Z] {A : Type u₂}
    [Category.{v₂} A] {B : Type*} [Category B] {v : Z ⥤ A} {u : A ⥤ B} {G : B ⥤ Cat.{v, u}}
    (s : Lift (v ⋙ u) G) : s.toComp.functor ⋙ Groth.map u (LaxTrans.id (u ⋙ G)) = s.functor :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- Postcomposition with `A ⋉ u^* G ⥤ B ⋉ G` is injective on functors over the same base. -/
theorem Groth.comp_map_id_injective {Z : Type u₁} [Category.{v₁} Z] {A : Type u₂}
    [Category.{v₂} A] {B : Type*} [Category B] {u : A ⥤ B} {G : B ⥤ Cat.{v, u}}
    {Ψ₁ Ψ₂ : Z ⥤ A ⋉ (u ⋙ G)} (hb : Ψ₁ ⋙ π _ = Ψ₂ ⋙ π _)
    (h : Ψ₁ ⋙ Groth.map u (LaxTrans.id _) = Ψ₂ ⋙ Groth.map u (LaxTrans.id _)) : Ψ₁ = Ψ₂ := by
  have hobj : ∀ X, Ψ₁.obj X = Ψ₂.obj X := by
    intro X
    have h₀ : (Ψ₁.obj X).base = (Ψ₂.obj X).base := Functor.congr_obj hb X
    have h₁ := Functor.congr_obj h X
    change (⟨u.obj (Ψ₁.obj X).base, (Ψ₁.obj X).fiber⟩ : B ⋉ G) =
      ⟨u.obj (Ψ₂.obj X).base, (Ψ₂.obj X).fiber⟩ at h₁
    revert h₀ h₁
    generalize Ψ₁.obj X = P
    generalize Ψ₂.obj X = Q
    rintro h₀ h₁
    obtain ⟨b, x⟩ := P
    obtain ⟨b', x'⟩ := Q
    obtain rfl : b = b' := h₀
    obtain rfl : x = x' := eq_of_heq (Grothendieck.mk.inj h₁).2
    rfl
  refine Functor.hext hobj fun X Y k => Hom.hext (hobj X) (hobj Y) (Functor.hcongr_hom hb k) ?_
  exact Groth.fiber_heq (Functor.congr_obj h X) (Functor.congr_obj h Y) (Functor.hcongr_hom h k)

/-- **The unstraightening sends the chosen lifts to cartesian morphisms**: `A ⋉ u^* G` is the
pullback of `B ⋉ G` along `u`. The factorization of a functor `χ : Z ⥤ B ⋉ G` over `r ⋙ g ⋙ u`
has the same fibres, read as a lift over `r ⋙ g` into `u ⋙ G`. -/
def isCartesianUnstraightenClift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) :
    IsCartesian (unstraighten.map (ICat.clift u G)) where
  lift g z χ := ⟨(Groth.Lift.ofFunctor χ.1.toFunctor
    (show χ.1.toFunctor ⋙ Groth.π G = (z.hom.toFunctor ⋙ g.toFunctor) ⋙ u.toFunctor from
      congrArg Cat.Hom.toFunctor χ.2)).toComp.functor.toCatHom, rfl⟩
  lift_fac _ _ _ := Subtype.ext (Cat.Hom.ext
    ((Groth.Lift.toComp_functor_comp_map _).trans (Groth.Lift.functor_ofFunctor _ _)))
  lift_uniq {_ g z _} ψ hψ := Subtype.ext (Cat.Hom.ext (Groth.comp_map_id_injective
    (show ψ.1.toFunctor ⋙ Groth.π _ = z.hom.toFunctor ⋙ g.toFunctor from
      congrArg Cat.Hom.toFunctor ψ.2)
    ((congrArg (fun w => Cat.Hom.toFunctor (Subtype.val w)) hψ).trans
      ((Groth.Lift.toComp_functor_comp_map _).trans (Groth.Lift.functor_ofFunctor _ _)).symm)))

/-- The unstraightening is faithful: `α` is read off `Groth.map α` on the morphisms `(𝟙, φ)` and
`(f, 𝟙)`. -/
theorem unstraighten_map_injective {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}}
    {G : B ⥤ Cat.{u, u}} {α β : ICat.Hom u F G} (h : unstraighten.map α = unstraighten.map β) :
    α = β := by
  have hF : Groth.map u.toFunctor α = Groth.map u.toFunctor β :=
    congrArg (fun w => Cat.Hom.toFunctor (Subtype.val w)) h
  refine LaxTrans.ext'
    (fun a x => eq_of_heq (Grothendieck.mk.inj (Functor.congr_obj hF ⟨a, x⟩)).2)
    (fun a x y φ => ?_) (fun {a a'} f x => ?_)
  · exact (Groth.fiber_heq (Functor.congr_obj hF _) (Functor.congr_obj hF _)
      (Functor.hcongr_hom hF (Hom.mk (X := ⟨a, x⟩) (Y := ⟨a, y⟩) (𝟙 a) φ)) :)
  · exact (Groth.fiber_heq (Functor.congr_obj hF _) (Functor.congr_obj hF _)
      (Functor.hcongr_hom hF (Hom.mk (X := ⟨a, x⟩) (Y := ⟨a', (F.map f).toFunctor.obj x⟩)
        f (𝟙 _))) :)

namespace Groth.Lift

variable {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B] {u : A ⥤ B} {F : A ⥤ Cat.{v, u}}
  {G : B ⥤ Cat.{v, u}}

/-- The lax transformation `F ⇒ u ⋙ G` of a functor `A ⋉ F ⥤ B ⋉ G` over `u`, given by its lift:
its components on the morphisms `(𝟙, φ)`, and its 2-cells on the morphisms `(f, 𝟙)`. -/
def toLaxTrans (s : Lift (π F ⋙ u) G) : LaxTrans F (u ⋙ G) where
  app a :=
    { obj y := s.obj ⟨a, y⟩
      map {y y'} φ := s.map (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
      map_id y := s.map_id ⟨a, y⟩
      map_comp {y y' y''} φ ψ := s.map_comp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
        (Hom.mk (X := ⟨a, y'⟩) (Y := ⟨a, y''⟩) (𝟙 a) ψ) }
  naturality {a a'} f y :=
    s.map (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
  naturality_naturality {a a'} f {y y'} φ :=
    (s.map_comp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
      (Hom.mk (X := ⟨a, y'⟩) (Y := ⟨a', (F.map f).toFunctor.obj y'⟩) f (𝟙 _))).symm.trans
    (s.map_comp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
      (Hom.mk (X := ⟨a', (F.map f).toFunctor.obj y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y'⟩)
        (𝟙 a') ((F.map f).toFunctor.map φ)))
  naturality_id {a} y := s.map_id ⟨a, y⟩
  naturality_comp {a a' a''} f g y :=
    s.map_comp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
      (Hom.mk (X := ⟨a', (F.map f).toFunctor.obj y⟩)
        (Y := ⟨a'', (F.map g).toFunctor.obj ((F.map f).toFunctor.obj y)⟩) g (𝟙 _))

/-- `Groth.map` of the lax transformation of a lift is its functor: `(f, φ) = (f, 𝟙) ≫ (𝟙, φ)`. -/
theorem map_toLaxTrans (s : Lift (π F ⋙ u) G) : Groth.map u s.toLaxTrans = s.functor :=
  Functor.hext (fun _ => rfl) fun X Y k => heq_of_eq (hom_mk_congr
    (s.map_comp (Hom.mk (X := X) (Y := ⟨Y.base, (F.map k.base).toFunctor.obj X.fiber⟩)
      k.base (𝟙 _))
    (Hom.mk (X := ⟨Y.base, (F.map k.base).toFunctor.obj X.fiber⟩) (Y := Y)
      (𝟙 Y.base) k.fiber)).symm)

end Groth.Lift

/-- The inverse of the unstraightening on morphisms: the lax transformation of a functor
`A ⋉ F ⥤ B ⋉ G` over `u`, through its lift. -/
def unstraightenPreimage {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}}
    {G : B ⥤ Cat.{u, u}} (w : unstraighten.obj F ⟶[u] unstraighten.obj G) : ICat.Hom u F G :=
  (Groth.Lift.ofFunctor w.1.toFunctor
    (show w.1.toFunctor ⋙ Groth.π G = Groth.π F ⋙ u.toFunctor from
      congrArg Cat.Hom.toFunctor w.2)).toLaxTrans

theorem unstraighten_map_preimage {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}}
    {G : B ⥤ Cat.{u, u}} (w : unstraighten.obj F ⟶[u] unstraighten.obj G) :
    unstraighten.map (unstraightenPreimage w) = w :=
  Subtype.ext (Cat.Hom.ext ((Groth.Lift.map_toLaxTrans _).trans
    (Groth.Lift.functor_ofFunctor _ _)))

/-- **The unstraightening is fully faithful**: functors `A ⋉ F ⥤ B ⋉ G` over `u` are the
same as lax transformations `F ⇒ u ⋙ G`. -/
def unstraightenFullyFaithful : unstraighten.{u}.FullyFaithful where
  preimage w := unstraightenPreimage w
  map_preimage w := unstraighten_map_preimage w
  preimage_map α := unstraighten_map_injective (unstraighten_map_preimage (unstraighten.map α))

/-! ## Transport in `A ⋉ F` -/

namespace Groth

variable {A : Type u₁} [Category.{v₁} A] (F : A ⥤ Cat.{v, u})

/-- The morphism `(f, 𝟙) : (a, x) ⟶ (a', F f x)`. -/
def transport {a a' : A} (f : a ⟶ a') (x : F.obj a) :
    (⟨a, x⟩ : Grothendieck F) ⟶ ⟨a', (F.map f).toFunctor.obj x⟩ :=
  ⟨f, 𝟙 _⟩

@[rewrite_rule]
theorem transport_id (a : A) (x : F.obj a) : transport F (𝟙 a) x = 𝟙 (⟨a, x⟩ : A ⋉ F) := rfl

@[rewrite_rule]
theorem transport_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : F.obj a) :
    transport F (f ≫ g) x = transport F f x ≫ transport F g ((F.map f).toFunctor.obj x) :=
  rfl

/-- A morphism `k` is `(k.base, 𝟙)` followed by `(𝟙, k.fiber)`. -/
theorem transport_incl {X Y : Grothendieck F} (k : X ⟶ Y) :
    transport F k.base X.fiber ≫ (Grothendieck.ι F Y.base).map k.fiber = k :=
  rfl

/-- `(f, 𝟙)` and `(𝟙, φ)` commute. -/
theorem transport_comm {a a' : A} (f : a ⟶ a') {x x' : F.obj a} (φ : x ⟶ x') :
    transport F f x ≫ (Grothendieck.ι F a').map ((F.map f).toFunctor.map φ) =
      (Grothendieck.ι F a).map φ ≫ transport F f x' :=
  rfl

variable {F}

/-! ## Identities between equal objects -/

section EqToHom

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

theorem eqToHom_comp_eqToHom_comp {X Y Z : C} (p : X = Y) (q : Y = X) (f : X ⟶ Z) :
    eqToHom p ≫ eqToHom q ≫ f = f := by
  simp

theorem eqToHom_eq_comp_map_eqToHom (G : C ⥤ D) {a b : C} {c : D} (p : c = G.obj b)
    (q : c = G.obj a) (r : a = b) : eqToHom p = eqToHom q ≫ G.map (eqToHom r) := by
  subst r
  simp

theorem eqToHom_eq_map_map_comp (G : C ⥤ D) (T : E ⥤ C) {a b : E} {c : C} {e : D}
    (p : G.obj c = e) (q : c = T.obj a) (r : a = b) (s : G.obj (T.obj b) = e) :
    eqToHom p = G.map (eqToHom q) ≫ G.map (T.map (eqToHom r)) ≫ eqToHom s := by
  subst q r
  simp

/-- Naturality of an identity between equal functors. -/
theorem map_comp_eqToHom {P Q : C ⥤ D} (h : P = Q) {x y : C} (β : x ⟶ y) :
    P.map β ≫ eqToHom (Functor.congr_obj h y) = eqToHom (Functor.congr_obj h x) ≫ Q.map β := by
  subst h
  simp

/-- Naturality of an identity between `T ⋙ G` and an equal functor, preceded by an identity. -/
theorem map_eqToHom_comp_map_map (T : E ⥤ C) (G : C ⥤ D) {Q : E ⥤ D} (h : T ⋙ G = Q) {x y : E}
    (c : T.obj x = T.obj x) (β : x ⟶ y) :
    G.map (eqToHom c) ≫ G.map (T.map β) ≫ eqToHom (Functor.congr_obj h y) =
      eqToHom (Functor.congr_obj h x) ≫ Q.map β := by
  subst h
  simp

end EqToHom

/-! ## Functors out of `A ⋉ F` -/

variable (B : Grothendieck F ⥤ Cat.{v, u})

/-- `B (𝟙, F f φ) ∘ B (f, 𝟙) = B (f, 𝟙) ∘ B (𝟙, φ)` on objects. -/
theorem obj_transport_comm {a a' : A} (f : a ⟶ a') {x x' : F.obj a} (φ : x ⟶ x')
    (b : B.obj (⟨a, x⟩ : Grothendieck F)) :
    (B.map ((Grothendieck.ι F a').map ((F.map f).toFunctor.map φ))).toFunctor.obj
        ((B.map (transport F f x)).toFunctor.obj b) =
      (B.map (transport F f x')).toFunctor.obj
        ((B.map ((Grothendieck.ι F a).map φ)).toFunctor.obj b) :=
  congrArg (fun k => (B.map k).toFunctor.obj b) (transport_comm F f φ)

/-- `B (𝟙, k.fiber) ∘ B (k.base, 𝟙) = B k` on objects. -/
theorem obj_transport_incl {X Y : Grothendieck F} (k : X ⟶ Y) (b : B.obj X) :
    (B.map ((Grothendieck.ι F Y.base).map k.fiber)).toFunctor.obj
        ((B.map (transport F k.base X.fiber)).toFunctor.obj b) = (B.map k).toFunctor.obj b :=
  congrArg (fun k' => (B.map k').toFunctor.obj b) (transport_incl F k)

end Groth

end Displayed.Opfibration.Straightening
