import ComprehensionCategory.LaxTrans
import Tactic.KernelTactic
import Mathlib.CategoryTheory.Grothendieck

/-!
# The category model

The *category model* is the full split comprehension category over `Cat` given by the split
fibration `ICat` of indexed categories and lax transformations (`ComprehensionCategory/LaxTrans`),
with the comprehension functor `ICat ⟶ cod Cat` sending `F : A ⥤ Cat` to the projection
`π : A ⋉ F ⥤ A` of its Grothendieck construction.

* `A ⋉ F` is Mathlib's `Grothendieck F`: objects are pairs `(a, x)` with `x : F a`, and a morphism
  `(a, x) ⟶ (a', y)` is a pair `(f, φ)` with `φ : F f x ⟶ y`. Its identities and composites carry
  `eqToHom`s along `F (𝟙 a) x = x` and `F (f ≫ g) x = F g (F f x)`, which the functor rules make
  identities, so that, with the category laws as rules too, they are `(𝟙, 𝟙)` and
  `(f ≫ g, F g φ ≫ ψ)` by `rfl`. The projection `π` is `Grothendieck.forget`.
* `Groth.map α`: the functor `A ⋉ F ⥤ B ⋉ G` over `u : A ⥤ B` induced by a lax transformation
  `α : F ⇒ u ⋙ G`, sending `(f, φ)` to `(u f, α_f x ≫ α φ)`.
* `compr : VertFunctor ICat (cod Cat)`, whose functor laws hold by `rfl`.
* It sends the chosen lifts, the identities `u^* G ⟶[u] G`, to cartesian morphisms of `cod Cat`
  (`isCartesian_compr_clift`): `A ⋉ u^* G` is the pullback of `B ⋉ G` along `u`.
* It is fully faithful (`compr_map_bijective`): a functor `A ⋉ F ⥤ B ⋉ G` over `u` is `Groth.map`
  of a unique lax transformation, read off on the morphisms `(f, 𝟙)` and `(𝟙, φ)`.

The Grothendieck construction `Grothendieck F` of `F : A ⥤ Cat` is written `A ⋉ F` (scoped in
`ComprehensionCategory`), as in the paper, so that the comprehension of `F` is `π : A ⋉ F ⥤ A`.

The last two are proved without transport: a functor `W` into `B ⋉ G` whose composite with `π` is
known is taken apart into its components, whose bases are then substituted by the known ones.
-/

universe v₁ u₁ v₂ u₂ v u

namespace ComprehensionCategory

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

/-! ## The comprehension functor -/

/-- The comprehension of `F : A ⥤ Cat`: the projection `π : A ⋉ F ⥤ A`. -/
def comprObj {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) : (cod Cat.{u, u}).Ob A :=
  ⟨Cat.of (A ⋉ F), (Groth.π F).toCatHom⟩

/-- The comprehension of a lax transformation over `u`: the induced functor `Groth.map u α`. -/
def comprMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}} {G : B ⥤ Cat.{u, u}}
    (α : LaxTrans F (u.toFunctor ⋙ G)) : (comprObj F ⟶[u] comprObj G) :=
  ⟨(Groth.map u.toFunctor α).toCatHom, rfl⟩

/-- The comprehension functor of the category model: `F : A ⥤ Cat` goes to `π : A ⋉ F ⥤ A`, and a
lax transformation over `u` to the induced functor `Groth.map u α`. -/
def compr : VertFunctor ICat.{u} (cod Cat.{u, u}) where
  obj F := comprObj F
  map α := comprMap α
  map_id _ := rfl
  -- By `rfl` in the elaborator; the kernel needs the functors compared pointwise.
  map_comp _ _ := Subtype.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl))

/-- The comprehension functor sends the chosen lifts to cartesian morphisms: `A ⋉ u^* G` is the
pullback of `B ⋉ G` along `u`. -/
theorem isCartesian_compr_clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) :
    IsCartesian (compr.map (ICat.clift u G)) := by
  intro A₀ g z χ
  obtain ⟨Z, r⟩ := z
  obtain ⟨⟨⟨o, m, hid, hcomp⟩⟩, hχ⟩ := χ
  -- The bases of `χ` are those of `r ≫ g ≫ u`: substitute them.
  have hB : (fun X => Grothendieck.base (o X)) =
      fun X => u.toFunctor.obj (g.toFunctor.obj (r.toFunctor.obj X)) :=
    congrArg (fun k : Z ⟶ B => k.toFunctor.obj) hχ
  obtain ⟨b, x, rfl⟩ : ∃ (b : Z → B) (x : ∀ X, G.obj (b X)),
      o = fun X => (⟨b X, x X⟩ : Grothendieck G) :=
    ⟨_, fun X => Grothendieck.fiber (o X), rfl⟩
  obtain rfl : b = fun X => u.toFunctor.obj (g.toFunctor.obj (r.toFunctor.obj X)) := hB
  have hmb : ∀ {X Y : Z} (k : X ⟶ Y),
      Hom.base (m k) = u.toFunctor.map (g.toFunctor.map (r.toFunctor.map k)) := fun k =>
    eq_of_heq (Functor.hcongr_hom (congrArg Cat.Hom.toFunctor hχ) k)
  obtain ⟨mb, mf, rfl⟩ : ∃ (mb : ∀ {X Y : Z}, (X ⟶ Y) →
        (u.toFunctor.obj (g.toFunctor.obj (r.toFunctor.obj X)) ⟶
          u.toFunctor.obj (g.toFunctor.obj (r.toFunctor.obj Y))))
      (mf : ∀ {X Y : Z} (k : X ⟶ Y), (G.map (mb k)).toFunctor.obj (x X) ⟶ x Y),
      @m = fun {X Y} k => Hom.mk (X := ⟨_, x X⟩) (Y := ⟨_, x Y⟩) (mb k) (mf k) :=
    ⟨fun k => Hom.base (m k), fun k => Hom.fiber (m k), rfl⟩
  obtain rfl : @mb = fun {X Y} k => u.toFunctor.map (g.toFunctor.map (r.toFunctor.map k)) := by
    funext X Y k
    exact hmb k
  -- The factorization through `u^* G`: the same components, over `r ≫ g`.
  let ψ : Z ⥤ Grothendieck (u.toFunctor ⋙ G) :=
    { obj X := ⟨g.toFunctor.obj (r.toFunctor.obj X), x X⟩
      map k := ⟨g.toFunctor.map (r.toFunctor.map k), mf k⟩
      map_id X := Groth.hom_mk_congr (by kernel_exact Groth.fiber_eq_of_eq (hid X))
      map_comp k l := Groth.hom_mk_congr (by kernel_exact Groth.fiber_eq_of_eq (hcomp k l)) }
  refine ⟨⟨ψ.toCatHom, rfl⟩, Subtype.ext (Cat.Hom.ext
    (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl)), ?_⟩
  rintro ⟨⟨⟨o', m', hid', hcomp'⟩⟩, hsq⟩ hψ
  -- Its bases are those of `r ≫ g`, and its fibres are those of `χ`.
  have hB' : (fun X => Grothendieck.base (o' X)) = fun X => g.toFunctor.obj (r.toFunctor.obj X) :=
    congrArg (fun k : Z ⟶ A => k.toFunctor.obj) hsq
  obtain ⟨b', x', rfl⟩ : ∃ (b' : Z → A) (x' : ∀ X, G.obj (u.toFunctor.obj (b' X))),
      o' = fun X => (⟨b' X, x' X⟩ : Grothendieck (u.toFunctor ⋙ G)) :=
    ⟨_, fun X => Grothendieck.fiber (o' X), rfl⟩
  obtain rfl : b' = fun X => g.toFunctor.obj (r.toFunctor.obj X) := hB'
  have hmb' : ∀ {X Y : Z} (k : X ⟶ Y),
      Hom.base (m' k) = g.toFunctor.map (r.toFunctor.map k) := fun k =>
    eq_of_heq (Functor.hcongr_hom (congrArg Cat.Hom.toFunctor hsq) k)
  obtain ⟨mb', mf', rfl⟩ : ∃ (mb' : ∀ {X Y : Z}, (X ⟶ Y) →
        (g.toFunctor.obj (r.toFunctor.obj X) ⟶ g.toFunctor.obj (r.toFunctor.obj Y)))
      (mf' : ∀ {X Y : Z} (k : X ⟶ Y),
        (G.map (u.toFunctor.map (mb' k))).toFunctor.obj (x' X) ⟶ x' Y),
      @m' = fun {X Y} k => Hom.mk (F := u.toFunctor ⋙ G) (X := ⟨_, x' X⟩) (Y := ⟨_, x' Y⟩)
        (mb' k) (mf' k) :=
    ⟨fun k => Hom.base (m' k), fun k => Hom.fiber (m' k), rfl⟩
  obtain rfl : @mb' = fun {X Y} k => g.toFunctor.map (r.toFunctor.map k) := by
    funext X Y k
    exact hmb' k
  have hF := congrArg (fun w => Cat.Hom.toFunctor (Subtype.val w)) hψ
  obtain rfl : x' = x :=
    funext fun X => eq_of_heq (Grothendieck.mk.inj (Functor.congr_obj hF X)).2
  obtain rfl : @mf' = @mf := by
    funext X Y k
    exact Groth.fiber_eq_of_eq (eq_of_heq (Functor.hcongr_hom hF k))
  exact Subtype.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl))

/-- **The comprehension functor is fully faithful**: functors `A ⋉ F ⥤ B ⋉ G` over `u` are the
same as lax transformations `F ⇒ u ⋙ G`. -/
theorem compr_map_bijective {A B : Cat.{u, u}} (u : A ⟶ B) (F : A ⥤ Cat.{u, u})
    (G : B ⥤ Cat.{u, u}) :
    Function.Bijective (compr.map : ICat.Hom u F G → _) := by
  refine ⟨fun α β h => ?_, fun w => ?_⟩
  · -- `α` is read off `Groth.map α` on the morphisms `(𝟙, φ)` and `(f, 𝟙)`.
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
  · obtain ⟨⟨⟨o, m, hid, hcomp⟩⟩, hw⟩ := w
    -- The bases of `w` are those of `π ≫ u`: substitute them.
    have hB : (fun X => Grothendieck.base (o X)) =
        fun X : Grothendieck F => u.toFunctor.obj X.base :=
      congrArg (fun k : Cat.of (Grothendieck F) ⟶ B => k.toFunctor.obj) hw
    obtain ⟨b, x, rfl⟩ : ∃ (b : Grothendieck F → B) (x : ∀ X, G.obj (b X)),
        o = fun X => (⟨b X, x X⟩ : Grothendieck G) :=
      ⟨_, fun X => Grothendieck.fiber (o X), rfl⟩
    obtain rfl : b = fun X : Grothendieck F => u.toFunctor.obj X.base := hB
    have hmb : ∀ {X Y : Grothendieck F} (k : X ⟶ Y),
        Hom.base (m k) = u.toFunctor.map (Hom.base k) := fun k =>
      eq_of_heq (Functor.hcongr_hom (congrArg Cat.Hom.toFunctor hw) k)
    obtain ⟨mb, mf, rfl⟩ : ∃ (mb : ∀ {X Y : Grothendieck F}, (X ⟶ Y) →
          (u.toFunctor.obj X.base ⟶ u.toFunctor.obj Y.base))
        (mf : ∀ {X Y : Grothendieck F} (k : X ⟶ Y), (G.map (mb k)).toFunctor.obj (x X) ⟶ x Y),
        @m = fun {X Y} k => Hom.mk (X := ⟨_, x X⟩) (Y := ⟨_, x Y⟩) (mb k) (mf k) :=
      ⟨fun k => Hom.base (m k), fun k => Hom.fiber (m k), rfl⟩
    obtain rfl : @mb = fun {X Y} k => u.toFunctor.map (Hom.base k) := by
      funext X Y k
      exact hmb k
    -- The lax transformation: components on `(𝟙, φ)`, 2-cells on `(f, 𝟙)`.
    let α : LaxTrans F (u.toFunctor ⋙ G) :=
      { app a :=
          { obj y := x ⟨a, y⟩
            map {y y'} φ := mf (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
            map_id y := Groth.fiber_eq_of_eq (hid ⟨a, y⟩)
            map_comp {y y' y''} φ ψ := Groth.fiber_eq_of_eq
              (hcomp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
                (Hom.mk (X := ⟨a, y'⟩) (Y := ⟨a, y''⟩) (𝟙 a) ψ)) }
        naturality {a a'} f y :=
          mf (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
        naturality_naturality {a a'} f {y y'} φ :=
          (Groth.fiber_eq_of_eq
            (hcomp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a, y'⟩) (𝟙 a) φ)
              (Hom.mk (X := ⟨a, y'⟩) (Y := ⟨a', (F.map f).toFunctor.obj y'⟩) f
                (𝟙 _)))).symm.trans
          (Groth.fiber_eq_of_eq
            (hcomp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
              (Hom.mk (X := ⟨a', (F.map f).toFunctor.obj y⟩)
                (Y := ⟨a', (F.map f).toFunctor.obj y'⟩) (𝟙 a') ((F.map f).toFunctor.map φ))))
        naturality_id {a} y := Groth.fiber_eq_of_eq (hid ⟨a, y⟩)
        naturality_comp {a a' a''} f g y := Groth.fiber_eq_of_eq
          (hcomp (Hom.mk (X := ⟨a, y⟩) (Y := ⟨a', (F.map f).toFunctor.obj y⟩) f (𝟙 _))
            (Hom.mk (X := ⟨a', (F.map f).toFunctor.obj y⟩)
              (Y := ⟨a'', (F.map g).toFunctor.obj ((F.map f).toFunctor.obj y)⟩) g (𝟙 _))) }
    -- `(f, φ) = (f, 𝟙) ≫ (𝟙, φ)`, so `Groth.map α` is `w`.
    refine ⟨α, Subtype.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun X Y k => heq_of_eq ?_))⟩
    exact Groth.hom_mk_congr (Groth.fiber_eq_of_eq
      (hcomp (Hom.mk (X := X) (Y := ⟨Y.base, (F.map k.base).toFunctor.obj X.fiber⟩)
          k.base (𝟙 _))
        (Hom.mk (X := ⟨Y.base, (F.map k.base).toFunctor.obj X.fiber⟩) (Y := Y)
          (𝟙 Y.base) k.fiber))).symm

@[instance_reducible]
instance ICat.comprehension : Comprehension ICat.{u} :=
  Comprehension.ofClift compr isCartesian_compr_clift

/-- **The category model** is a full split comprehension category over `Cat`. -/
instance ICat.splitComprehension : SplitComprehension ICat.{u} where

instance ICat.fullComprehension : FullComprehension ICat.{u} where
  compr_map_bijective := compr_map_bijective

end ComprehensionCategory
