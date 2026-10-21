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
  (`isCartesian_unstraighten_clift`): `A ⋉ u^* G` is the pullback of `B ⋉ G` along `u`.
* It is fully faithful (`unstraighten_map_bijective`): a functor `A ⋉ F ⥤ B ⋉ G` over `u` is
  `Groth.map` of a unique lax transformation, read off on the morphisms `(f, 𝟙)` and `(𝟙, φ)`.
* Transport in `A ⋉ F`: the morphisms `(f, 𝟙)` (`Groth.transport`), as rules, and their action
  under functors out of `A ⋉ F`.

The notation `A ⋉ F` is scoped in `Displayed.Opfibration.Straightening`, as in the paper.

The last two items about `unstraighten` are proved without transport: a functor `W` into `B ⋉ G`
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

/-- The unstraightening sends the chosen lifts to cartesian morphisms: `A ⋉ u^* G` is the
pullback of `B ⋉ G` along `u`. -/
theorem isCartesian_unstraighten_clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) :
    IsCartesian (unstraighten.map (ICat.clift u G)) := by
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

/-- **The unstraightening is fully faithful**: functors `A ⋉ F ⥤ B ⋉ G` over `u` are the
same as lax transformations `F ⇒ u ⋙ G`. -/
theorem unstraighten_map_bijective {A B : Cat.{u, u}} (u : A ⟶ B) (F : A ⥤ Cat.{u, u})
    (G : B ⥤ Cat.{u, u}) :
    Function.Bijective (unstraighten.map : ICat.Hom u F G → _) := by
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
