import Displayed.Opfibration.Straightening.Unstraighten

/-!
# Context extension in the category model

The context extension of `F : A ⥤ Cat` in the category model is the total category of its
unstraightening, `A ⋉ F := (unstraightenObj F).Total`: objects are pairs `(a, x)` with `x : F a`,
and a morphism `(a, x) ⟶ (a', y)` is a pair `(f, φ)` with `φ : F f x ⟶ y`. Its identities are
`(𝟙, 𝟙)` and its composites `(f ≫ g, F g φ ≫ ψ)`, by `rfl`. A lax transformation `α : F ⇒ u ⋙ G`
induces the functor `(unstraightenMap α).total : A ⋉ F ⥤ B ⋉ G`, sending `(f, φ)` to
`(u f, α_f x ≫ α φ)`.

This file gives the inclusion `incl F a : F a ⥤ A ⋉ F` of a fibre, the morphisms `(f, 𝟙)`
(`transport`), as rules, and their action under functors out of `A ⋉ F`, used for Σ-types.
-/

universe v₁ u₁ v₂ u₂ v u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- `A ⋉ F` is the total category of the unstraightening of `F : A ⥤ Cat`. -/
scoped notation:65 Γ:65 " ⋉ " F:66 => Displayed.Total (A := Γ) (unstraightenObj F)

section

variable {A : Type u₁} [Category.{v₁} A] (F : A ⥤ Cat.{v, u})

/-- The projection `π : A ⋉ F ⥤ A`. -/
abbrev π : A ⋉ F ⥤ A := (unstraightenObj F).π

/-- The inclusion `F a ⥤ A ⋉ F` of the fibre over `a`: `x ↦ (a, x)` and `φ ↦ (𝟙, φ)`. -/
def incl (a : A) : F.obj a ⥤ A ⋉ F where
  obj x := (unstraightenObj F).tot x
  map φ := (unstraightenObj F).totalMk (𝟙 a) φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The morphism `(f, 𝟙) : (a, x) ⟶ (a', F f x)`. -/
def transport {a a' : A} (f : a ⟶ a') (x : F.obj a) :
    (unstraightenObj F).tot x ⟶ (unstraightenObj F).tot ((F.map f).toFunctor.obj x) :=
  (unstraightenObj F).totalMk f (𝟙 _)

@[rewrite_rule]
theorem transport_id (a : A) (x : F.obj a) :
    transport F (𝟙 a) x = 𝟙 ((unstraightenObj F).tot x) := rfl

@[rewrite_rule]
theorem transport_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : F.obj a) :
    transport F (f ≫ g) x = transport F f x ≫ transport F g ((F.map f).toFunctor.obj x) :=
  rfl

/-- A morphism `k` is `(k.base, 𝟙)` followed by `(𝟙, k.fiber)`. -/
theorem transport_incl {X Y : A ⋉ F} (k : X ⟶ Y) :
    transport F k.base X.2 ≫ (incl F Y.1).map k.fiber = k :=
  rfl

/-- `(f, 𝟙)` and `(𝟙, φ)` commute. -/
theorem transport_comm {a a' : A} (f : a ⟶ a') {x x' : F.obj a} (φ : x ⟶ x') :
    transport F f x ≫ (incl F a').map ((F.map f).toFunctor.map φ) =
      (incl F a).map φ ≫ transport F f x' :=
  rfl

/-- The functor induced by the identity transformation is the identity. -/
theorem total_unstraightenMap_id :
    (unstraightenMap (u := 𝟭 A) (LaxTrans.id F)).total = 𝟭 (A ⋉ F) :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- The functor induced by a composite transformation is the composite. -/
theorem total_unstraightenMap_vcomp {B : Type u₂} [Category.{v₂} B] {C : Type*} [Category C]
    {G : B ⥤ Cat.{v, u}} {H : C ⥤ Cat.{v, u}} (u : A ⥤ B) (w : B ⥤ C) (α : LaxTrans F (u ⋙ G))
    (β : LaxTrans G (w ⋙ H)) :
    (unstraightenMap (u := u ⋙ w) (α.vcomp (β.whiskerLeft u))).total =
      (unstraightenMap α).total ⋙ (unstraightenMap β).total :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end

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

section

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v, u}} (B : A ⋉ F ⥤ Cat.{v, u})

/-- `B (𝟙, F f φ) ∘ B (f, 𝟙) = B (f, 𝟙) ∘ B (𝟙, φ)` on objects. -/
theorem obj_transport_comm {a a' : A} (f : a ⟶ a') {x x' : F.obj a} (φ : x ⟶ x')
    (b : B.obj ((unstraightenObj F).tot x)) :
    (B.map ((incl F a').map ((F.map f).toFunctor.map φ))).toFunctor.obj
        ((B.map (transport F f x)).toFunctor.obj b) =
      (B.map (transport F f x')).toFunctor.obj ((B.map ((incl F a).map φ)).toFunctor.obj b) :=
  congrArg (fun k => (B.map k).toFunctor.obj b) (transport_comm F f φ)

/-- `B (𝟙, k.fiber) ∘ B (k.base, 𝟙) = B k` on objects. -/
theorem obj_transport_incl {X Y : A ⋉ F} (k : X ⟶ Y) (b : B.obj X) :
    (B.map ((incl F Y.1).map k.fiber)).toFunctor.obj
        ((B.map (transport F k.base X.2)).toFunctor.obj b) = (B.map k).toFunctor.obj b :=
  congrArg (fun k' => (B.map k').toFunctor.obj b) (transport_incl F k)

end

end ComprehensionCategory.CatModel
