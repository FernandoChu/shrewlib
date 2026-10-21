import ComprehensionCategory.CatModel
import ComprehensionCategory.Sigma

/-!
# Σ-types in the category model

For `A : Γ ⥤ Cat` and `B : Γ ⋉ A ⥤ Cat`, the Σ-type `Σ[A] B : Γ ⥤ Cat` (`Groth.sigma B`) sends
`γ` to the Grothendieck construction `A γ ⋉ B(γ, −)` of `B` restricted to the fibre over `γ`, and
`f : γ ⟶ γ'` to the functor induced by the strict transformation with components `B(f, 𝟙)`. Then
`Γ ▹ A ▹ B = Γ ⋉ A ⋉ B` and `Γ ▹ Σ[A] B = Γ ⋉ Σ[A] B` are isomorphic over `Γ`, by
`((γ, x), b) ↦ (γ, (x, b))`, and the category model has Σ-types (`ICat.hasSigma`).

`B(f, 𝟙) ∘ B(𝟙, φ)` and `B(𝟙, F f φ) ∘ B(f, 𝟙)` agree on objects definitionally, since both
composites of morphisms of `Γ ⋉ A` are `(f, F f φ)`, but the functor rules unfold the two into
different terms, which the definitional-equality checker does not identify. So the 2-cells of the
reindexing of `Σ_A B`, and of the pairing, are identities `eqToHom` along such equations, proved by
`rfl`.

Comparing terms that the rules reduce in many steps is slow in the elaborator, which first tries
hard to unify the arguments of applications with the same head, so the expensive steps are checked
in the kernel instead (`kernel_exact`, `kernel_rfl'`), as `kernel_rfl` in `Bicategory/Basic`.
-/

universe v₁ u₁ v u

namespace ComprehensionCategory

open CategoryTheory

open Grothendieck (Hom)

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

/-! ## The Σ-type -/

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

/-- The restriction `B(a, −) : F a ⥤ Cat` of `B` to the fibre over `a`. -/
abbrev fib (a : A) : F.obj a ⥤ Cat.{v, u} := Grothendieck.ι F a ⋙ B

/-- The transformation `B(f, 𝟙) : B(a, −) ⇒ B(a', F f −)`, strictly natural. -/
def sigmaTrans {a a' : A} (f : a ⟶ a') :
    LaxTrans (fib B a) ((F.map f).toFunctor ⋙ fib B a') where
  app x := (B.map (transport F f x)).toFunctor
  naturality φ b := eqToHom (obj_transport_comm B f φ b)
  naturality_naturality φ _ _ β :=
    map_comp_eqToHom (congrArg (fun k => (B.map k).toFunctor) (transport_comm F f φ)) β
  naturality_id _ := eqToHom_refl _ _
  naturality_comp φ ψ b := by
    rw [eqToHom_map, eqToHom_trans]

theorem sigmaTrans_id (a : A) :
    sigmaTrans B (𝟙 a) = (LaxTrans.id (fib B a) :
      LaxTrans (fib B a) ((F.map (𝟙 a)).toFunctor ⋙ fib B a)) :=
  LaxTrans.ext' (fun _ _ => by kernel_rfl') (fun _ _ _ _ => by kernel_rfl') fun φ b => by
    kernel_exact eqToHom_refl _ (obj_transport_comm B (𝟙 a) φ b)

theorem sigmaTrans_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    sigmaTrans B (f ≫ g) = ((sigmaTrans B f).vcomp ((sigmaTrans B g).whiskerLeft
      (F.map f).toFunctor) :
        LaxTrans (fib B a) ((F.map (f ≫ g)).toFunctor ⋙ fib B a'')) :=
  LaxTrans.ext' (fun _ _ => by kernel_rfl') (fun _ _ _ _ => by kernel_rfl') fun {x x'} φ b => by
    kernel_exact eqToHom_eq_comp_map_eqToHom
      (B.map (transport F g ((F.map f).toFunctor.obj x'))).toFunctor
      (obj_transport_comm B (f ≫ g) φ b)
      (obj_transport_comm B g ((F.map f).toFunctor.map φ)
        ((B.map (transport F f x)).toFunctor.obj b))
      (obj_transport_comm B f φ b)

/-- The Σ-type `Σ_F B : A ⥤ Cat`, sending `a` to `F a ⋉ B(a, −)`. -/
def sigma : A ⥤ Cat.{v, u} where
  obj a := Cat.of (Grothendieck (fib B a))
  map f := (Groth.map (F.map f).toFunctor (sigmaTrans B f)).toCatHom
  map_id a := Cat.Hom.ext ((congrArg (Groth.map _) (sigmaTrans_id B a)).trans (Groth.map_id' _))
  map_comp f g := Cat.Hom.ext ((congrArg (Groth.map _) (sigmaTrans_comp B f g)).trans
    (Groth.map_vcomp _ _ _ _))

/-! ## The isomorphism `Γ.A.B ≅ Γ.Σ_A B` -/

/-- The transformation `B ⇒ π ⋙ Σ_F B` including `B(a, x)` into `F a ⋉ B(a, −)`, whose 2-cells
are the morphisms `(φ, 𝟙) : (F f x, B(f, 𝟙) b) ⟶ (x', B(f, φ) b)`. -/
def pairTrans : LaxTrans B (π F ⋙ Groth.sigma B) where
  app X := Grothendieck.ι (fib B X.base) X.fiber
  naturality k b := ⟨k.fiber, eqToHom (obj_transport_incl B k b)⟩
  naturality_naturality {X Y} k {b b'} β := Hom.ext' (by kernel_rfl') (by
    kernel_exact map_eqToHom_comp_map_map (B.map (transport F k.base X.fiber)).toFunctor
      (B.map ((Grothendieck.ι F Y.base).map k.fiber)).toFunctor
      (congrArg (fun k' => (B.map k').toFunctor) (transport_incl F k))
      (obj_transport_comm B k.base (𝟙 X.fiber) b) β)
  naturality_id {X} b := Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_refl _ (obj_transport_incl B (𝟙 X) b))
  naturality_comp {X Y Z} k l b := Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_eq_map_map_comp (B.map ((Grothendieck.ι F Z.base).map l.fiber)).toFunctor
      (B.map (transport F l.base Y.fiber)).toFunctor (obj_transport_incl B (k ≫ l) b)
      (obj_transport_comm B l.base k.fiber ((B.map (transport F k.base X.fiber)).toFunctor.obj b))
      (obj_transport_incl B k b) (obj_transport_incl B l ((B.map k).toFunctor.obj b)))

/-- `((a, x), b) ↦ (a, (x, b))`. -/
def pair : A ⋉ F ⋉ B ⥤ A ⋉ Groth.sigma B := Groth.map (π F) (pairTrans B)

/-- `(a, (x, b)) ↦ ((a, x), b)` on morphisms. -/
def unpairMap {X Y : Grothendieck (Groth.sigma B)} (k : X ⟶ Y) :
    (⟨⟨X.base, X.fiber.base⟩, X.fiber.fiber⟩ : A ⋉ F ⋉ B) ⟶
      ⟨⟨Y.base, Y.fiber.base⟩, Y.fiber.fiber⟩ :=
  ⟨⟨k.base, k.fiber.base⟩, eqToHom (obj_transport_incl B (Hom.mk (X := ⟨X.base, X.fiber.base⟩)
    (Y := ⟨Y.base, Y.fiber.base⟩) k.base k.fiber.base) X.fiber.fiber).symm ≫ k.fiber.fiber⟩

theorem unpairMap_pair_map {X Y : Grothendieck B} (k : X ⟶ Y) : unpairMap B ((pair B).map k) = k :=
  Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_comp_eqToHom_comp
      (obj_transport_incl B (Hom.mk (X := ⟨X.base.base, X.base.fiber⟩)
        (Y := ⟨Y.base.base, Y.base.fiber⟩) k.base.base k.base.fiber) X.fiber).symm
      (obj_transport_incl B k.base X.fiber) k.fiber)

theorem pair_map_unpairMap {X Y : Grothendieck (Groth.sigma B)} (k : X ⟶ Y) :
    (pair B).map (unpairMap B k) = k :=
  Hom.ext' (by kernel_rfl') (Hom.hext (by kernel_rfl') (by kernel_rfl') (by kernel_rfl') (by
    kernel_exact eqToHom_comp_eqToHom_comp
      (obj_transport_incl B (Hom.mk (X := ⟨X.base, X.fiber.base⟩)
        (Y := ⟨Y.base, Y.fiber.base⟩) k.base k.fiber.base) X.fiber.fiber)
      (obj_transport_incl B (Hom.mk (X := ⟨X.base, X.fiber.base⟩)
        (Y := ⟨Y.base, Y.fiber.base⟩) k.base k.fiber.base) X.fiber.fiber).symm k.fiber.fiber))

/-- `(a, (x, b)) ↦ ((a, x), b)`, inverse to `pair`. -/
def unpair : A ⋉ Groth.sigma B ⥤ A ⋉ F ⋉ B where
  obj X := ⟨⟨X.base, X.fiber.base⟩, X.fiber.fiber⟩
  map k := unpairMap B k
  map_id X := by
    kernel_exact (congrArg (unpairMap B) ((pair B).map_id
      (⟨⟨X.base, X.fiber.base⟩, X.fiber.fiber⟩ : Grothendieck B))).symm.trans
      (unpairMap_pair_map B (𝟙 (⟨⟨X.base, X.fiber.base⟩, X.fiber.fiber⟩ : Grothendieck B)))
  map_comp {X Y Z} k l := by
    have h : (pair B).map (unpairMap B k ≫ unpairMap B l) = k ≫ l := by
      rw [Functor.map_comp]
      kernel_exact congrArg₂ (· ≫ ·) (pair_map_unpairMap B k) (pair_map_unpairMap B l)
    kernel_exact (congrArg (unpairMap B) h).symm.trans
      (unpairMap_pair_map B (unpairMap B k ≫ unpairMap B l))

theorem pair_unpair : pair B ⋙ unpair B = 𝟭 _ :=
  Functor.hext (fun _ => by kernel_rfl') fun _ _ k => by kernel_exact unpairMap_pair_map B k

theorem unpair_pair : unpair B ⋙ pair B = 𝟭 _ :=
  Functor.hext (fun _ => by kernel_rfl') fun _ _ k => by kernel_exact pair_map_unpairMap B k

theorem pair_π : pair B ⋙ π (Groth.sigma B) = π B ⋙ π F :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end Groth

/-! ## The category model has Σ-types -/

open Displayed

namespace ICat

variable {Γ : Cat.{u, u}} (A : Γ ⥤ Cat.{u, u}) (B : Γ ⋉ A ⥤ Cat.{u, u})

/-- The Σ-type `Σ_A B` of the category model. -/
def sigma : Γ ⥤ Cat.{u, u} := Groth.sigma B

/-- `Γ.A.B ⟶ Γ.Σ_A B`. -/
def pairHom : Cat.of (Γ ⋉ A ⋉ B) ⟶ Cat.of (Γ ⋉ ICat.sigma A B) := (Groth.pair B).toCatHom

/-- `Γ.Σ_A B ⟶ Γ.A.B`. -/
def unpairHom : Cat.of (Γ ⋉ ICat.sigma A B) ⟶ Cat.of (Γ ⋉ A ⋉ B) :=
  (Groth.unpair B).toCatHom

/-- The Σ-types of the category model, stable under substitution. -/
instance preSigma : PreSigma ICat.{u} where
  sigma A B := ICat.sigma A B
  pull_sigma _ _ _ := Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl'

/-- **The category model has Σ-types.** -/
instance hasSigma : HasSigma ICat.{u} where
  pair A B := pairHom A B
  unpair A B := unpairHom A B
  pair_unpair _ B := Cat.Hom.ext (Groth.pair_unpair B)
  unpair_pair _ B := Cat.Hom.ext (Groth.unpair_pair B)
  pair_proj _ B := Cat.Hom.ext (Groth.pair_π B)
  pair_q _ _ _ := Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

end ICat

end ComprehensionCategory
