import Nfib.Displayed.Cartesian
import Mathlib.CategoryTheory.Equivalence

/-!
# Fibrations and displayed equivalences

A displayed category `D` over `A` is a *fibration* if every base morphism `f : a ⟶ a'` has a
cartesian lift at every object over `a'` (`IsFibration`). Cartesian morphisms are the strong ones of
`Nfib.Displayed.Cartesian`.

Categories over `A` and functors over `A` are displayed categories over `A` and displayed functors
over the identity (`DFunctor`). An *equivalence over `A`* (`DEquivalence`) is a pair of displayed
functors with vertical natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`: their components lie over
identities. We show:

* a displayed equivalence is fully faithful on displayed hom-types over each base morphism
  (`DEquivalence.map_injective`, `DEquivalence.map_surjective`);
* it preserves cartesian morphisms (`DEquivalence.isCartesian_map`);
* the fibration property transfers along it (`DEquivalence.isFibration`);
* it induces an equivalence of the total categories commuting with the projections to `A`
  (`DEquivalence.total`).

The laws of displayed functors are rewrite rules.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A]

/-- A displayed category is a *fibration* if every base morphism has a cartesian lift at every
object over its codomain. -/
def IsFibration (D : Displayed.{v₁, u₁, v₂, u₂} A) : Prop :=
  ∀ ⦃a a' : A⦄ (f : a ⟶ a') (y : D.Ob a'), ∃ (x : D.Ob a) (φ : x ⟶[f] y), IsCartesian φ

section DFunctor

/-- A displayed functor over the identity of `A`, i.e. a functor over `A` between the total
categories. -/
structure DFunctor (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) where
  /-- The action on objects, fiberwise. -/
  obj : {a : A} → D.Ob a → E.Ob a
  /-- The action on morphisms, over the same base morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : D.Ob a} → {y : D.Ob a'} → (x ⟶[f] y) →
    (obj x ⟶[f] obj y)
  map_id : ∀ {a : A} (x : D.Ob a), map (𝟙ᵈ x) = 𝟙ᵈ (obj x)
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z), map (φ ≫ᵈ ψ) = map φ ≫ᵈ map ψ

attribute [rewrite_rule] DFunctor.map_id DFunctor.map_comp

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}
  {E' : Displayed.{v₁, u₁, v₂, u₂} A}

/-- The identity displayed functor. -/
def DFunctor.id (D : Displayed.{v₁, u₁, v₂, u₂} A) : DFunctor D D where
  obj x := x
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of displayed functors. -/
def DFunctor.comp (F : DFunctor D E) (G : DFunctor E E') : DFunctor D E' where
  obj x := G.obj (F.obj x)
  map φ := G.map (F.map φ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A vertical natural isomorphism between displayed functors: its components lie over identities,
and it is natural with respect to displayed morphisms over arbitrary base morphisms. -/
structure VNatIso (F G : DFunctor D E) where
  /-- The components. -/
  app : ∀ {a : A} (x : D.Ob a), F.obj x ⟶[𝟙 a] G.obj x
  /-- The components of the inverse. -/
  inv : ∀ {a : A} (x : D.Ob a), G.obj x ⟶[𝟙 a] F.obj x
  app_inv : ∀ {a : A} (x : D.Ob a), app x ≫ᵈ inv x = 𝟙ᵈ (F.obj x)
  inv_app : ∀ {a : A} (x : D.Ob a), inv x ≫ᵈ app x = 𝟙ᵈ (G.obj x)
  naturality : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
    app x ≫ᵈ G.map φ = F.map φ ≫ᵈ app y

namespace VNatIso

variable {F G : DFunctor D E} (η : VNatIso F G)

theorem app_inv_assoc {a a' : A} {g : a ⟶ a'} (x : D.Ob a) {z : E.Ob a'} (h : F.obj x ⟶[g] z) :
    η.app x ≫ᵈ (η.inv x ≫ᵈ h) = h :=
  (congrArg (· ≫ᵈ h) (η.app_inv x) :)

theorem inv_app_assoc {a a' : A} {g : a ⟶ a'} (x : D.Ob a) {z : E.Ob a'} (h : G.obj x ⟶[g] z) :
    η.inv x ≫ᵈ (η.app x ≫ᵈ h) = h :=
  (congrArg (· ≫ᵈ h) (η.inv_app x) :)

attribute [rewrite_rule] app_inv inv_app app_inv_assoc inv_app_assoc

theorem inv_naturality {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    η.inv x ≫ᵈ F.map φ = G.map φ ≫ᵈ η.inv y :=
  (congrArg (fun t => η.inv x ≫ᵈ (t ≫ᵈ η.inv y)) (η.naturality φ).symm :)

/-- The inverse of a vertical natural isomorphism. -/
def symm : VNatIso G F where
  app := η.inv
  inv := η.app
  app_inv := η.inv_app
  inv_app := η.app_inv
  naturality := η.inv_naturality

end VNatIso

/-- Postcomposing a cartesian morphism with a vertical isomorphism gives a cartesian morphism. -/
theorem IsCartesian.comp_iso {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y y' : D.Ob a'}
    {φ : x ⟶[f] y} (H : IsCartesian φ) (ι : y ⟶[𝟙 a'] y') (ι' : y' ⟶[𝟙 a'] y)
    (h : ι' ≫ᵈ ι = 𝟙ᵈ y') (h' : ι ≫ᵈ ι' = 𝟙ᵈ y) : IsCartesian (φ ≫ᵈ ι) := by
  intro a₀ g z χ
  refine ⟨IsCartesian.lift H g (χ ≫ᵈ ι' :), ?_, fun ψ hψ => IsCartesian.lift_uniq H ψ ?_⟩
  · exact ((congrArg (· ≫ᵈ ι) (IsCartesian.lift_fac H g (χ ≫ᵈ ι' :))).trans
      (congrArg (χ ≫ᵈ ·) h) :)
  · exact ((congrArg (fun t => ψ ≫ᵈ (φ ≫ᵈ t)) h').symm.trans (congrArg (· ≫ᵈ ι') hψ) :)

/-- An equivalence of categories over `A`: displayed functors in both directions, with vertical
natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`. -/
structure DEquivalence (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) where
  /-- The functor. -/
  functor : DFunctor D E
  /-- The inverse functor. -/
  inverse : DFunctor E D
  /-- The unit. -/
  unitIso : VNatIso (DFunctor.id D) (functor.comp inverse)
  /-- The counit. -/
  counitIso : VNatIso (inverse.comp functor) (DFunctor.id E)

namespace DEquivalence

variable (e : DEquivalence D E)

/-- The inverse equivalence. -/
def symm : DEquivalence E D where
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- A displayed morphism, recovered from its image under `F ⋙ G` by conjugating with the unit. -/
theorem eq_conj {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    φ = e.unitIso.app x ≫ᵈ (e.inverse.map (e.functor.map φ) ≫ᵈ e.unitIso.inv y) :=
  (congrArg (· ≫ᵈ e.unitIso.inv y) (e.unitIso.naturality φ) :).symm

/-- A displayed equivalence is faithful on displayed hom-types. -/
theorem map_injective {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ φ' : x ⟶[f] y}
    (h : e.functor.map φ = e.functor.map φ') : φ = φ' :=
  (e.eq_conj φ).trans ((congrArg (fun t =>
    e.unitIso.app x ≫ᵈ (e.inverse.map t ≫ᵈ e.unitIso.inv y)) h).trans (e.eq_conj φ').symm)

/-- A displayed equivalence is full on displayed hom-types. -/
theorem map_surjective {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : ∃ φ : x ⟶[f] y, e.functor.map φ = ψ := by
  let φ : x ⟶[f] y := (e.unitIso.app x ≫ᵈ (e.inverse.map ψ ≫ᵈ e.unitIso.inv y) :)
  refine ⟨φ, e.symm.map_injective ?_⟩
  exact (congrArg (fun t => e.unitIso.inv x ≫ᵈ (t ≫ᵈ e.unitIso.app y)) (e.eq_conj φ) :).symm

/-- **A displayed equivalence preserves cartesian morphisms.** -/
theorem isCartesian_map {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsCartesian φ) : IsCartesian (e.functor.map φ) := by
  intro a₀ g z χ
  let ε := e.counitIso
  obtain ⟨χ', hχ'⟩ := e.map_surjective (ε.app z ≫ᵈ χ :)
  refine ⟨(ε.inv z ≫ᵈ e.functor.map (IsCartesian.lift H g χ') :), ?_, fun ψ hψ => ?_⟩
  · exact ((congrArg (fun t => ε.inv z ≫ᵈ e.functor.map t) (IsCartesian.lift_fac H g χ')).trans
      (congrArg (ε.inv z ≫ᵈ ·) hχ') :)
  · obtain ⟨ψ', hψ'⟩ := e.map_surjective (ε.app z ≫ᵈ ψ :)
    have h₁ : ψ' ≫ᵈ φ = χ' := e.map_injective
      ((congrArg (· ≫ᵈ e.functor.map φ) hψ').trans ((congrArg (ε.app z ≫ᵈ ·) hψ).trans hχ'.symm) :)
    have h₂ : ψ' = IsCartesian.lift H g χ' := IsCartesian.lift_uniq H ψ' h₁
    exact (congrArg (ε.inv z ≫ᵈ ·) (hψ'.symm.trans (congrArg e.functor.map h₂)) :)

/-- **The fibration property transfers along a displayed equivalence.** -/
theorem isFibration (e : DEquivalence D E) (hD : IsFibration D) : IsFibration E := by
  intro a a' f y
  obtain ⟨x, φ, H⟩ := hD f (e.inverse.obj y)
  exact ⟨e.functor.obj x, e.functor.map φ ≫ᵈ e.counitIso.app y,
    IsCartesian.comp_iso (e.isCartesian_map H) _ (e.counitIso.inv y) (e.counitIso.inv_app y)
      (e.counitIso.app_inv y)⟩

end DEquivalence

/-! ### Total categories -/

/-- The functor between total categories induced by a displayed functor. -/
def DFunctor.total (F : DFunctor D E) : D.Total ⥤ E.Total where
  obj X := ⟨X.1, F.obj X.2⟩
  map g := ⟨g.base, F.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor induced by a displayed functor lies over `A`, strictly. -/
theorem DFunctor.total_comp_π (F : DFunctor D E) : F.total ⋙ E.π = D.π :=
  rfl

/-- The natural isomorphism between total functors induced by a vertical natural isomorphism. -/
def VNatIso.total {F G : DFunctor D E} (η : VNatIso F G) : F.total ≅ G.total :=
  NatIso.ofComponents
    (fun X =>
      { hom := ⟨𝟙 X.1, η.app X.2⟩
        inv := ⟨𝟙 X.1, η.inv X.2⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun {X Y} g => (congrArg (Total.Hom.mk (x := F.total.obj X) (y := G.total.obj Y) g.base)
      (η.naturality g.fiber).symm :))

/-- The components of `VNatIso.total` are vertical: they lie over identities. -/
theorem VNatIso.π_map_total_hom {F G : DFunctor D E} (η : VNatIso F G) (X : D.Total) :
    E.π.map (η.total.hom.app X) = 𝟙 X.1 :=
  rfl

/-- **A displayed equivalence induces an equivalence of the total categories over `A`**: its
functors commute with the projections to `A` (`DEquivalence.total_functor_comp_π`), and the
components of its unit and counit lie over identities. -/
def DEquivalence.total (e : DEquivalence D E) : D.Total ≌ E.Total :=
  CategoryTheory.Equivalence.mk e.functor.total e.inverse.total e.unitIso.total e.counitIso.total

theorem DEquivalence.total_functor_comp_π (e : DEquivalence D E) :
    e.total.functor ⋙ E.π = D.π :=
  rfl

theorem DEquivalence.total_inverse_comp_π (e : DEquivalence D E) :
    e.total.inverse ⋙ D.π = E.π :=
  rfl

end DFunctor

end Displayed

end Nfib
