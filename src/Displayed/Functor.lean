import Displayed.Cartesian
import Displayed.Total
import Mathlib.CategoryTheory.Equivalence

/-!
# Displayed functors and equivalences over the base

Categories over `A` and functors over `A` are displayed categories over `A` and displayed functors
over the identity (`VertFunctor`). An *equivalence over `A`* (`VertEquivalence`) is a pair of
displayed functors with vertical natural isomorphisms (`VertNatIso`) `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`:
their components lie over identities. We show:

* a displayed equivalence is fully faithful on displayed hom-types over each base morphism
  (`VertEquivalence.map_injective`, `VertEquivalence.map_surjective`);
* it preserves cartesian and opcartesian morphisms (`VertEquivalence.isCartesian_map`,
  `VertEquivalence.isOpcartesian_map`);
* it induces an equivalence of the total categories commuting with the projections to `A`
  (`VertEquivalence.total`).

Cleavages transfer along displayed equivalences in `Transfer.lean`. This file and `Opfib.lean`,
`Fib.lean` do not import each other: the cancellation rules of vertical natural isomorphisms here
and the interchange rules there are keyed on displayed composition, and trying them on every
composite of the other files is too slow.

The laws of displayed functors, and the cancellation of vertical natural isomorphisms with their
inverses, are rewrite rules.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A]

section VertFunctor

/-- A displayed functor over the identity of `A`, i.e. a functor over `A` between the total
categories. -/
structure VertFunctor (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) where
  /-- The action on objects, fiberwise. -/
  obj : {a : A} → D.Ob a → E.Ob a
  /-- The action on morphisms, over the same base morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : D.Ob a} → {y : D.Ob a'} → (x ⟶[f] y) →
    (obj x ⟶[f] obj y)
  map_id : ∀ {a : A} (x : D.Ob a), map (𝟙ᵈ x) = 𝟙ᵈ (obj x)
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z), map (φ ≫ᵈ ψ) = map φ ≫ᵈ map ψ

attribute [rewrite_rule] VertFunctor.map_id VertFunctor.map_comp

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}
  {E' : Displayed.{v₁, u₁, v₂, u₂} A}

/-- The identity displayed functor. -/
def VertFunctor.id (D : Displayed.{v₁, u₁, v₂, u₂} A) : VertFunctor D D where
  obj x := x
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of displayed functors. -/
def VertFunctor.comp (F : VertFunctor D E) (G : VertFunctor E E') : VertFunctor D E' where
  obj x := G.obj (F.obj x)
  map φ := G.map (F.map φ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A vertical natural isomorphism between displayed functors: its components lie over identities,
and it is natural with respect to displayed morphisms over arbitrary base morphisms. -/
structure VertNatIso (F G : VertFunctor D E) where
  /-- The components. -/
  app : ∀ {a : A} (x : D.Ob a), F.obj x ⟶[𝟙 a] G.obj x
  /-- The components of the inverse. -/
  inv : ∀ {a : A} (x : D.Ob a), G.obj x ⟶[𝟙 a] F.obj x
  app_inv : ∀ {a : A} (x : D.Ob a), app x ≫ᵈ inv x = 𝟙ᵈ (F.obj x)
  inv_app : ∀ {a : A} (x : D.Ob a), inv x ≫ᵈ app x = 𝟙ᵈ (G.obj x)
  naturality : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
    app x ≫ᵈ G.map φ = F.map φ ≫ᵈ app y

namespace VertNatIso

variable {F G : VertFunctor D E} (η : VertNatIso F G)

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
def symm : VertNatIso G F where
  app := η.inv
  inv := η.app
  app_inv := η.inv_app
  inv_app := η.app_inv
  naturality := η.inv_naturality

end VertNatIso

/-- An equivalence of categories over `A`: displayed functors in both directions, with vertical
natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`. -/
structure VertEquivalence (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) :
    Type _ where
  /-- The functor. -/
  functor : VertFunctor D E
  /-- The inverse functor. -/
  inverse : VertFunctor E D
  /-- The unit. -/
  unitIso : VertNatIso (VertFunctor.id D) (functor.comp inverse)
  /-- The counit. -/
  counitIso : VertNatIso (inverse.comp functor) (VertFunctor.id E)

namespace VertEquivalence

variable (e : VertEquivalence D E)

/-- The inverse equivalence. -/
def symm : VertEquivalence E D where
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

/-- **A displayed equivalence preserves opcartesian morphisms.** -/
theorem isOpcartesian_map {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsOpcartesian φ) : IsOpcartesian (e.functor.map φ) := by
  intro a'' g z χ
  let ε := e.counitIso
  obtain ⟨χ', hχ'⟩ := e.map_surjective (χ ≫ᵈ ε.inv z :)
  refine ⟨(e.functor.map (IsOpcartesian.desc H g χ') ≫ᵈ ε.app z :), ?_, fun ψ hψ => ?_⟩
  · exact ((congrArg (fun t => e.functor.map t ≫ᵈ ε.app z) (IsOpcartesian.desc_fac H g χ')).trans
      (congrArg (· ≫ᵈ ε.app z) hχ') :)
  · obtain ⟨ψ', hψ'⟩ := e.map_surjective (ψ ≫ᵈ ε.inv z :)
    have h₁ : φ ≫ᵈ ψ' = χ' := e.map_injective
      ((congrArg (e.functor.map φ ≫ᵈ ·) hψ').trans ((congrArg (· ≫ᵈ ε.inv z) hψ).trans hχ'.symm) :)
    have h₂ : ψ' = IsOpcartesian.desc H g χ' := IsOpcartesian.desc_uniq H ψ' h₁
    exact (congrArg (· ≫ᵈ ε.app z) (hψ'.symm.trans (congrArg e.functor.map h₂)) :)

end VertEquivalence

/-! ### Total categories -/

/-- The functor between total categories induced by a displayed functor. -/
def VertFunctor.total (F : VertFunctor D E) : D.Total ⥤ E.Total where
  obj X := ⟨X.1, F.obj X.2⟩
  map g := ⟨g.base, F.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor induced by a displayed functor lies over `A`, strictly. -/
theorem VertFunctor.total_comp_π (F : VertFunctor D E) : F.total ⋙ E.π = D.π :=
  rfl

/-- The natural isomorphism between total functors induced by a vertical natural isomorphism. -/
def VertNatIso.total {F G : VertFunctor D E} (η : VertNatIso F G) : F.total ≅ G.total :=
  NatIso.ofComponents
    (fun X =>
      { hom := ⟨𝟙 X.1, η.app X.2⟩
        inv := ⟨𝟙 X.1, η.inv X.2⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun {X Y} g => (congrArg (Total.Hom.mk (x := F.total.obj X) (y := G.total.obj Y) g.base)
      (η.naturality g.fiber).symm :))

/-- The components of `VertNatIso.total` are vertical: they lie over identities. -/
theorem VertNatIso.π_map_total_hom {F G : VertFunctor D E} (η : VertNatIso F G) (X : D.Total) :
    E.π.map (η.total.hom.app X) = 𝟙 X.1 :=
  rfl

/-- **A displayed equivalence induces an equivalence of the total categories over `A`**: its
functors commute with the projections to `A` (`VertEquivalence.total_functor_comp_π`), and the
components of its unit and counit lie over identities. -/
def VertEquivalence.total (e : VertEquivalence D E) : D.Total ≌ E.Total :=
  CategoryTheory.Equivalence.mk e.functor.total e.inverse.total e.unitIso.total e.counitIso.total

theorem VertEquivalence.total_functor_comp_π (e : VertEquivalence D E) :
    e.total.functor ⋙ E.π = D.π :=
  rfl

theorem VertEquivalence.total_inverse_comp_π (e : VertEquivalence D E) :
    e.total.inverse ⋙ D.π = E.π :=
  rfl

end VertFunctor

end Displayed
