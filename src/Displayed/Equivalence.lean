import Displayed.Cartesian

/-!
# Equivalences over the base

An *equivalence over `A`* (`VertEquivalence`) between displayed categories over `A` is a pair of
vertical functors with vertical natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`: their components
lie over identities. We show:

* a vertical equivalence is fully faithful on displayed hom-types over each base morphism
  (`VertEquivalence.map_injective`, `VertEquivalence.map_surjective`);
* it preserves cartesian and opcartesian morphisms (`VertEquivalence.isCartesian_map`,
  `VertEquivalence.isOpcartesian_map`).

The induced equivalence of total categories is `VertEquivalence.total` in `Displayed/Total.lean`,
and the transfer of cleavages along a vertical equivalence is in `Displayed/Fibration/`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A]

/-- An equivalence of categories over `A`: vertical functors in both directions, with vertical
natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`. -/
structure VertEquivalence (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) :
    Type _ where
  /-- The functor. -/
  functor : VertFunctor D E
  /-- The inverse functor. -/
  inverse : VertFunctor E D
  /-- The unit. -/
  unitIso : VertFunctor.id D ≅ functor.comp inverse
  /-- The counit. -/
  counitIso : inverse.comp functor ≅ VertFunctor.id E

namespace VertEquivalence

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}
  (e : VertEquivalence D E)

/-- The inverse equivalence. -/
def symm : VertEquivalence E D where
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- A displayed morphism, recovered from its image under `F ⋙ G` by conjugating with the unit. -/
theorem eq_conj {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    φ = e.unitIso.hom.app x ≫ᵈ (e.inverse.map (e.functor.map φ) ≫ᵈ e.unitIso.inv.app y) :=
  ((congrArg (φ ≫ᵈ ·) (VertNatIso.hom_inv_id_app e.unitIso y)).symm.trans
    (congrArg (· ≫ᵈ e.unitIso.inv.app y) (e.unitIso.hom.naturality φ)) :)

/-- A vertical equivalence is faithful on displayed hom-types. -/
theorem map_injective {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ φ' : x ⟶[f] y}
    (h : e.functor.map φ = e.functor.map φ') : φ = φ' :=
  (e.eq_conj φ).trans ((congrArg (fun t =>
    e.unitIso.hom.app x ≫ᵈ (e.inverse.map t ≫ᵈ e.unitIso.inv.app y)) h).trans (e.eq_conj φ').symm)

/-- A vertical equivalence is full on displayed hom-types. -/
theorem map_surjective {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : ∃ φ : x ⟶[f] y, e.functor.map φ = ψ := by
  let η := e.unitIso
  let φ : x ⟶[f] y := (η.hom.app x ≫ᵈ (e.inverse.map ψ ≫ᵈ η.inv.app y) :)
  refine ⟨φ, e.symm.map_injective ?_⟩
  -- Conjugating `eq_conj φ` back with the unit, both sides cancel to `G (F φ)` and `G ψ`.
  have c := congrArg (fun t => η.inv.app x ≫ᵈ (t ≫ᵈ η.hom.app y)) (e.eq_conj φ)
  have hL := (VertNatIso.inv_hom_id_app_assoc η x _).trans
    (congrArg (e.inverse.map ψ ≫ᵈ ·) (VertNatIso.inv_hom_id_app η y))
  have hR := (VertNatIso.inv_hom_id_app_assoc η x _).trans
    (congrArg (e.inverse.map (e.functor.map φ) ≫ᵈ ·) (VertNatIso.inv_hom_id_app η y))
  exact (hR.symm.trans (c.symm.trans hL) :)

/-- **A vertical equivalence preserves cartesian morphisms.** -/
theorem isCartesian_map {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsCartesian φ) : IsCartesian (e.functor.map φ) := by
  intro a₀ g z χ
  let ε := e.counitIso
  obtain ⟨χ', hχ'⟩ := e.map_surjective (ε.hom.app z ≫ᵈ χ :)
  refine ⟨(ε.inv.app z ≫ᵈ e.functor.map (IsCartesian.lift H g χ') :), ?_, fun ψ hψ => ?_⟩
  · exact (((congrArg (fun t => ε.inv.app z ≫ᵈ e.functor.map t)
      (IsCartesian.lift_fac H g χ')).trans (congrArg (ε.inv.app z ≫ᵈ ·) hχ')).trans
        (VertNatIso.inv_hom_id_app_assoc ε z χ) :)
  · obtain ⟨ψ', hψ'⟩ := e.map_surjective (ε.hom.app z ≫ᵈ ψ :)
    have h₁ : ψ' ≫ᵈ φ = χ' := e.map_injective
      ((congrArg (· ≫ᵈ e.functor.map φ) hψ').trans
        ((congrArg (ε.hom.app z ≫ᵈ ·) hψ).trans hχ'.symm) :)
    have h₂ : ψ' = IsCartesian.lift H g χ' := IsCartesian.lift_uniq H ψ' h₁
    exact ((VertNatIso.inv_hom_id_app_assoc ε z ψ).symm.trans
      (congrArg (ε.inv.app z ≫ᵈ ·) (hψ'.symm.trans (congrArg e.functor.map h₂))) :)

/-- **A vertical equivalence preserves opcartesian morphisms.** -/
theorem isOpcartesian_map {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsOpcartesian φ) : IsOpcartesian (e.functor.map φ) := by
  intro a'' g z χ
  let ε := e.counitIso
  obtain ⟨χ', hχ'⟩ := e.map_surjective (χ ≫ᵈ ε.inv.app z :)
  refine ⟨(e.functor.map (IsOpcartesian.desc H g χ') ≫ᵈ ε.hom.app z :), ?_, fun ψ hψ => ?_⟩
  · exact (((congrArg (fun t => e.functor.map t ≫ᵈ ε.hom.app z)
      (IsOpcartesian.desc_fac H g χ')).trans (congrArg (· ≫ᵈ ε.hom.app z) hχ')).trans
        (congrArg (χ ≫ᵈ ·) (VertNatIso.inv_hom_id_app ε z)) :)
  · obtain ⟨ψ', hψ'⟩ := e.map_surjective (ψ ≫ᵈ ε.inv.app z :)
    have h₁ : φ ≫ᵈ ψ' = χ' := e.map_injective
      ((congrArg (e.functor.map φ ≫ᵈ ·) hψ').trans
        ((congrArg (· ≫ᵈ ε.inv.app z) hψ).trans hχ'.symm) :)
    have h₂ : ψ' = IsOpcartesian.desc H g χ' := IsOpcartesian.desc_uniq H ψ' h₁
    exact ((congrArg (ψ ≫ᵈ ·) (VertNatIso.inv_hom_id_app ε z)).symm.trans
      (congrArg (· ≫ᵈ ε.hom.app z) (hψ'.symm.trans (congrArg e.functor.map h₂))) :)

end VertEquivalence

end Displayed
