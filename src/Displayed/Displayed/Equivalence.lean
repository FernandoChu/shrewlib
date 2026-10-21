import Displayed.Displayed.Basic

/-!
# Equivalences over the base

An *equivalence over `A`* (`VertEquivalence`) between displayed categories over `A` is a pair of
vertical functors with vertical natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`: their components
lie over identities. We show:

a vertical equivalence is fully faithful on displayed hom-types over each base morphism
(`VertEquivalence.map_injective`, `VertEquivalence.map_surjective`). That it preserves
(op)cartesian morphisms is in `Displayed/Fibration/Basic.lean` and
`Displayed/Opfibration/Basic.lean`.

The induced equivalence of total categories is `VertEquivalence.total` in
`Displayed/Displayed/Total.lean`, and the transfer of cleavages along a vertical equivalence is in
`Displayed/Fibration/` and `Displayed/Opfibration/`.
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

end VertEquivalence

end Displayed
