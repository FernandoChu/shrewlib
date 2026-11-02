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

Conversely, a fully faithful vertical functor (`VertFunctor.FullyFaithful`: an inverse to its action
on each displayed hom-type, as data) with chosen preimages `F (G y) ≅ y` of every object is an
equivalence over the base (`VertEquivalence.ofFullyFaithful`). The inverse sends `ψ` to the
preimage of `ψ` conjugated by these isomorphisms.

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
natural isomorphisms `𝟭 ≅ F ⋙ᵥ G` and `G ⋙ᵥ F ≅ 𝟭`. -/
structure VertEquivalence (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) :
    Type _ where
  /-- The functor. -/
  functor : VertFunctor D E
  /-- The inverse functor. -/
  inverse : VertFunctor E D
  /-- The unit. -/
  unitIso : VertFunctor.id D ≅ functor ⋙ᵥ inverse
  /-- The counit. -/
  counitIso : inverse ⋙ᵥ functor ≅ VertFunctor.id E

section FullyFaithful

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}

/-- A fully faithful vertical functor: an inverse to its action on each displayed hom-type, in
the style of Mathlib's `Functor.FullyFaithful`. -/
structure VertFunctor.FullyFaithful (F : VertFunctor D E) where
  /-- The preimage of a displayed morphism. -/
  preimage : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'},
    (F.obj x ⟶[f] F.obj y) → (x ⟶[f] y)
  map_preimage : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : F.obj x ⟶[f] F.obj y), F.map (preimage ψ) = ψ
  preimage_map : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
    preimage (F.map φ) = φ

namespace VertFunctor.FullyFaithful

variable {F : VertFunctor D E}

theorem map_injective (hF : F.FullyFaithful) {a a' : A} {f : a ⟶ a'} {x : D.Ob a}
    {y : D.Ob a'} {φ φ' : x ⟶[f] y} (h : F.map φ = F.map φ') : φ = φ' :=
  (hF.preimage_map φ).symm.trans ((congrArg hF.preimage h).trans (hF.preimage_map φ'))

/-- The composite of fully faithful vertical functors is fully faithful. -/
def comp {E' : Displayed.{v₁, u₁, v₂, u₂} A} {G : VertFunctor E E'} (hF : F.FullyFaithful)
    (hG : G.FullyFaithful) : (F ⋙ᵥ G).FullyFaithful where
  preimage ψ := hF.preimage (hG.preimage ψ)
  map_preimage ψ := (congrArg G.map (hF.map_preimage _)).trans (hG.map_preimage ψ)
  preimage_map φ := (congrArg hF.preimage (hG.preimage_map _)).trans (hF.preimage_map φ)

end VertFunctor.FullyFaithful

end FullyFaithful

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

/-- The preimage of `ψ : F x ⟶[f] F y`: `G ψ`, conjugated by the unit. -/
def preimage {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : x ⟶[f] y :=
  (e.unitIso.hom.app x ≫ᵈ (e.inverse.map ψ ≫ᵈ e.unitIso.inv.app y) :)

theorem map_preimage {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : e.functor.map (e.preimage ψ) = ψ := by
  let η := e.unitIso
  refine e.symm.map_injective ?_
  -- Conjugating `eq_conj φ` back with the unit, both sides cancel to `G (F φ)` and `G ψ`.
  have c := congrArg (fun t => η.inv.app x ≫ᵈ (t ≫ᵈ η.hom.app y)) (e.eq_conj (e.preimage ψ))
  have hL := (VertNatIso.inv_hom_id_app_assoc η x _).trans
    (congrArg (e.inverse.map ψ ≫ᵈ ·) (VertNatIso.inv_hom_id_app η y))
  have hR := (VertNatIso.inv_hom_id_app_assoc η x _).trans
    (congrArg (e.inverse.map (e.functor.map (e.preimage ψ)) ≫ᵈ ·)
      (VertNatIso.inv_hom_id_app η y))
  exact (hR.symm.trans (c.symm.trans hL) :)

/-- A vertical equivalence is full on displayed hom-types. -/
theorem map_surjective {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : ∃ φ : x ⟶[f] y, e.functor.map φ = ψ :=
  ⟨e.preimage ψ, e.map_preimage ψ⟩

/-- The functor of a vertical equivalence is fully faithful. -/
def fullyFaithful : e.functor.FullyFaithful where
  preimage ψ := e.preimage ψ
  map_preimage ψ := e.map_preimage ψ
  preimage_map _ := e.map_injective (e.map_preimage _)

/-! ## From a fully faithful functor with chosen preimages up to isomorphism -/

section OfFullyFaithful

variable {F : VertFunctor D E} (hF : F.FullyFaithful)
  (G : ∀ {a : A}, E.Ob a → D.Ob a) (ε : ∀ {a : A} (y : E.Ob a), (F.obj (G y) : E.Fiber a) ≅ y)

/-- `ψ`, conjugated by the chosen isomorphisms `F (G y) ≅ y`. -/
def conj {a a' : A} {f : a ⟶ a'} {y : E.Ob a} {y' : E.Ob a'} (ψ : y ⟶[f] y') :
    F.obj (G y) ⟶[f] F.obj (G y') :=
  ((ε y).hom ≫ᵈ (ψ ≫ᵈ (ε y').inv) :)

/-- The inverse of a fully faithful vertical functor with chosen preimages `F (G y) ≅ y`: a
morphism `ψ` goes to the preimage of `ψ` conjugated by these isomorphisms. -/
def inverseOfFullyFaithful : VertFunctor E D where
  obj y := G y
  map ψ := hF.preimage (conj G ε ψ)
  map_id y := hF.map_injective ((hF.map_preimage _).trans
    (((ε y).hom_inv_id :).trans (F.map_id (G y)).symm))
  map_comp {_ _ _ _ _ y y' y''} ψ ψ' := hF.map_injective ((hF.map_preimage _).trans
    ((congrArg (fun t => (ε y).hom ≫ᵈ (ψ ≫ᵈ t))
      ((ε y').inv_hom_id_displayed (ψ' ≫ᵈ (ε y'').inv))).symm.trans
        ((congrArg₂ (· ≫ᵈ ·) (hF.map_preimage (conj G ε ψ))
          (hF.map_preimage (conj G ε ψ'))).symm.trans (F.map_comp _ _).symm)))

/-- The unit at `x`: the preimage of `F x ≅ F (G (F x))`. -/
def unitApp {a : A} (x : D.Ob a) : x ⟶[𝟙 a] G (F.obj x) :=
  hF.preimage (show F.obj x ⟶[𝟙 a] F.obj (G (F.obj x)) from (ε (F.obj x)).inv)

/-- The inverse of the unit at `x`. -/
def unitInvApp {a : A} (x : D.Ob a) : G (F.obj x) ⟶[𝟙 a] x :=
  hF.preimage (show F.obj (G (F.obj x)) ⟶[𝟙 a] F.obj x from (ε (F.obj x)).hom)

/-- **A fully faithful vertical functor with chosen preimages `F (G y) ≅ y` is an equivalence
over the base.** -/
def ofFullyFaithful : VertEquivalence D E where
  functor := F
  inverse := inverseOfFullyFaithful hF G ε
  unitIso := VertNatIso.ofComponents
    (fun x =>
      { hom := unitApp hF G ε x
        inv := unitInvApp hF G ε x
        hom_inv_id := hF.map_injective ((F.map_comp _ _).trans ((congrArg₂ (· ≫ᵈ ·)
          (hF.map_preimage _) (hF.map_preimage _)).trans
            (((ε (F.obj x)).inv_hom_id :).trans (F.map_id x).symm)))
        inv_hom_id := hF.map_injective ((F.map_comp _ _).trans ((congrArg₂ (· ≫ᵈ ·)
          (hF.map_preimage _) (hF.map_preimage _)).trans
            (((ε (F.obj x)).hom_inv_id :).trans (F.map_id _).symm))) })
    (fun {_ _ _ x _} φ => hF.map_injective ((F.map_comp _ _).trans
      ((congrArg (F.map φ ≫ᵈ ·) (hF.map_preimage _)).trans
        ((((ε (F.obj x)).inv_hom_id_displayed _).symm.trans
          (congrArg₂ (· ≫ᵈ ·) (hF.map_preimage _)
            (hF.map_preimage (conj G ε (F.map φ)))).symm).trans (F.map_comp _ _).symm))))
  counitIso := VertNatIso.ofComponents (fun y => ε y)
    (fun {_ _ _ y y'} ψ => (congrArg (· ≫ᵈ (ε y').hom) (hF.map_preimage (conj G ε ψ))).trans
      (congrArg (fun t => (ε y).hom ≫ᵈ (ψ ≫ᵈ t)) (ε y').inv_hom_id :))

end OfFullyFaithful

end VertEquivalence

end Displayed
