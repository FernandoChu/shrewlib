import TwoCategory.Monad.PseudoAlgebra
import TwoCategory.Adjunction

/-!
# Lax idempotent 2-monads

A 2-monad `M = (T, η, μ)` on a 2-category `C` is *lax idempotent* (or *Kock–Zöberlein*) if it comes
with a modification `δ : Tη ⟶ ηT`, that is 2-cells `δ x : T η_x ⟶ η_{T x}` natural in `x`, with
```
  δ x ▷ μ x = 𝟙 (𝟙 (T x))        η x ◁ δ x = 𝟙 (η x ≫ η (T x))
```
The types of these equations agree by the unit laws of `M` and the naturality of `η`, which are
rules (`TwoMonad`). Equivalently, `T η_x ⊣ μ_x` with identity unit, and counit `T δ_x ▷ μ_{T x}`
(`LaxIdempotent.mapηAdjunction`), see Kelly–Lack, *On property-like structures*.

The point of lax idempotence is that algebra structures on `x` are adjoint to the unit `η_x`:

| structure on `η_x`                             | `M`-algebra structure on `x`                   |
|------------------------------------------------|------------------------------------------------|
| left adjoint with invertible counit            | pseudo-algebra (`pseudoAlgEquiv`)              |
| left adjoint left inverse (LALI)               | normal pseudo-algebra (`normalPseudoAlgEquiv`) |
| LALI `a` with `μ_x ≫ a = T a ≫ a`              | strict algebra (`algEquiv`)                    |

Here a LALI of `η_x` is a left adjoint `a ⊣ η_x` with identity counit, so a retraction of `η_x`
(`Reflection`), and it is *split* if it satisfies the associativity law of an algebra
(`SplitReflection`). The pseudo-algebras of `M` are the left adjoints `a ⊣ η_x` with invertible
counit (`PseudoReflection`):

* given a pseudo-algebra `(a, ζ, α)`, `a ⊣ η_x` with counit `ζ` and unit
  `T ζ⁻¹ ≫ δ_x ▷ T a : 𝟙 ⟶ T η_x ≫ T a ⟶ η_{T x} ≫ T a = a ≫ η_x` (`PseudoAlg.toPseudoReflection`);
* conversely, given `a ⊣ η_x` with invertible counit `ζ`, the associativity 2-cell is
  `α = μ_x ◁ T ζ⁻¹ ▷ a ≫ (T δ_x ▷ μ_{T x}) ▷ T a ▷ a : μ_x ≫ a ⟶ μ_x ≫ T η_x ≫ T a ≫ a ⟶ T a ≫ a`
  (`PseudoReflection.toPseudoAlg`), with inverse
  `(δ_{T x} ▷ T μ_x) ▷ T a ▷ a ≫ μ_x ◁ a ◁ ζ : T a ≫ a ⟶ μ_x ≫ η_{T x} ≫ T a ≫ a ⟶ μ_x ≫ a`.

These are inverse. By `T η_x ⊣ μ_x`, a 2-cell out of `μ_x ≫ g` is determined by its whiskering
with `T η_x` (`LaxIdempotent.hom_ext_μ`), so `α` is determined by `ζ` through the unit law
`T η_x ◁ α ≫ T ζ ▷ a = 𝟙`. By `a ⊣ η_x`, a 2-cell into `a ≫ η_x` is determined by its whiskering
with `η_x` (`Adjunction.hom_ext_to`), so the unit is determined by `ζ` through the triangle law
`η_x ◁ η ≫ ζ ▷ η_x = 𝟙`. In the same way, the invertibility of `α` and the laws of a
pseudo-algebra reduce to the triangle laws of `a ⊣ η_x`. Normal pseudo-algebras and LALIs are the
case `ζ = 𝟙`.

Splitness is not implied by the adjunction: a LALI is a normal pseudo-algebra structure, not
necessarily a strict one. For split retractions, the adjunction is `Retraction.adjunction`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {C : Type u} [TwoCategory.{w, v} C]

namespace TwoMonad

variable (M : TwoMonad C)

/-! ## Lax idempotence -/

/-- A lax idempotent 2-monad: a modification `δ : Tη ⟶ ηT` with `δ ▷ μ = 𝟙` and `η ◁ δ = 𝟙`. -/
structure LaxIdempotent where
  /-- The modification `δ x : T η_x ⟶ η_{T x}`. -/
  δ (x : C) : M.T.map (M.η x) ⟶ M.η (M.T.obj x)
  δ_naturality {x y : C} (m : x ⟶ y) : δ x ▷ M.T.map (M.T.map m) = M.T.map m ◁ δ y
  δ_whiskerRight_μ (x : C) : δ x ▷ M.μ x = 𝟙 (𝟙 (M.T.obj x))
  η_whiskerLeft_δ (x : C) : M.η x ◁ δ x = 𝟙 (M.η x ≫ M.η (M.T.obj x))

variable {M}

namespace LaxIdempotent

variable (K : M.LaxIdempotent)

/-! ## `T η_x ⊣ μ_x` -/

/-- The counit `T δ_x ▷ μ_{T x} : μ_x ≫ T η_x ⟶ 𝟙` of `T η_x ⊣ μ_x`. -/
def mapηCounit (x : C) : M.μ x ≫ M.T.map (M.η x) ⟶ 𝟙 (M.T.obj (M.T.obj x)) :=
  M.T.map₂ (K.δ x) ▷ M.μ (M.T.obj x)

/-- **`T η_x ⊣ μ_x`**, with identity unit. -/
def mapηAdjunction (x : C) : M.T.map (M.η x) ⊣ M.μ x where
  unit := 𝟙 _
  counit := K.mapηCounit x
  left_triangle := by
    kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ M.μ (M.T.obj x)) (K.η_whiskerLeft_δ x)
  right_triangle := by
    kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ M.μ x) (K.δ_whiskerRight_μ x)

include K in
/-- A 2-cell out of `μ_x ≫ g` is determined by its whiskering with `T η_x`. -/
theorem hom_ext_μ {x z : C} {g : M.T.obj x ⟶ z} {f : M.T.obj (M.T.obj x) ⟶ z}
    {φ ψ : M.μ x ≫ g ⟶ f} (h : M.T.map (M.η x) ◁ φ = M.T.map (M.η x) ◁ ψ) : φ = ψ :=
  Adjunction.hom_ext_from (K.mapηAdjunction x) h

/-! ## The 2-cells of the correspondence

For a 1-cell `a : T x ⟶ x` and an invertible 2-cell `ζ : η_x ≫ a ≅ 𝟙`, the unit `adjUnitOf ζ` of
the adjunction `a ⊣ η_x` with counit `ζ`, and the associativity 2-cell `assocHomOf ζ` of the
pseudo-algebra with unit 2-cell `ζ`, with its inverse `assocInvOf ζ`. -/

variable {x : C} {a : M.T.obj x ⟶ x} (ζ : M.η x ≫ a ≅ 𝟙 x)

/-- The unit `T ζ⁻¹ ≫ δ_x ▷ T a : 𝟙 ⟶ a ≫ η_x`. -/
def adjUnitOf : 𝟙 (M.T.obj x) ⟶ a ≫ M.η x :=
  M.T.map₂ ζ.inv ≫ K.δ x ▷ M.T.map a

/-- The associativity 2-cell `μ_x ◁ T ζ⁻¹ ▷ a ≫ (T δ_x ▷ μ_{T x}) ▷ T a ▷ a : μ_x ≫ a ⟶ T a ≫ a`. -/
def assocHomOf : M.μ x ≫ a ⟶ M.T.map a ≫ a :=
  M.μ x ◁ M.T.map₂ ζ.inv ▷ a ≫ K.mapηCounit x ▷ M.T.map a ▷ a

/-- The inverse `(δ_{T x} ▷ T μ_x) ▷ T a ▷ a ≫ μ_x ◁ a ◁ ζ : T a ≫ a ⟶ μ_x ≫ a`. -/
def assocInvOf : M.T.map a ≫ a ⟶ M.μ x ≫ a :=
  K.δ (M.T.obj x) ▷ M.T.map (M.μ x) ▷ M.T.map a ▷ a ≫ M.μ x ◁ a ◁ ζ.hom

theorem η_whiskerLeft_adjUnitOf : M.η x ◁ K.adjUnitOf ζ = ζ.inv ▷ M.η x := by
  have h₁ : M.η x ◁ M.T.map₂ ζ.inv = ζ.inv ▷ M.η x := M.η_naturality₂ ζ.inv
  have h₂ : M.η x ◁ K.δ x ▷ M.T.map a = 𝟙 _ := by
    kernel_exact congrArg (· ▷ M.T.map a) (K.η_whiskerLeft_δ x)
  kernel_exact (congrArg₂ (· ≫ ·) h₁ h₂).trans (Category.comp_id _)

/-- The triangle law of `a ⊣ η_x` involving `η_x`, which holds for every `ζ`. -/
theorem adjUnitOf_right_triangle : M.η x ◁ K.adjUnitOf ζ ≫ ζ.hom ▷ M.η x = 𝟙 (M.η x) := by
  have h : ζ.inv ▷ M.η x ≫ ζ.hom ▷ M.η x = 𝟙 _ := by
    kernel_exact congrArg (· ▷ M.η x) ζ.inv_hom_id
  kernel_exact (congrArg (· ≫ ζ.hom ▷ M.η x) (K.η_whiskerLeft_adjUnitOf ζ)).trans h

theorem mapη_whiskerLeft_assocHomOf :
    M.T.map (M.η x) ◁ K.assocHomOf ζ = M.T.map₂ ζ.inv ▷ a := by
  have h : M.T.map (M.η x) ◁ M.T.map₂ (K.δ x) ▷ M.μ (M.T.obj x) ▷ M.T.map a ▷ a = 𝟙 _ := by
    kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ M.μ (M.T.obj x) ▷ M.T.map a ▷ a)
      (K.η_whiskerLeft_δ x)
  kernel_exact (congrArg (M.T.map₂ ζ.inv ▷ a ≫ ·) h).trans (Category.comp_id _)

theorem η_whiskerLeft_assocHomOf : M.η (M.T.obj x) ◁ K.assocHomOf ζ = K.adjUnitOf ζ ▷ a := by
  have h : M.η (M.T.obj x) ◁ M.T.map₂ (K.δ x) ▷ M.μ (M.T.obj x) ▷ M.T.map a ▷ a =
      K.δ x ▷ M.T.map a ▷ a := by
    kernel_exact congrArg (· ▷ M.μ (M.T.obj x) ▷ M.T.map a ▷ a) (M.η_naturality₂ (K.δ x))
  kernel_exact congrArg (M.T.map₂ ζ.inv ▷ a ≫ ·) h

theorem mapη_whiskerLeft_assocInvOf :
    M.T.map (M.η x) ◁ K.assocInvOf ζ = K.δ x ▷ M.T.map a ▷ a ≫ a ◁ ζ.hom := by
  have h : M.T.map (M.η x) ◁ K.δ (M.T.obj x) ▷ M.T.map (M.μ x) ▷ M.T.map a ▷ a =
      K.δ x ▷ M.T.map a ▷ a := by
    kernel_exact congrArg (· ▷ M.T.map (M.μ x) ▷ M.T.map a ▷ a) (K.δ_naturality (M.η x)).symm
  kernel_exact congrArg (· ≫ a ◁ ζ.hom) h

end LaxIdempotent

/-! ## Pseudo-algebras are left adjoints of units with invertible counit -/

/-- A left adjoint `a ⊣ η_x` of the unit with invertible counit. -/
structure PseudoReflection (x : C) where
  /-- The left adjoint `a`. -/
  act : M.T.obj x ⟶ x
  /-- The adjunction `a ⊣ η_x`. -/
  adj : act ⊣ M.η x
  /-- The counit, as an isomorphism. -/
  counitIso : M.η x ≫ act ≅ 𝟙 x
  counit_eq : adj.counit = counitIso.hom

namespace PseudoAlg

variable (K : M.LaxIdempotent) (A : M.PseudoAlg)

theorem whiskerLeft_unitIso_hom :
    A.act ◁ A.unitIso.hom = M.η (M.T.obj A.obj) ◁ A.assocIso.inv :=
  (Iso.hom_comp_eq_id (whiskerLeftIso _ A.assocIso)).1 A.unit_left

theorem map₂_unitIso_hom_whiskerRight :
    M.T.map₂ A.unitIso.hom ▷ A.act = M.T.map (M.η A.obj) ◁ A.assocIso.inv :=
  (Iso.hom_comp_eq_id (whiskerLeftIso _ A.assocIso)).1 A.unit_right

theorem mapη_whiskerLeft_assocIso_hom :
    M.T.map (M.η A.obj) ◁ A.assocIso.hom = M.T.map₂ A.unitIso.inv ▷ A.act :=
  (Iso.comp_hom_eq_id (whiskerRightIso (M.T.map₂Iso A.unitIso) A.act)).1 A.unit_right

/-- The associativity 2-cell of a pseudo-algebra of a lax idempotent 2-monad is determined by its
unit 2-cell. -/
theorem assocIso_hom_eq : A.assocIso.hom = K.assocHomOf A.unitIso :=
  K.hom_ext_μ ((A.mapη_whiskerLeft_assocIso_hom).trans
    (K.mapη_whiskerLeft_assocHomOf A.unitIso).symm)

/-- `δ_x ▷ T a ▷ a ≫ a ◁ ζ = T ζ ▷ a`, by the unit laws of the pseudo-algebra. -/
theorem δ_whiskerRight_comp_whiskerLeft_unitIso_hom :
    K.δ A.obj ▷ M.T.map A.act ▷ A.act ≫ A.act ◁ A.unitIso.hom =
      M.T.map₂ A.unitIso.hom ▷ A.act := by
  have ex : M.T.map (M.η A.obj) ◁ A.assocIso.inv ≫ K.δ A.obj ▷ M.μ A.obj ▷ A.act =
      K.δ A.obj ▷ M.T.map A.act ▷ A.act ≫ M.η (M.T.obj A.obj) ◁ A.assocIso.inv := by
    kernel_exact whisker_exchange (K.δ A.obj) A.assocIso.inv
  have hδ : K.δ A.obj ▷ M.μ A.obj ▷ A.act = 𝟙 _ := by
    kernel_exact congrArg (· ▷ A.act) (K.δ_whiskerRight_μ A.obj)
  kernel_exact ((congrArg (K.δ A.obj ▷ M.T.map A.act ▷ A.act ≫ ·)
    A.whiskerLeft_unitIso_hom).trans ex.symm).trans
      ((congrArg (M.T.map (M.η A.obj) ◁ A.assocIso.inv ≫ ·) hδ).trans
        ((Category.comp_id _).trans A.map₂_unitIso_hom_whiskerRight.symm))

/-- The triangle law of `a ⊣ η_x` involving `a`. -/
theorem adjUnitOf_left_triangle :
    K.adjUnitOf A.unitIso ▷ A.act ≫ A.act ◁ A.unitIso.hom = 𝟙 A.act := by
  have h₁ := congrArg (M.T.map₂ A.unitIso.inv ▷ A.act ≫ ·)
    (A.δ_whiskerRight_comp_whiskerLeft_unitIso_hom K)
  have h₂ : M.T.map₂ A.unitIso.inv ▷ A.act ≫ M.T.map₂ A.unitIso.hom ▷ A.act = 𝟙 _ := by
    kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ A.act) A.unitIso.inv_hom_id
  kernel_exact h₁.trans h₂

/-- **The action of a pseudo-algebra of a lax idempotent 2-monad is left adjoint to the unit**,
with counit the unit 2-cell `ζ`. -/
def toPseudoReflection : M.PseudoReflection A.obj where
  act := A.act
  adj :=
    { unit := K.adjUnitOf A.unitIso
      counit := A.unitIso.hom
      left_triangle := by kernel_exact A.adjUnitOf_left_triangle K
      right_triangle := by kernel_exact K.adjUnitOf_right_triangle A.unitIso }
  counitIso := A.unitIso
  counit_eq := rfl

end PseudoAlg

namespace PseudoReflection

variable (K : M.LaxIdempotent) {x : C} (R : M.PseudoReflection x)

/-- The unit of the adjunction is `adjUnitOf ζ`: both satisfy the triangle law involving `η_x`,
and a 2-cell into `a ≫ η_x` is determined by its whiskering with `η_x`. -/
theorem unit_eq : R.adj.unit = K.adjUnitOf R.counitIso := by
  refine Adjunction.hom_ext_to R.adj ((Iso.comp_hom_eq_id
    (whiskerRightIso R.counitIso (M.η x))).1 ?_ |>.trans (K.η_whiskerLeft_adjUnitOf _).symm)
  have h := R.adj.right_triangle
  rw [R.counit_eq] at h
  kernel_exact h

theorem left_triangle : K.adjUnitOf R.counitIso ▷ R.act ≫ R.act ◁ R.counitIso.hom = 𝟙 R.act := by
  have h := R.adj.left_triangle
  rw [R.counit_eq, R.unit_eq K] at h
  kernel_exact h

theorem adjUnitOf_whiskerRight : K.adjUnitOf R.counitIso ▷ R.act = R.act ◁ R.counitIso.inv :=
  (Iso.comp_hom_eq_id (whiskerLeftIso R.act R.counitIso)).1 (R.left_triangle K)

/-- `δ_x ▷ T a ▷ a ≫ a ◁ ζ = T ζ ▷ a`, by the triangle law involving `a`. -/
theorem δ_whiskerRight_comp_whiskerLeft_counitIso_hom :
    K.δ x ▷ M.T.map R.act ▷ R.act ≫ R.act ◁ R.counitIso.hom =
      M.T.map₂ R.counitIso.hom ▷ R.act := by
  have e : M.T.map₂ R.counitIso.hom ▷ R.act ≫ M.T.map₂ R.counitIso.inv ▷ R.act = 𝟙 _ := by
    kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ R.act) R.counitIso.hom_inv_id
  kernel_exact ((Category.id_comp _).symm.trans (congrArg (· ≫ K.δ x ▷ M.T.map R.act ▷ R.act ≫
    R.act ◁ R.counitIso.hom) e.symm)).trans
      ((congrArg (M.T.map₂ R.counitIso.hom ▷ R.act ≫ ·) (R.left_triangle K)).trans
        (Category.comp_id _))

theorem mapη_whiskerLeft_assocInvOf :
    M.T.map (M.η x) ◁ K.assocInvOf R.counitIso = M.T.map₂ R.counitIso.hom ▷ R.act :=
  (K.mapη_whiskerLeft_assocInvOf R.counitIso).trans
    (R.δ_whiskerRight_comp_whiskerLeft_counitIso_hom K)

/-- The associativity 2-cell, as an isomorphism. -/
def assocIso : M.μ x ≫ R.act ≅ M.T.map R.act ≫ R.act where
  hom := K.assocHomOf R.counitIso
  inv := K.assocInvOf R.counitIso
  hom_inv_id := by
    refine K.hom_ext_μ ?_
    have h : M.T.map₂ R.counitIso.inv ▷ R.act ≫ M.T.map₂ R.counitIso.hom ▷ R.act = 𝟙 _ := by
      kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ R.act) R.counitIso.inv_hom_id
    kernel_exact (congrArg₂ (· ≫ ·) (K.mapη_whiskerLeft_assocHomOf R.counitIso)
      (R.mapη_whiskerLeft_assocInvOf K)).trans h
  inv_hom_id := by
    refine Adjunction.hom_ext_to (M.T.mapAdjunction R.adj) ?_
    have h : M.T.map₂ R.counitIso.hom ▷ R.act ≫ M.T.map₂ R.counitIso.inv ▷ R.act = 𝟙 _ := by
      kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ R.act) R.counitIso.hom_inv_id
    kernel_exact (congrArg₂ (· ≫ ·) (R.mapη_whiskerLeft_assocInvOf K)
      (K.mapη_whiskerLeft_assocHomOf R.counitIso)).trans h

/-- **A left adjoint of the unit of a lax idempotent 2-monad with invertible counit is a
pseudo-algebra**, with unit 2-cell the counit. -/
def toPseudoAlg : M.PseudoAlg where
  obj := x
  act := R.act
  unitIso := R.counitIso
  assocIso := R.assocIso K
  unit_left := by
    kernel_exact (congrArg (· ≫ R.act ◁ R.counitIso.hom)
      (K.η_whiskerLeft_assocHomOf R.counitIso)).trans (R.left_triangle K)
  unit_right := by
    have h : M.T.map₂ R.counitIso.inv ▷ R.act ≫ M.T.map₂ R.counitIso.hom ▷ R.act = 𝟙 _ := by
      kernel_exact congrArg (fun θ => M.T.map₂ θ ▷ R.act) R.counitIso.inv_hom_id
    kernel_exact (congrArg (· ≫ M.T.map₂ R.counitIso.hom ▷ R.act)
      (K.mapη_whiskerLeft_assocHomOf R.counitIso)).trans h
  assoc := by
    refine K.hom_ext_μ (x := M.T.obj x) (g := M.μ x ≫ R.act) ?_
    have l : M.T.map (M.η (M.T.obj x)) ◁ M.T.map (M.T.map R.act) ◁ K.assocHomOf R.counitIso =
        M.T.map R.act ◁ M.T.map₂ R.counitIso.inv ▷ R.act :=
      (eq_of_heq (whiskerLeft_congr (M.toPreTwoMonad.map_η_naturality R.act) _)).trans
        (congrArg (M.T.map R.act ◁ ·) (K.mapη_whiskerLeft_assocHomOf R.counitIso))
    have r : M.T.map₂ (M.η (M.T.obj x) ◁ K.assocHomOf R.counitIso) ▷ R.act =
        M.T.map₂ (R.act ◁ R.counitIso.inv) ▷ R.act :=
      (congrArg (fun θ => M.T.map₂ θ ▷ R.act) (K.η_whiskerLeft_assocHomOf R.counitIso)).trans
        (congrArg (fun θ => M.T.map₂ θ ▷ R.act) (R.adjUnitOf_whiskerRight K))
    kernel_exact (congrArg (K.assocHomOf R.counitIso ≫ ·) l).trans
      (congrArg (K.assocHomOf R.counitIso ≫ ·) r).symm

end PseudoReflection

/-- **The pseudo-algebras of a lax idempotent 2-monad are the left adjoints of the units with
invertible counit.** -/
def LaxIdempotent.pseudoAlgEquiv (K : M.LaxIdempotent) :
    M.PseudoAlg ≃ Σ x : C, M.PseudoReflection x where
  toFun A := ⟨A.obj, A.toPseudoReflection K⟩
  invFun R := R.2.toPseudoAlg K
  left_inv A := by
    obtain ⟨x, a, ζ, α, h₁, h₂, h₃⟩ := A
    dsimp only [PseudoAlg.toPseudoReflection, PseudoReflection.toPseudoAlg]
    congr 1
    exact Iso.ext (PseudoAlg.assocIso_hom_eq K ⟨x, a, ζ, α, h₁, h₂, h₃⟩).symm
  right_inv := by
    rintro ⟨x, a, adj, ζ, hε⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    dsimp only [PseudoAlg.toPseudoReflection, PseudoReflection.toPseudoAlg]
    congr 1
    exact Bicategory.Adjunction.ext (PseudoReflection.unit_eq K ⟨a, adj, ζ, hε⟩).symm hε.symm

/-! ## Normal pseudo-algebras are left adjoint left inverses of units -/

/-- A left adjoint left inverse (LALI) of the unit: a retraction `a` of `η_x` that is left adjoint
to `η_x` with identity counit. -/
structure Reflection (x : C) where
  /-- The retraction `a`. -/
  toRetraction : M.Retraction x
  /-- The adjunction `a ⊣ η_x`. -/
  adj : toRetraction.act ⊣ M.η x
  counit_eq : adj.counit = 𝟙 _

/-- A LALI of the unit is a left adjoint with invertible counit. -/
def Reflection.toPseudoReflection {x : C} (R : M.Reflection x) : M.PseudoReflection x where
  act := R.toRetraction.act
  adj := R.adj
  counitIso := Iso.refl (𝟙 x)
  counit_eq := R.counit_eq

/-- **The action of a normal pseudo-algebra of a lax idempotent 2-monad is a LALI of the
unit.** -/
def NormalPseudoAlg.toReflection (K : M.LaxIdempotent) (A : M.NormalPseudoAlg) :
    M.Reflection A.obj where
  toRetraction := A.toRetraction
  adj := (A.toPseudoAlg.toPseudoReflection K).adj
  counit_eq := rfl

/-- **A LALI of the unit of a lax idempotent 2-monad is a normal pseudo-algebra.** -/
def Reflection.toNormalPseudoAlg (K : M.LaxIdempotent) {x : C} (R : M.Reflection x) :
    M.NormalPseudoAlg where
  obj := x
  toRetraction := R.toRetraction
  assocIso := (R.toPseudoReflection.toPseudoAlg K).assocIso
  unit_left := by
    kernel_exact (Category.comp_id _).symm.trans (R.toPseudoReflection.toPseudoAlg K).unit_left
  unit_right := by
    kernel_exact (Category.comp_id _).symm.trans (R.toPseudoReflection.toPseudoAlg K).unit_right
  assoc := (R.toPseudoReflection.toPseudoAlg K).assoc

/-- **The normal pseudo-algebras of a lax idempotent 2-monad are the left adjoint left inverses
of the units.** -/
def LaxIdempotent.normalPseudoAlgEquiv (K : M.LaxIdempotent) :
    M.NormalPseudoAlg ≃ Σ x : C, M.Reflection x where
  toFun A := ⟨A.obj, A.toReflection K⟩
  invFun R := R.2.toNormalPseudoAlg K
  left_inv A := by
    obtain ⟨x, r, α, h₁, h₂, h₃⟩ := A
    dsimp only [NormalPseudoAlg.toReflection, Reflection.toNormalPseudoAlg,
      PseudoAlg.toPseudoReflection, PseudoReflection.toPseudoAlg, Reflection.toPseudoReflection,
      NormalPseudoAlg.toPseudoAlg]
    congr 1
    exact Iso.ext (PseudoAlg.assocIso_hom_eq K (NormalPseudoAlg.toPseudoAlg
      ⟨x, r, α, h₁, h₂, h₃⟩)).symm
  right_inv := by
    rintro ⟨x, r, adj, hε⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    dsimp only [NormalPseudoAlg.toReflection, Reflection.toNormalPseudoAlg,
      PseudoAlg.toPseudoReflection, PseudoReflection.toPseudoAlg, Reflection.toPseudoReflection,
      NormalPseudoAlg.toPseudoAlg]
    congr 1
    exact Bicategory.Adjunction.ext
      (PseudoReflection.unit_eq K (Reflection.toPseudoReflection ⟨r, adj, hε⟩)).symm hε.symm

/-! ## Strict algebras are split left adjoint left inverses of units -/

namespace Retraction

variable {x : C} (r : M.Retraction x) (K : M.LaxIdempotent)

/-- The unit `δ x ▷ T a : 𝟙 ⟶ a ≫ η_x` of the adjunction `a ⊣ η_x`. -/
def adjUnit : 𝟙 (M.T.obj x) ⟶ r.act ≫ M.η x :=
  K.δ x ▷ M.T.map r.act

/-- The triangle law involving `η_x`, which holds for every retraction. -/
theorem η_whiskerLeft_adjUnit : M.η x ◁ r.adjUnit K = 𝟙 (M.η x) := by
  kernel_exact congrArg (· ▷ M.T.map r.act) (K.η_whiskerLeft_δ x)

/-- The triangle law involving `a`, which holds when `a` is split: `T a ≫ a = μ_x ≫ a`, and
`δ x ▷ μ_x` is the identity. -/
theorem adjUnit_whiskerRight (h : r.IsSplit) :
    K.δ x ▷ (M.T.map r.act ≫ r.act) = 𝟙 r.act := by
  have h' : K.δ x ▷ (M.μ x ≫ r.act) = 𝟙 r.act := by
    kernel_exact congrArg (· ▷ r.act) (K.δ_whiskerRight_μ x)
  exact eq_of_heq ((whiskerRight_congr (K.δ x) h.symm).trans (heq_of_eq h'))

theorem left_triangle (h : r.IsSplit) :
    leftZigzag (r.adjUnit K) (𝟙 (M.η x ≫ r.act)) = (λ_ r.act).hom ≫ (ρ_ r.act).inv := by
  kernel_exact r.adjUnit_whiskerRight K h

theorem right_triangle :
    rightZigzag (r.adjUnit K) (𝟙 (M.η x ≫ r.act)) = (ρ_ (M.η x)).hom ≫ (λ_ (M.η x)).inv := by
  kernel_exact r.η_whiskerLeft_adjUnit K

/-- For a lax idempotent 2-monad, a split retraction `a` of `η_x` is left adjoint to `η_x`, with
identity counit. -/
def adjunction (h : r.IsSplit) : r.act ⊣ M.η x where
  unit := r.adjUnit K
  counit := 𝟙 _
  left_triangle := r.left_triangle K h
  right_triangle := r.right_triangle K

end Retraction

variable (M) in
/-- A split LALI of the unit: a LALI `a` of `η_x` that is split, `μ_x ≫ a = T a ≫ a`. -/
structure SplitReflection (x : C) extends M.Reflection x where
  isSplit : toRetraction.IsSplit

namespace Alg

variable (A : M.Alg)

/-- The action of an algebra, as a retraction of the unit. -/
def toRetraction : M.Retraction A.obj :=
  ⟨A.act, A.unit⟩

theorem toRetraction_isSplit : A.toRetraction.IsSplit :=
  A.assoc

/-- **The action of an algebra of a lax idempotent 2-monad is left adjoint to the unit**, with
identity counit. -/
def adjunction (K : M.LaxIdempotent) : A.act ⊣ M.η A.obj :=
  A.toRetraction.adjunction K A.assoc

end Alg

/-- **The algebras of a lax idempotent 2-monad are the split LALIs**: an algebra structure on `x`
is the same as a split retraction of `η_x` left adjoint to `η_x` with identity counit. -/
def LaxIdempotent.algEquiv (K : M.LaxIdempotent) : M.Alg ≃ Σ x : C, M.SplitReflection x where
  toFun A := ⟨A.obj, ⟨A.toRetraction, A.adjunction K, rfl⟩, A.assoc⟩
  invFun s := ⟨s.1, s.2.toRetraction.act, s.2.toRetraction.unit, s.2.isSplit⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, ⟨r, adj, hε⟩, h⟩
    change r.IsSplit at h
    obtain rfl : adj = r.adjunction K h :=
      Bicategory.Adjunction.ext (Adjunction.unit_eq_of_counit_eq adj (r.adjunction K h) hε) hε
    rfl

end TwoMonad

end CategoryTheory.TwoCategory
