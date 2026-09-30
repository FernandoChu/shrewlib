import Nfib.Displayed.Basic
import Nfib.Displayed.Cartesian
import Mathlib.CategoryTheory.EqToHom

/-!
# Split opfibrations and fibrations

A `SplitOpfib` structure on a displayed category `D` is a strictly functorial cloven opfibration:
a chosen pushforward `transp f x` for every base morphism `f` and object `x`, a chosen opcartesian
lift `olift f x`, and the splitting axioms `transp_id`/`olift_id`/`transp_comp`/`olift_comp`.
`SplitFib` is the exact dual (chosen cartesian lifts).

The splitting axioms are stated as equalities. `olift_id` and `olift_comp` compare morphisms whose
*codomains* differ (`transp (𝟙 a) x` versus `x`, and `transp (f ≫ g) x` versus
`transp g (transp f x)`); that is an object-level discrepancy, which `castHom` — a transport along
base morphisms — cannot express, so it is absorbed by the fiber `eqToHom` of `transp_id` /
`transp_comp` instead. `HEq` restatements are available as `olift_id_heq` and `olift_comp_heq`.

From a `SplitOpfib` we derive:

* `factor` — the vertical factorization of an arbitrary displayed morphism through the chosen lift,
  with its universal-property lemmas;
* `homEquiv` — the hom-set bijection `D.Hom f x y ≃ (transp f x ⟶ y)`;
* `transpMap`/`transpFunctor` — the fiber transport functor `D.Fiber a ⥤ D.Fiber a'`;
* `totalOlift` — the chosen opcartesian morphisms of the total category.

This is part of milestone **M2** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂

namespace Nfib

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

/-- A split opfibration structure on a displayed category: strictly functorial chosen opcartesian
lifts. -/
class SplitOpfib (D : Displayed A) where
  /-- The chosen pushforward of `x` along `f`, as an object of the fiber over `a'`. -/
  transp : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Fiber a'
  /-- The chosen opcartesian lift of `f` at `x`. -/
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → (x ⟶[f] (transp f x))
  /-- The chosen lifts are opcartesian. -/
  olift_opcartesian : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)
  /-- Pushforward along the identity is the identity. -/
  transp_id : ∀ {a : A} (x : D.Ob a), transp (𝟙 a) x = x
  /-- The lift of the identity is the displayed identity, after transporting its codomain along
  `transp_id`. -/
  olift_id : ∀ {a : A} (x : D.Ob a), D.castOb (olift (𝟙 a) x) rfl (transp_id x) = D.id x
  /-- Pushforward is functorial in the base morphism. -/
  transp_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    transp (f ≫ g) x = transp g (transp f x)
  /-- The lift of a composite is the composite of lifts, after transporting the codomain along
  `transp_comp`. -/
  olift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    D.castOb (olift (f ≫ g) x) rfl (transp_comp f g x)
      = olift f x ≫ᵈ olift g (transp f x)

/-- A split fibration structure on a displayed category: strictly functorial chosen cartesian
lifts. The exact dual of `SplitOpfib`; used for documentation and the duality. -/
class SplitFib (D : Displayed A) where
  /-- The chosen pullback of `y` along `f`, as an object of the fiber over `a`. -/
  pull : {a a' : A} → (f : a ⟶ a') → D.Ob a' → D.Fiber a
  /-- The chosen cartesian lift of `f` at `y`. -/
  clift : {a a' : A} → (f : a ⟶ a') → (y : D.Ob a') → ((pull f y) ⟶[f] y)
  /-- The chosen lifts are cartesian. -/
  clift_cartesian : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (clift f y)
  /-- Pullback along the identity is the identity. -/
  pull_id : ∀ {a : A} (y : D.Ob a), pull (𝟙 a) y = y
  /-- The lift of the identity is the displayed identity, after transporting its domain along
  `pull_id`. -/
  clift_id : ∀ {a : A} (y : D.Ob a), D.castOb (clift (𝟙 a) y) (pull_id y) rfl = D.id y
  /-- Pullback is functorial in the base morphism. -/
  pull_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    pull (f ≫ g) y = pull f (pull g y)
  /-- The lift of a composite is the composite of lifts, after transporting the domain along
  `pull_comp`. -/
  clift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    D.castOb (clift (f ≫ g) y) (pull_comp f g y) rfl
      = clift f (pull g y) ≫ᵈ clift g y

section

variable (D : Displayed A) [SplitOpfib D]

/-- The chosen pushforward of `x` along `f`, viewed as an object of the fiber over `a'`. -/
def transp {a a' : A} (f : a ⟶ a') (x : D.Ob a) : D.Fiber a' := SplitOpfib.transp f x

/-- The chosen opcartesian lift of `f` at `x`. -/
def olift {a a' : A} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] (D.transp f x) := SplitOpfib.olift f x

theorem olift_opcartesian {a a' : A} (f : a ⟶ a') (x : D.Ob a) :
    IsOpcartesian (D.olift f x) := SplitOpfib.olift_opcartesian f x

@[simp]
theorem transp_id {a : A} (x : D.Ob a) : D.transp (𝟙 a) x = x := SplitOpfib.transp_id x

@[simp]
theorem olift_id {a : A} (x : D.Ob a) :
    D.castOb (D.olift (𝟙 a) x) rfl (D.transp_id x) = D.id x := SplitOpfib.olift_id x

/-- `olift_id` read in the fiber over `a`, where the codomain correction becomes an `eqToHom`. -/
theorem olift_id_eqToHom {a : A} (x : D.Ob a) :
    D.olift (𝟙 a) x = eqToHom (D.transp_id x).symm :=
  eq_of_heq <| ((D.castOb_heq _ rfl (D.transp_id x)).symm.trans
    (heq_of_eq (D.olift_id x))).trans
      (eqToHom_heq_id_dom (C := D.Fiber a) x _ (D.transp_id x).symm).symm

theorem transp_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.transp (f ≫ g) x = D.transp g (D.transp f x) := SplitOpfib.transp_comp f g x

@[simp]
theorem olift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.castOb (D.olift (f ≫ g) x) rfl (D.transp_comp f g x)
      = D.olift f x ≫ᵈ D.olift g (D.transp f x) := SplitOpfib.olift_comp f g x

/-- `HEq` form of `olift_id`: the two sides lie over the same base morphism but have different
codomains, so this is the object-level heterogeneity that `castHom` cannot express. -/
theorem olift_id_heq {a : A} (x : D.Ob a) : D.olift (𝟙 a) x ≍ D.id x :=
  (D.castOb_heq _ rfl (D.transp_id x)).symm.trans (heq_of_eq (D.olift_id x))

/-- `HEq` form of `olift_comp`, with the codomain correction absorbed. -/
theorem olift_comp_heq {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.olift (f ≫ g) x ≍ D.olift f x ≫ᵈ D.olift g (D.transp f x) :=
  (D.castOb_heq _ rfl (D.transp_comp f g x)).symm.trans (heq_of_eq (D.olift_comp f g x))

end

section Factor

variable (D : Displayed A) [SplitOpfib D] {a a' : A}

/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift `olift f x` by a
vertical morphism `transp f x ⟶ y`. -/
noncomputable def factor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    (D.transp f x) ⟶[𝟙 a'] y :=
  IsOpcartesian.desc (D.olift_opcartesian f x) (𝟙 a') (D.castHom φ (Category.comp_id f).symm)

@[simp]
theorem olift_factor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.olift f x ≫ᵈ D.factor φ = D.castHom φ (Category.comp_id f).symm :=
  IsOpcartesian.desc_fac (D.olift_opcartesian f x) (𝟙 a') _

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with `factor φ`. -/
theorem factor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : (D.transp f x) ⟶[𝟙 a'] y)
    (h : D.olift f x ≫ᵈ β = D.castHom φ (Category.comp_id f).symm) : β = D.factor φ :=
  IsOpcartesian.desc_uniq (D.olift_opcartesian f x) β h

@[simp]
theorem factor_olift {f : a ⟶ a'} (x : D.Ob a) :
    D.factor (D.olift f x) = 𝟙 (D.transp f x) :=
  (D.factor_uniq (D.olift f x) (𝟙 (D.transp f x)) (D.comp_id' (D.olift f x))).symm

/-- The hom-set bijection defining an opfibration: `D.Hom f x y ≃ (transp f x ⟶ y)`. -/
noncomputable def homEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.transp f x) ⟶[𝟙 a'] y) where
  toFun φ := D.factor φ
  invFun β := D.castHom (D.olift f x ≫ᵈ β) (Category.comp_id f)
  left_inv φ := by simp
  right_inv β := (D.factor_uniq _ β (by simp)).symm

end Factor

section TranspMap

variable (D : Displayed A) [SplitOpfib D] {a a' : A}

/-- Transport of a vertical morphism along `f`. -/
noncomputable def transpMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.transp f x ⟶ D.transp f y :=
  D.factor (D.castHom (β ≫ᵈ D.olift f y) (Category.id_comp f))

/-- The defining equation of `transpMap`, as an `Eq` modulo a cast. -/
@[simp]
theorem olift_transpMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.olift f x ≫ᵈ D.transpMap f β = D.castHom (β ≫ᵈ D.olift f y) := by
  have h : D.transpMap f β = D.factor (D.castHom (β ≫ᵈ D.olift f y) (Category.id_comp f)) := rfl
  rw [h, olift_factor, DisplayedStruct.castHom_castHom]

/-- The defining equation of `transpMap`, as a `HEq` (cast-free). -/
theorem olift_transpMap_heq (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.olift f x ≫ᵈ D.transpMap f β ≍ β ≫ᵈ D.olift f y := by
  rw [olift_transpMap]; exact D.castHom_heq _ _

/-- `transpMap f` preserves identities (functor identity law). -/
theorem transpMap_id_vert (f : a ⟶ a') (x : D.Fiber a) :
    D.transpMap f (𝟙 x) = 𝟙 (D.transp f x) := by
  refine IsOpcartesian.hom_ext (D.olift_opcartesian f x) ?_
  simp [Fiber.id_def]

/-- `transpMap f` preserves composition (functor composition law). -/
theorem transpMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.transpMap f (β ≫ γ) = D.transpMap f β ≫ D.transpMap f γ := by
  refine IsOpcartesian.hom_ext (D.olift_opcartesian f x) (eq_of_heq ?_)
  have hmix : (𝟙 a ≫ f) = (f ≫ 𝟙 a') := by simp
  refine (D.olift_transpMap_heq f (β ≫ γ)).trans ?_
  refine (D.heq_comp (Category.comp_id (𝟙 a)).symm rfl rfl rfl rfl
    (D.castHom_heq _ _) HEq.rfl).trans ?_
  refine (D.assoc_heq β γ (D.olift f z)).trans ?_
  refine (D.heq_comp rfl hmix rfl rfl rfl HEq.rfl (D.olift_transpMap_heq f γ).symm).trans ?_
  refine (D.assoc_heq β (D.olift f y) (D.transpMap f γ)).symm.trans ?_
  refine (D.heq_comp hmix rfl rfl rfl rfl (D.olift_transpMap_heq f β).symm HEq.rfl).trans ?_
  refine (D.assoc_heq (D.olift f x) (D.transpMap f β) (D.transpMap f γ)).trans ?_
  exact D.heq_comp rfl (Category.comp_id (𝟙 a')) rfl rfl rfl HEq.rfl (D.castHom_heq _ _).symm

/-- Transport along the identity is the identity, up to the object equality `transp_id`. -/
theorem transpMap_id (a : A) {x y : D.Fiber a} (β : x ⟶ y) :
    D.transpMap (𝟙 a) β
      = eqToHom (D.transp_id x) ≫ β ≫ eqToHom (D.transp_id y).symm := by
  have hW : (eqToHom (D.transp_id x) ≫ β ≫ eqToHom (D.transp_id y).symm) ≍ β :=
    (conj_eqToHom_iff_heq _ _ (D.transp_id x) (D.transp_id y)).mp rfl
  refine IsOpcartesian.hom_ext (D.olift_opcartesian (𝟙 a) x) (eq_of_heq ?_)
  refine (D.olift_transpMap_heq (𝟙 a) β).trans ?_
  refine (D.heq_comp rfl rfl rfl rfl (D.transp_id y) HEq.rfl (D.olift_id_heq y)).trans ?_
  refine (D.comp_id_heq β).trans ?_
  refine (D.id_comp_heq β).symm.trans ?_
  exact (D.heq_comp rfl rfl rfl (D.transp_id x) (D.transp_id y) (D.olift_id_heq x) hW).symm

/-- Transport along a composite is the composite of transports, up to `transp_comp`. -/
theorem transpMap_comp (f : a ⟶ a') (g : a' ⟶ a'') {x y : D.Fiber a} (β : x ⟶ y) :
    D.transpMap (f ≫ g) β
      = eqToHom (D.transp_comp f g x) ≫ D.transpMap g (D.transpMap f β)
          ≫ eqToHom (D.transp_comp f g y).symm := by
  have hbg : (g ≫ 𝟙 a'') = (𝟙 a' ≫ g) := by simp
  have hbf : (f ≫ 𝟙 a') = (𝟙 a ≫ f) := by simp
  set Q := D.transpMap g (D.transpMap f β) with hQ
  have hW : (eqToHom (D.transp_comp f g x) ≫ Q ≫ eqToHom (D.transp_comp f g y).symm) ≍ Q :=
    (conj_eqToHom_iff_heq _ _ (D.transp_comp f g x) (D.transp_comp f g y)).mp rfl
  -- the common target of both post-`olift` composites
  have chain : (D.olift f x ≫ᵈ D.olift g (D.transp f x)) ≫ᵈ Q ≍ β ≫ᵈ D.olift (f ≫ g) y := by
    refine (D.assoc_heq (D.olift f x) (D.olift g (D.transp f x)) Q).trans ?_
    refine (D.heq_comp rfl hbg rfl rfl rfl HEq.rfl
      (D.olift_transpMap_heq g (D.transpMap f β))).trans ?_
    refine (D.assoc_heq (D.olift f x) (D.transpMap f β) (D.olift g (D.transp f y))).symm.trans ?_
    refine (D.heq_comp hbf rfl rfl rfl rfl (D.olift_transpMap_heq f β) HEq.rfl).trans ?_
    refine (D.assoc_heq β (D.olift f y) (D.olift g (D.transp f y))).trans ?_
    exact D.heq_comp rfl rfl rfl rfl (D.transp_comp f g y).symm HEq.rfl
      (D.olift_comp_heq f g y).symm
  refine IsOpcartesian.hom_ext (D.olift_opcartesian (f ≫ g) x) (eq_of_heq ?_)
  refine (D.olift_transpMap_heq (f ≫ g) β).trans ?_
  refine HEq.symm ?_
  refine (D.heq_comp rfl rfl rfl (D.transp_comp f g x) (D.transp_comp f g y)
    (D.olift_comp_heq f g x) hW).trans chain

/-- The fiber transport functor `D.Fiber a ⥤ D.Fiber a'`. -/
noncomputable def transpFunctor (f : a ⟶ a') : D.Fiber a ⥤ D.Fiber a' where
  obj x := D.transp f x
  map β := D.transpMap f β
  map_id x := D.transpMap_id_vert f x
  map_comp β γ := D.transpMap_comp_vert f β γ

@[simp] theorem transpFunctor_obj (f : a ⟶ a') (x : D.Fiber a) :
    (D.transpFunctor f).obj x = D.transp f x := rfl

@[simp] theorem transpFunctor_map (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    (D.transpFunctor f).map β = D.transpMap f β := rfl

/-- Transport of an `eqToHom` is an `eqToHom`. -/
@[simp]
theorem transpMap_eqToHom (f : a ⟶ a') {x y : D.Fiber a} (h : x = y) :
    D.transpMap f (eqToHom h) = eqToHom (by rw [h]) := by
  subst h; exact D.transpMap_id_vert f x

end TranspMap

section TotalOlift

variable (D : Displayed A) [SplitOpfib D] {a a' : A}

/-- The chosen opcartesian morphisms of the total category. -/
def totalOlift (f : a ⟶ a') (x : D.Ob a) : D.tot x ⟶ D.tot (D.transp f x) :=
  ⟨f, D.olift f x⟩

@[simp] theorem totalOlift_base (f : a ⟶ a') (x : D.Ob a) : (D.totalOlift f x).base = f := rfl

@[simp] theorem totalOlift_fiber (f : a ⟶ a') (x : D.Ob a) :
    (D.totalOlift f x).fiber = D.olift f x := rfl

@[simp] theorem π_map_totalOlift (f : a ⟶ a') (x : D.Ob a) :
    (D.π).map (D.totalOlift f x) = f := rfl

/-- Every morphism of the total category factors as the chosen lift followed by a vertical
morphism. -/
@[reassoc]
theorem factorTotal {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.totalMk f φ = D.totalOlift f x ≫ D.totalVert (D.factor φ) :=
  Total.hom_ext D (by simp [totalOlift]) (by
    change φ ≍ D.olift f x ≫ᵈ D.factor φ
    rw [olift_factor]
    exact (D.castHom_heq φ _).symm)

/-- Uniqueness of the vertical factorization, phrased in the total category. -/
theorem factor_eq_of_totalEq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : (D.transp f x) ⟶[𝟙 a'] y)
    (h : D.totalOlift f x ≫ D.totalVert β = D.totalMk f φ) : β = D.factor φ :=
  D.factor_uniq φ β (eq_of_heq ((heq_of_totalHom_eq D h).trans (D.castHom_heq φ _).symm))

/-- The chosen lift of an identity is the identity of the total category, up to the vertical
`eqToHom` supplied by `transp_id`. -/
@[reassoc]
theorem totalOlift_id (x : D.Ob a) :
    D.totalOlift (𝟙 a) x ≫ D.totalVert (eqToHom (D.transp_id x)) = 𝟙 (D.tot x) :=
  Total.hom_ext D (by simp [totalOlift]) (by
    change D.olift (𝟙 a) x ≫ᵈ eqToHom (D.transp_id x) ≍ D.id x
    exact (D.heq_comp rfl rfl rfl (D.transp_id x) rfl (D.olift_id_heq x)
      (eqToHom_heq_id_cod _ _ (D.transp_id x))).trans (D.comp_id_heq _))

/-- Splitness in the total category: the chosen lift of a composite is the composite of the chosen
lifts, up to the vertical `eqToHom` supplied by `transp_comp`. -/
@[reassoc]
theorem totalOlift_comp {a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.totalOlift (f ≫ g) x ≫ D.totalVert (eqToHom (D.transp_comp f g x))
      = D.totalOlift f x ≫ D.totalOlift g (D.transp f x) :=
  Total.hom_ext D (by simp [totalOlift]) (by
    change D.olift (f ≫ g) x ≫ᵈ eqToHom (D.transp_comp f g x)
        ≍ D.olift f x ≫ᵈ D.olift g (D.transp f x)
    exact (D.heq_comp rfl rfl rfl (D.transp_comp f g x) rfl (D.olift_comp_heq f g x)
      (eqToHom_heq_id_cod _ _ (D.transp_comp f g x))).trans (D.comp_id_heq _))

/-- Interchange in the total category: a vertical morphism followed by a chosen lift equals the
chosen lift followed by the transported vertical morphism. -/
@[reassoc]
theorem totalVert_comp_totalOlift {a'' : A} (g : a' ⟶ a'') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.totalVert β ≫ D.totalOlift g y = D.totalOlift g x ≫ D.totalVert (D.transpMap g β) :=
  Total.hom_ext D (by simp [totalOlift]) (by
    change β ≫ᵈ D.olift g y ≍ D.olift g x ≫ᵈ D.transpMap g β
    exact (D.olift_transpMap_heq g β).symm)

/-- Factorization of a *vertical* morphism: `factor` merely absorbs the object equality
`transp_id`. -/
theorem factor_vert {b b' : D.Ob a} (β : b ⟶[𝟙 a] b') :
    D.factor β = eqToHom (D.transp_id b) ≫ β := by
  refine (D.factor_eq_of_totalEq β _ ?_).symm
  rw [D.totalVert_comp (eqToHom (D.transp_id b)) β, D.totalOlift_id_assoc]
  rfl

/-- Heterogeneous form of `factor_vert`: the factorization of a vertical morphism is the morphism
itself, modulo `transp_id`. -/
theorem factor_vert_heq {b b' : D.Ob a} (β : b ⟶[𝟙 a] b') : D.factor β ≍ β := by
  rw [D.factor_vert β]; exact eqToHom_comp_heq _ _

@[simp]
theorem factor_id (b : D.Ob a) : D.factor (D.id b) = eqToHom (D.transp_id b) := by
  rw [D.factor_vert (D.id b)]; exact Category.comp_id _

/-- `factor` of a composite: an equation in the fiber category over the final base object. -/
theorem factor_comp {a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.factor (φ ≫ᵈ ψ)
      = eqToHom (D.transp_comp f g x) ≫ D.transpMap g (D.factor φ) ≫ D.factor ψ := by
  refine (D.factor_eq_of_totalEq (φ ≫ᵈ ψ) _ ?_).symm
  rw [D.totalVert_comp, D.totalVert_comp, D.totalOlift_comp_assoc,
    ← D.totalVert_comp_totalOlift_assoc, ← D.factorTotal_assoc, ← D.factorTotal, totalMk_comp]

/-- Heterogeneous form of `factor_comp`. -/
theorem factor_comp_heq {a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.factor (φ ≫ᵈ ψ) ≍ (D.transpMap g (D.factor φ) ≫ D.factor ψ :
      D.transp g (D.transp f x) ⟶ z) := by
  rw [D.factor_comp φ ψ]; exact eqToHom_comp_heq _ _

end TotalOlift

end Displayed

end Nfib
