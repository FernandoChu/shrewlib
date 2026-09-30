import Nfib.Displayed.Double
import Nfib.Displayed.Sigma
import Nfib.Displayed.DualOp

/-!
# Dependent 2-sided split fibrations (`D2SFib`)

`D2SFib C` is a data-carrying class on a doubly displayed category `C : DoubleDisplayed B`
(with `B` a split opfibration over `A`). It packages, following Def. `def:d2sfib` of the paper
adapted to the displayed setting:

1. a *local split fibration*: chosen cartesian lifts `pull`/`pullLift` of the vertical morphisms of
   `B` (morphisms over `𝟙 a`), cartesian among morphisms of the same fiber;
2.–3. a *split opfibration over `A`*: chosen opcartesian lifts `push`/`pushLift`, typed over the
   chosen lifts `B.olift` of `B` (so the paper's axiom (3) is absorbed into the type of `pushLift`);
4. a strict *push/pull interchange* `push_pull`/`pushLift_pullLift`.

This is part of milestone **M5** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A]

section Bridges

variable {D : Displayed A} {a a' a'' : A}

/-- A `castOb` transporting only the codomain is postcomposition with the fiber `eqToHom`. -/
theorem castOb_rfl_eq_comp_eqToHom {f : a ⟶ a'} {x : D.Ob a} {y y' : D.Ob a'} (φ : x ⟶[f] y)
    (h : y = y') : D.castOb φ rfl h = D.castHom (φ ≫ᵈ eqToHom (C := D.Fiber a') h) := by
  cases h; simp [Displayed.Fiber.id_def]

variable [SplitOpfib D]

/-- `olift_id` in `eqToHom` form: the chosen lift over `𝟙 a`, corrected by the fiber `eqToHom` of
`transp_id`, is the displayed identity. -/
@[simp]
theorem olift_comp_eqToHom_id (x : D.Ob a) :
    D.castHom (D.olift (𝟙 a) x ≫ᵈ eqToHom (C := D.Fiber a) (D.transp_id x)) = D.id x := by
  rw [← castOb_rfl_eq_comp_eqToHom]; exact D.olift_id x

/-- `olift_comp` in `eqToHom` form. -/
@[simp]
theorem olift_comp_eqToHom_comp (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.castHom (D.olift (f ≫ g) x ≫ᵈ eqToHom (C := D.Fiber a'') (D.transp_comp f g x))
      = D.olift f x ≫ᵈ D.olift g (D.transp f x) := by
  rw [← castOb_rfl_eq_comp_eqToHom]; exact D.olift_comp f g x

end Bridges

/-- A dependent 2-sided split fibration structure on a doubly displayed category `C` over a split
opfibration `B`. -/
class D2SFib {B : Displayed A} [SplitOpfib B] (C : DoubleDisplayed B) where
  /-- Chosen cartesian pullback of a vertical morphism `β : b ⟶ b'`. -/
  pull : {a : A} → {b b' : B.Ob a} → (β : b ⟶[𝟙 a] b') → C.Ob b' → C.Ob b
  /-- Chosen cartesian lift over `β`. -/
  pullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    (pull β c) ⟶[[β]] c
  /-- The chosen pullback lifts are cartesian (among morphisms of the same fiber). -/
  pullLift_cartesian : ∀ {a : A} {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (χ : c₀ ⟶[[β₀ ≫ᵈ β]] c),
    ∃! ξ : c₀ ⟶[[β₀]] (pull β c), ξ ≫ᵈᵈ pullLift β c = χ
  /-- Pullback along the vertical identity is the identity. -/
  pull_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), pull (B.id b) c = c
  /-- The lift of the vertical identity is the identity, after correcting the domain by the
  `eqToHom` of `pull_id`. -/
  pullLift_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b),
    C.castHom (C.eqToHom (pull_id c).symm ≫ᵈᵈ pullLift (B.id b) c) = C.id c
  /-- Pullback is functorial in the vertical morphism. -/
  pull_comp : ∀ {a : A} {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'') (c : C.Ob b''),
    pull (β ≫ γ) c = pull β (pull γ c)
  /-- The lift of a composite is the composite of lifts, after correcting the domain by the
  `eqToHom` of `pull_comp` and the `B`-base by `Displayed.Fiber.comp_def`. -/
  pullLift_comp : ∀ {a : A} {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'') (c : C.Ob b''),
    C.castHom (C.eqToHom (pull_comp β γ c).symm ≫ᵈᵈ pullLift (β ≫ γ) c)
        rfl (by simp [Displayed.Fiber.comp_def])
      = pullLift β (pull γ c) ≫ᵈᵈ pullLift γ c
  /-- Chosen opcartesian pushforward along `α : a ⟶ a'`, over `B`'s pushforward `B.transp`. -/
  push : {a a' : A} → (α : a ⟶ a') → {b : B.Ob a} → C.Ob b → C.Ob (B.transp α b)
  /-- Chosen opcartesian lift over `B.olift α b`. -/
  pushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    c ⟶[[B.olift α b]] (push α c)
  /-- The chosen pushforward lifts are opcartesian over `B`. -/
  pushLift_opcartesian : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    DoubleDisplayed.IsOpcartesian (pushLift α c)
  /-- Pushforward along the identity is the identity, after transporting the `B`-object along
  `B.transp_id`. -/
  push_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), C.castObj (push (𝟙 a) c) (B.transp_id b) = c
  /-- The lift of the identity pushforward, with its codomain carried back over `b` by
  `eqToHomBase`, is the `eqToHom` of `push_id`. -/
  pushLift_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b),
    C.castHom (pushLift (𝟙 a) c ≫ᵈᵈ C.eqToHomBase (push (𝟙 a) c) (B.transp_id b))
        (Category.comp_id (𝟙 a)) (olift_comp_eqToHom_id b)
      = C.eqToHom (push_id c).symm
  /-- Pushforward is functorial, after transporting the `B`-object along `B.transp_comp`. -/
  push_comp : ∀ {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b),
    C.castObj (push (α ≫ α') c) (B.transp_comp α α' b) = push α' (push α c)
  /-- The lift of a composite pushforward is the composite of lifts, with the codomain carried
  back by `eqToHomBase` and then by the `eqToHom` of `push_comp`. -/
  pushLift_comp : ∀ {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b),
    C.castHom ((pushLift (α ≫ α') c
        ≫ᵈᵈ C.eqToHomBase (push (α ≫ α') c) (B.transp_comp α α' b))
        ≫ᵈᵈ C.eqToHom (push_comp α α' c))
      = pushLift α c ≫ᵈᵈ pushLift α' (push α c)
  /-- Strict push/pull interchange on objects. -/
  push_pull : ∀ {a a' : A} (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    push α (pull β c) = pull (B.transpMap α β) (push α c)
  /-- Strict push/pull interchange on lifts: the two ways around the pull/push square agree.
  The codomain discrepancy recorded by `push_pull` is absorbed by an `eqToHom` rather than by a
  `▸`, and the `B`-base discrepancy by a `castHom` (whose obligation is `B.olift_transpMap`). -/
  pushLift_pullLift : ∀ {a a' : A} (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    (c : C.Ob b'),
    C.castHom (pullLift β c ≫ᵈᵈ pushLift α c)
      = (pushLift α (pull β c) ≫ᵈᵈ C.eqToHom (push_pull α β c))
          ≫ᵈᵈ pullLift (B.transpMap α β) (push α c)

namespace D2SFib

open DoubleDisplayed

variable {B : Displayed A} [SplitOpfib B] {C : DoubleDisplayed B} [D2SFib C]

section HEqAxioms

/-- `HEq` form of `pullLift_id`. -/
theorem pullLift_id_heq {a : A} {b : B.Ob a} (c : C.Ob b) : pullLift (B.id b) c ≍ C.id c :=
  (C.eqToHom_comp_heq' _ _).symm.trans ((C.castHom_eq_iff_heq _ _).mp (D2SFib.pullLift_id c))

/-- `HEq` form of `pullLift_comp`. -/
theorem pullLift_comp_heq {a : A} {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'')
    (c : C.Ob b'') : pullLift (β ≫ γ) c ≍ pullLift β (pull γ c) ≫ᵈᵈ pullLift γ c :=
  (C.eqToHom_comp_heq' _ _).symm.trans
    ((C.castHom_eq_iff_heq _ _).mp (D2SFib.pullLift_comp β γ c))

/-- `HEq` form of `push_id`. -/
theorem push_id_heq {a : A} {b : B.Ob a} (c : C.Ob b) : push (𝟙 a) c ≍ c :=
  (C.castObj_eq_iff_heq _).mp (D2SFib.push_id c)

/-- `HEq` form of `push_comp`. -/
theorem push_comp_heq {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b) :
    push (α ≫ α') c ≍ push α' (push α c) :=
  (C.castObj_eq_iff_heq _).mp (D2SFib.push_comp α α' c)

/-- `HEq` form of `pushLift_id`. -/
theorem pushLift_id_heq {a : A} {b : B.Ob a} (c : C.Ob b) : pushLift (𝟙 a) c ≍ C.id c :=
  ((C.comp_eqToHomBase_heq _ _ _).symm.trans
    ((C.castHom_eq_iff_heq _ _).mp (D2SFib.pushLift_id c))).trans (C.eqToHom_heq_id _)

/-- `HEq` form of `pushLift_comp`. -/
theorem pushLift_comp_heq {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b) :
    pushLift (α ≫ α') c ≍ pushLift α c ≫ᵈᵈ pushLift α' (push α c) :=
  (((C.comp_eqToHomBase_heq _ _ _).symm.trans (C.comp_eqToHom_heq' _ _).symm)).trans
    ((C.castHom_eq_iff_heq _ _).mp (D2SFib.pushLift_comp α α' c))

end HEqAxioms

section PushMap

variable {a a' : A}

/-- The base equality witnessing `B.id b ≫ᵈ B.olift α b` and `B.olift α b ≫ᵈ B.id (transp α b)`
both reduce to `B.olift α b`. -/
private theorem push_base_heq (α : a ⟶ a') (b : B.Ob a) :
    B.id b ≫ᵈ B.olift α b ≍ B.olift α b ≫ᵈ B.id (B.transp α b) :=
  (B.id_comp_heq (B.olift α b)).trans (B.comp_id_heq (B.olift α b)).symm

/-- Functorial action of pushforward on vertical morphisms. -/
noncomputable def pushMap (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    (push α c) ⟶[[B.id (B.transp α b)]] (push α c') :=
  IsOpcartesian.desc (pushLift_opcartesian α c) (B.id (B.transp α b))
    (C.castHom (f ≫ᵈᵈ pushLift α c'))

/-- Descent characterization of `pushMap`. -/
theorem pushLift_pushMap (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    pushLift α c ≫ᵈᵈ pushMap α f
      = C.castHom (f ≫ᵈᵈ pushLift α c') :=
  IsOpcartesian.desc_fac (pushLift_opcartesian α c) (B.id (B.transp α b)) _

/-- `pushMap` preserves identities. -/
theorem pushMap_id (α : a ⟶ a') {b : B.Ob a} (c : C.Fiber b) :
    pushMap α (𝟙 c) = C.id (push α c) := by
  refine IsOpcartesian.hom_ext (pushLift_opcartesian α c) (eq_of_heq ?_)
  refine (heq_of_eq (pushLift_pushMap α (𝟙 c))).trans ?_
  refine (C.castHom_heq _ _ _).trans ?_
  refine (C.heq_comp rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Fiber.id_def C b c))
    HEq.rfl).trans ?_
  refine (C.id_comp_heq (pushLift α c)).trans ?_
  exact (C.comp_id_heq (pushLift α c)).symm

/-- `pushMap` preserves composition (stated with the fiber composite unfolded to `castHom`). -/
theorem pushMap_comp (α : a ⟶ a') {b : B.Ob a} {c c' c'' : C.Fiber b} (f : c ⟶ c') (g : c' ⟶ c'') :
    pushMap α (f ≫ g)
      = C.castHom
          (pushMap α f ≫ᵈᵈ pushMap α g) := by
  refine IsOpcartesian.hom_ext (pushLift_opcartesian α c) (eq_of_heq ?_)
  -- common target `T := f ≫ᵈᵈ (g ≫ᵈᵈ pushLift α c'')`
  have hL : pushLift α c ≫ᵈᵈ pushMap α (f ≫ g) ≍ f ≫ᵈᵈ (g ≫ᵈᵈ pushLift α c'') := by
    rw [pushLift_pushMap, DoubleDisplayed.Fiber.comp_def]
    refine (C.castHom_heq _ _ _).trans ?_
    refine (C.heq_comp (Category.id_comp (𝟙 a)).symm rfl rfl HEq.rfl (B.id_comp_heq (B.id b)).symm
      HEq.rfl (C.castHom_heq _ _ _) HEq.rfl).trans ?_
    exact C.assoc_heq f g (pushLift α c'')
  have hR : pushLift α c ≫ᵈᵈ C.castHom (pushMap α f ≫ᵈᵈ pushMap α g)
      (Category.comp_id (𝟙 a')) (B.id_comp (B.id (B.transp α b)))
      ≍ f ≫ᵈᵈ (g ≫ᵈᵈ pushLift α c'') := by
    refine (C.heq_comp rfl (Category.comp_id (𝟙 a')).symm rfl HEq.rfl HEq.rfl
      (B.id_comp_heq (B.id (B.transp α b))).symm HEq.rfl (C.castHom_heq _ _ _)).trans ?_
    refine (C.assoc_heq (pushLift α c) (pushMap α f) (pushMap α g)).symm.trans ?_
    refine (C.heq_comp (by simp) rfl rfl HEq.rfl (push_base_heq α b).symm HEq.rfl
      ((heq_of_eq (pushLift_pushMap α f)).trans (C.castHom_heq _ _ _)) HEq.rfl).trans ?_
    refine (C.assoc_heq f (pushLift α c') (pushMap α g)).trans ?_
    refine C.heq_comp rfl (by simp) rfl HEq.rfl HEq.rfl (push_base_heq α b).symm HEq.rfl ?_
    exact (heq_of_eq (pushLift_pushMap α g)).trans (C.castHom_heq _ _ _)
  exact hL.trans hR.symm

/-- The pushforward functor on fibers. -/
noncomputable def pushFunctor (α : a ⟶ a') (b : B.Ob a) : C.Fiber b ⥤ C.Fiber (B.transp α b) where
  obj c := push α c
  map f := pushMap α f
  map_id c := pushMap_id α c
  map_comp f g := by rw [DoubleDisplayed.Fiber.comp_def]; exact pushMap_comp α f g

@[simp] theorem pushFunctor_obj (α : a ⟶ a') (b : B.Ob a) (c : C.Fiber b) :
    (pushFunctor α b).obj c = push α c := rfl

@[simp] theorem pushFunctor_map (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    (pushFunctor α b).map f = pushMap α f := rfl

/-- Pushforward along the identity acts trivially on morphisms (heterogeneously). -/
theorem pushMap_id_heq {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    pushMap (𝟙 a) f ≍ f := by
  have hidt : B.id (B.transp (𝟙 a) b) ≍ B.id b := by rw [B.transp_id]
  have step : f ≫ᵈᵈ pushLift (𝟙 a) c' ≍ f ≫ᵈᵈ C.id c' :=
    C.heq_comp_right rfl (B.transp_id b) (B.olift_id_heq b) (push_id_heq c') (pushLift_id_heq c')
  have hcomp : pushLift (𝟙 a) c ≫ᵈᵈ pushMap (𝟙 a) f ≍ C.id c ≫ᵈᵈ f := by
    refine (heq_of_eq (pushLift_pushMap (𝟙 a) f)).trans ?_
    refine (C.castHom_heq _ _ _).trans ?_
    exact step.trans ((C.comp_id_heq f).trans (C.id_comp_heq f).symm)
  exact DoubleDisplayed.IsOpcartesian.hom_ext_heq (pushLift_opcartesian (𝟙 a) c)
    (B.transp_id b) (B.olift_id_heq b) (push_id_heq c) (pushLift_id_heq c)
    (B.transp_id b) hidt (push_id_heq c') hcomp

/-- Pushforward along a composite acts as the composite of pushforwards (heterogeneously). -/
theorem pushMap_comp_base {a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {c c' : C.Fiber b}
    (f : c ⟶ c') : pushMap (α ≫ α') f ≍ pushMap α' (pushMap α f) := by
  have hidt : B.id (B.transp (α ≫ α') b) ≍ B.id (B.transp α' (B.transp α b)) := by
    rw [B.transp_comp]
  have hL : pushLift (α ≫ α') c ≫ᵈᵈ pushMap (α ≫ α') f
      ≍ f ≫ᵈᵈ (pushLift α c' ≫ᵈᵈ pushLift α' (push α c')) := by
    refine (heq_of_eq (pushLift_pushMap (α ≫ α') f)).trans ?_
    refine (C.castHom_heq _ _ _).trans ?_
    exact C.heq_comp_right rfl (B.transp_comp α α' b) (B.olift_comp_heq α α' b)
      (push_comp_heq α α' c') (pushLift_comp_heq α α' c')
  have hR : (pushLift α c ≫ᵈᵈ pushLift α' (push α c)) ≫ᵈᵈ pushMap α' (pushMap α f)
      ≍ f ≫ᵈᵈ (pushLift α c' ≫ᵈᵈ pushLift α' (push α c')) := by
    refine (C.assoc_heq (pushLift α c) (pushLift α' (push α c)) (pushMap α' (pushMap α f))).trans ?_
    refine (C.heq_comp_right (by simp) rfl (push_base_heq α' (B.transp α b)).symm HEq.rfl
      ((heq_of_eq (pushLift_pushMap α' (pushMap α f))).trans (C.castHom_heq _ _ _))).trans ?_
    refine (C.assoc_heq (pushLift α c) (pushMap α f) (pushLift α' (push α c'))).symm.trans ?_
    refine (C.heq_comp_left (by simp) rfl (push_base_heq α b).symm HEq.rfl
      ((heq_of_eq (pushLift_pushMap α f)).trans (C.castHom_heq _ _ _))).trans ?_
    exact C.assoc_heq f (pushLift α c') (pushLift α' (push α c'))
  have hcomp : pushLift (α ≫ α') c ≫ᵈᵈ pushMap (α ≫ α') f
      ≍ (pushLift α c ≫ᵈᵈ pushLift α' (push α c)) ≫ᵈᵈ pushMap α' (pushMap α f) := hL.trans hR.symm
  exact DoubleDisplayed.IsOpcartesian.hom_ext_heq (pushLift_opcartesian (α ≫ α') c)
    (B.transp_comp α α' b) (B.olift_comp_heq α α' b) (push_comp_heq α α' c)
    (pushLift_comp_heq α α' c)
    (B.transp_comp α α' b) hidt (push_comp_heq α α' c') hcomp

end PushMap

section PullMap

variable {a : A}

omit [SplitOpfib B] [D2SFib C] in
/-- The base equality witnessing `β ≫ᵈ B.id b'` and `B.id b ≫ᵈ β` both reduce to `β`. -/
private theorem pull_base_heq {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    β ≫ᵈ B.id b' ≍ B.id b ≫ᵈ β :=
  (B.comp_id_heq β).trans (B.id_comp_heq β).symm

/-- The unique factorization through a chosen cartesian lift. -/
noncomputable def pullDesc {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (χ : c₀ ⟶[[β₀ ≫ᵈ β]] c) :
    c₀ ⟶[[β₀]] (pull β c) :=
  (pullLift_cartesian β c β₀ c₀ χ).choose

@[simp]
theorem pullDesc_fac {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (χ : c₀ ⟶[[β₀ ≫ᵈ β]] c) :
    pullDesc β c β₀ c₀ χ ≫ᵈᵈ pullLift β c = χ :=
  (pullLift_cartesian β c β₀ c₀ χ).choose_spec.1

theorem pullDesc_uniq {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) {χ : c₀ ⟶[[β₀ ≫ᵈ β]] c}
    (ξ : c₀ ⟶[[β₀]] (pull β c)) (hξ : ξ ≫ᵈᵈ pullLift β c = χ) : ξ = pullDesc β c β₀ c₀ χ :=
  (pullLift_cartesian β c β₀ c₀ χ).choose_spec.2 ξ hξ

/-- Two maps into `pull β c` agreeing after postcomposition with `pullLift β c` are equal. -/
theorem pull_hom_ext {b b' b₀ : B.Ob a} {β : b ⟶[𝟙 a] b'} {c : C.Ob b'}
    {β₀ : b₀ ⟶[𝟙 a] b} {c₀ : C.Ob b₀} {ξ ξ' : c₀ ⟶[[β₀]] (pull β c)}
    (h : ξ ≫ᵈᵈ pullLift β c = ξ' ≫ᵈᵈ pullLift β c) : ξ = ξ' :=
  (pullDesc_uniq β c β₀ c₀ ξ rfl).trans (pullDesc_uniq β c β₀ c₀ ξ' h.symm).symm

/-- Functorial action of pullback on vertical morphisms. -/
noncomputable def pullMap {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'} (f : c ⟶ c') :
    (pull β c) ⟶[[B.id b]] (pull β c') :=
  pullDesc β c' (B.id b) (pull β c) (C.castHom (pullLift β c ≫ᵈᵈ f))

/-- Descent characterization of `pullMap`. -/
theorem pullMap_pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'} (f : c ⟶ c') :
    pullMap β f ≫ᵈᵈ pullLift β c'
      = C.castHom (pullLift β c ≫ᵈᵈ f) :=
  pullDesc_fac β c' (B.id b) (pull β c) _

/-- `pullMap` preserves identities. -/
theorem pullMap_id {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Fiber b') :
    pullMap β (𝟙 c) = C.id (pull β c) := by
  refine pull_hom_ext (eq_of_heq ?_)
  refine (heq_of_eq (pullMap_pullLift β (𝟙 c))).trans ?_
  refine (C.castHom_heq _ _ _).trans ?_
  refine (C.heq_comp rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Fiber.id_def C b' c)))
    |>.trans ?_
  refine (C.comp_id_heq (pullLift β c)).trans ?_
  exact (C.id_comp_heq (pullLift β c)).symm

/-- `pullMap` preserves composition (stated with the fiber composite unfolded to `castHom`). -/
theorem pullMap_comp {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' c'' : C.Fiber b'}
    (f : c ⟶ c') (g : c' ⟶ c'') :
    pullMap β (f ≫ g)
      = C.castHom (pullMap β f ≫ᵈᵈ pullMap β g) := by
  refine pull_hom_ext (eq_of_heq ?_)
  -- common target `T := (pullLift β c ≫ᵈᵈ f) ≫ᵈᵈ g`
  have hL : pullMap β (f ≫ g) ≫ᵈᵈ pullLift β c'' ≍ (pullLift β c ≫ᵈᵈ f) ≫ᵈᵈ g := by
    rw [pullMap_pullLift, DoubleDisplayed.Fiber.comp_def]
    refine (C.castHom_heq _ _ _).trans ?_
    refine (C.heq_comp rfl (Category.id_comp (𝟙 a)).symm rfl HEq.rfl HEq.rfl
      (B.id_comp_heq (B.id b')).symm HEq.rfl (C.castHom_heq _ _ _)).trans ?_
    exact (C.assoc_heq (pullLift β c) f g).symm
  have hR : C.castHom (pullMap β f ≫ᵈᵈ pullMap β g)
        (Category.comp_id (𝟙 a)) (B.id_comp (B.id b))
      ≫ᵈᵈ pullLift β c'' ≍ (pullLift β c ≫ᵈᵈ f) ≫ᵈᵈ g := by
    refine (C.heq_comp (Category.comp_id (𝟙 a)).symm rfl rfl HEq.rfl
      (B.id_comp_heq (B.id b)).symm HEq.rfl (C.castHom_heq _ _ _) HEq.rfl).trans ?_
    refine (C.assoc_heq (pullMap β f) (pullMap β g) (pullLift β c'')).trans ?_
    refine (C.heq_comp rfl (by simp) rfl HEq.rfl HEq.rfl (pull_base_heq β).symm HEq.rfl
      ((heq_of_eq (pullMap_pullLift β g)).trans (C.castHom_heq _ _ _))).trans ?_
    refine (C.assoc_heq (pullMap β f) (pullLift β c') g).symm.trans ?_
    refine C.heq_comp (by simp) rfl rfl HEq.rfl (pull_base_heq β).symm HEq.rfl
      ((heq_of_eq (pullMap_pullLift β f)).trans (C.castHom_heq _ _ _)) HEq.rfl
  exact hL.trans hR.symm

/-- The pullback functor on fibers. -/
noncomputable def pullFunctor {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') : C.Fiber b' ⥤ C.Fiber b where
  obj c := pull β c
  map f := pullMap β f
  map_id c := pullMap_id β c
  map_comp f g := by rw [DoubleDisplayed.Fiber.comp_def]; exact pullMap_comp β f g

@[simp] theorem pullFunctor_obj {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Fiber b') :
    (pullFunctor β).obj c = pull β c := rfl

@[simp] theorem pullFunctor_map {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') : (pullFunctor β).map f = pullMap β f := rfl

/-- The chosen cartesian lift is cartesian (as the `IsCartesian` predicate). -/
theorem pullLift_isCartesian {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    DoubleDisplayed.IsCartesian (pullLift β c) :=
  fun β₀ c₀ χ => pullLift_cartesian β c β₀ c₀ χ

/-- Pullback along the identity vertical morphism acts trivially on morphisms (heterogeneously). -/
theorem pullMap_idBase_heq {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    pullMap (B.id b) f ≍ f := by
  have hcomp : pullMap (B.id b) f ≫ᵈᵈ pullLift (B.id b) c' ≍ f ≫ᵈᵈ C.id c' := by
    refine (heq_of_eq (pullMap_pullLift (B.id b) f)).trans ?_
    refine (C.castHom_heq _ _ _).trans ?_
    refine (C.heq_comp_left rfl rfl HEq.rfl (heq_of_eq (pull_id c)) (pullLift_id_heq c)).trans ?_
    exact (C.id_comp_heq f).trans (C.comp_id_heq f).symm
  exact DoubleDisplayed.IsCartesian.hom_ext_heq (pullLift_isCartesian (B.id b) c')
    rfl rfl rfl HEq.rfl (heq_of_eq (pull_id c')) (pullLift_id_heq c')
    rfl HEq.rfl (heq_of_eq (pull_id c)) hcomp

/-- Pulling back along a vertical identity is the identity functor, on the nose. -/
theorem pullFunctor_id {b : B.Ob a} : pullFunctor (C := C) (B.id b) = 𝟭 (C.Fiber b) :=
  CategoryTheory.Functor.hext (fun c => pull_id c) (fun _ _ f => pullMap_idBase_heq f)

/-- Pullback along an `eqToHom` acts trivially on objects (heterogeneously). -/
theorem pull_eqToHom {b b' : B.Fiber a} (h : b = b') (c : C.Ob b') :
    pull (eqToHom h) c ≍ c := by
  subst h; exact heq_of_eq (pull_id c)

/-- Pullback along an `eqToHom` acts trivially on morphisms (heterogeneously). -/
theorem pullMap_eqToHom {b b' : B.Fiber a} (h : b = b') {c c' : C.Fiber b'} (f : c ⟶ c') :
    pullMap (eqToHom h) f ≍ f := by
  subst h; exact pullMap_idBase_heq f

/-- Pullback along a composite acts as the (reversed) composite of pullbacks (heterogeneously). -/
theorem pullMap_comp_base {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'')
    {c c' : C.Fiber b''} (f : c ⟶ c') : pullMap (β ≫ γ) f ≍ pullMap β (pullMap γ f) := by
  have hbg : (β ≫ γ) ≍ (β ≫ᵈ γ) := B.castHom_heq (β ≫ᵈ γ) (Category.comp_id (𝟙 a))
  have hL : pullMap (β ≫ γ) f ≫ᵈᵈ pullLift (β ≫ γ) c'
      ≍ pullLift β (pull γ c) ≫ᵈᵈ (pullLift γ c ≫ᵈᵈ f) := by
    refine (heq_of_eq (pullMap_pullLift (β ≫ γ) f)).trans ?_
    refine (C.castHom_heq _ _ _).trans ?_
    refine (C.heq_comp_left (by simp) rfl hbg (heq_of_eq (pull_comp β γ c))
      (pullLift_comp_heq β γ c)).trans ?_
    exact C.assoc_heq (pullLift β (pull γ c)) (pullLift γ c) f
  have hR : pullMap β (pullMap γ f) ≫ᵈᵈ (pullLift β (pull γ c') ≫ᵈᵈ pullLift γ c')
      ≍ pullLift β (pull γ c) ≫ᵈᵈ (pullLift γ c ≫ᵈᵈ f) := by
    refine (C.assoc_heq (pullMap β (pullMap γ f)) (pullLift β (pull γ c'))
      (pullLift γ c')).symm.trans ?_
    refine (C.heq_comp_left (by simp) rfl (pull_base_heq β).symm HEq.rfl
      ((heq_of_eq (pullMap_pullLift β (pullMap γ f))).trans (C.castHom_heq _ _ _))).trans ?_
    refine (C.assoc_heq (pullLift β (pull γ c)) (pullMap γ f) (pullLift γ c')).trans ?_
    exact C.heq_comp_right (by simp) rfl (pull_base_heq γ).symm HEq.rfl
      ((heq_of_eq (pullMap_pullLift γ f)).trans (C.castHom_heq _ _ _))
  have hcomp : pullMap (β ≫ γ) f ≫ᵈᵈ pullLift (β ≫ γ) c'
      ≍ pullMap β (pullMap γ f) ≫ᵈᵈ (pullLift β (pull γ c') ≫ᵈᵈ pullLift γ c') := hL.trans hR.symm
  exact DoubleDisplayed.IsCartesian.hom_ext_heq (pullLift_isCartesian (β ≫ γ) c')
    (by simp) rfl rfl hbg (heq_of_eq (pull_comp β γ c')) (pullLift_comp_heq β γ c')
    rfl HEq.rfl (heq_of_eq (pull_comp β γ c)) hcomp

end PullMap

section Interchange

variable {a a' : A}

/-- The push/pull lift square, packaged from the `pushLift_pullLift` field (with the object cast
`push_pull` carried by `▸`). -/
theorem pushLift_pullLift_square (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    (c : C.Ob b') : pullLift β c ≫ᵈᵈ pushLift α c
      ≍ (push_pull α β c ▸ pushLift α (pull β c)) ≫ᵈᵈ pullLift (B.transpMap α β) (push α c) :=
  by
  have hδ : (push_pull α β c ▸ pushLift α (pull β c)) ≍ pushLift α (pull β c) :=
    eqRec_heq_self _ _
  refine ((C.castHom_eq_iff_heq _ _).mp (D2SFib.pushLift_pullLift α β c)).trans ?_
  exact C.heq_comp_left (by simp) rfl (B.comp_id_heq _) HEq.rfl
    ((C.comp_eqToHom_heq' _ _).trans hδ.symm)

/-- `pull` respects heterogeneous equality of the vertical morphism and the object. -/
theorem pull_congr_obj {b b' b'₂ : B.Ob a} {β : b ⟶[𝟙 a] b'} {β₂ : b ⟶[𝟙 a] b'₂}
    {c : C.Ob b'} {d : C.Ob b'₂} (hb' : b' = b'₂) (hβ : β ≍ β₂) (hc : c ≍ d) :
    pull β c ≍ pull β₂ d := by
  subst hb'; obtain rfl := eq_of_heq hβ; obtain rfl := eq_of_heq hc; rfl

/-- `pushMap α` respects heterogeneous equality of morphisms. -/
theorem pushMap_congr (α : a ⟶ a') {b b₂ : B.Ob a} {c c' : C.Fiber b} {d d' : C.Fiber b₂}
    {f : c ⟶ c'} {g : d ⟶ d'} (hb : b = b₂) (hc : c ≍ d) (hc' : c' ≍ d') (hf : f ≍ g) :
    pushMap α f ≍ pushMap α g := by
  subst hb; obtain rfl := eq_of_heq hc; obtain rfl := eq_of_heq hc'; obtain rfl := eq_of_heq hf; rfl

/-- `pullMap` respects heterogeneous equality of the vertical morphism and the morphism. -/
theorem pullMap_congr {b b' b'₂ : B.Ob a} {β : b ⟶[𝟙 a] b'} {β₂ : b ⟶[𝟙 a] b'₂}
    {c c' : C.Fiber b'} {d d' : C.Fiber b'₂} {f : c ⟶ c'} {g : d ⟶ d'}
    (hb' : b' = b'₂) (hβ : β ≍ β₂) (hc : c ≍ d) (hc' : c' ≍ d') (hf : f ≍ g) :
    pullMap β f ≍ pullMap β₂ g := by
  subst hb'; obtain rfl := eq_of_heq hβ; obtain rfl := eq_of_heq hc; obtain rfl := eq_of_heq hc'
  obtain rfl := eq_of_heq hf; rfl

/-- The push/pull interchange on morphisms (the paper's `d2sfib:lemma`). -/
theorem pushMap_pullMap (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : C.Fiber b'} (f : c ⟶ c') :
    pushMap α (pullMap β f) ≍ pullMap (B.transpMap α β) (pushMap α f) := by
  have hθ₂ : ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c'))
      ≍ pullLift (B.transpMap α β) (push α c') := eqRec_heq_self _ _
  have hδc : (push_pull α β c ▸ pushLift α (pull β c)) ≍ pushLift α (pull β c) :=
    eqRec_heq_self _ _
  -- Side B, by inner opcartesian uniqueness (details filled below)
  have hδc' : (push_pull α β c' ▸ pushLift α (pull β c')) ≍ pushLift α (pull β c') :=
    eqRec_heq_self _ _
  -- consequence of the square at `c'`
  have hsq' : pushLift α (pull β c')
        ≫ᵈᵈ ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c'))
      ≍ pullLift β c' ≫ᵈᵈ pushLift α c' := by
    refine HEq.trans ?_ (pushLift_pullLift_square α β c').symm
    exact C.heq_comp rfl rfl rfl (heq_of_eq (push_pull α β c')) HEq.rfl HEq.rfl hδc'.symm hθ₂
  have sideB : pushMap α (pullMap β f)
        ≫ᵈᵈ ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c'))
      ≍ pullLift (B.transpMap α β) (push α c) ≫ᵈᵈ pushMap α f := by
    refine DoubleDisplayed.IsOpcartesian.hom_ext_heq (pushLift_opcartesian α (pull β c))
      rfl HEq.rfl (heq_of_eq (push_pull α β c)) hδc.symm
      rfl ((pull_base_heq (B.transpMap α β)).symm) HEq.rfl ?_
    -- inner: pushLift α (pull β c) ≫ᵈᵈ (…) ≍ δc ≫ᵈᵈ (…), both ≍ N
    have inner_L : pushLift α (pull β c)
          ≫ᵈᵈ (pushMap α (pullMap β f)
            ≫ᵈᵈ ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c')))
        ≍ pullLift β c ≫ᵈᵈ (f ≫ᵈᵈ pushLift α c') := by
      refine (C.assoc_heq (pushLift α (pull β c)) (pushMap α (pullMap β f))
        ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c'))).symm.trans ?_
      refine (C.heq_comp_left rfl rfl HEq.rfl HEq.rfl
        (heq_of_eq (pushLift_pushMap α (pullMap β f)))).trans ?_
      refine (C.heq_comp_left (by simp) rfl (push_base_heq α b).symm HEq.rfl
        (C.castHom_heq _ _ _)).trans ?_
      refine (C.assoc_heq (pullMap β f) (pushLift α (pull β c'))
        ((push_pull α β c').symm ▸ pullLift (B.transpMap α β) (push α c'))).trans ?_
      refine (C.heq_comp_right (by simp) rfl (B.olift_transpMap_heq α β) HEq.rfl hsq').trans ?_
      refine (C.assoc_heq (pullMap β f) (pullLift β c') (pushLift α c')).symm.trans ?_
      refine (C.heq_comp_left rfl rfl HEq.rfl HEq.rfl (heq_of_eq (pullMap_pullLift β f))).trans ?_
      refine (C.heq_comp_left (by simp) rfl (pull_base_heq β).symm HEq.rfl
        (C.castHom_heq _ _ _)).trans ?_
      exact C.assoc_heq (pullLift β c) f (pushLift α c')
    have inner_R : (push_pull α β c ▸ pushLift α (pull β c))
          ≫ᵈᵈ (pullLift (B.transpMap α β) (push α c) ≫ᵈᵈ pushMap α f)
        ≍ pullLift β c ≫ᵈᵈ (f ≫ᵈᵈ pushLift α c') := by
      refine (C.assoc_heq (push_pull α β c ▸ pushLift α (pull β c))
        (pullLift (B.transpMap α β) (push α c)) (pushMap α f)).symm.trans ?_
      refine (C.heq_comp_left (by simp) rfl (B.olift_transpMap_heq α β) HEq.rfl
        (pushLift_pullLift_square α β c).symm).trans ?_
      refine (C.assoc_heq (pullLift β c) (pushLift α c) (pushMap α f)).trans ?_
      refine (C.heq_comp_right rfl rfl HEq.rfl HEq.rfl
        (heq_of_eq (pushLift_pushMap α f))).trans ?_
      exact C.heq_comp_right (by simp) rfl (push_base_heq α b').symm HEq.rfl (C.castHom_heq _ _ _)
    exact inner_L.trans inner_R.symm
  refine HEq.symm (DoubleDisplayed.IsCartesian.hom_ext_heq
    (pullLift_isCartesian (B.transpMap α β) (push α c'))
    rfl rfl rfl HEq.rfl (heq_of_eq (push_pull α β c').symm) hθ₂.symm
    rfl HEq.rfl (heq_of_eq (push_pull α β c).symm) ?_)
  refine (heq_of_eq (pullMap_pullLift (B.transpMap α β) (pushMap α f))).trans ?_
  exact (C.castHom_heq _ _ _).trans sideB.symm

end Interchange

section HomEquiv

variable {a a' : A}

/-- Opcartesian descent along the chosen pushforward lift, as a bijection of hom-sets. -/
noncomputable def pushDescEquiv (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) {a'' : A} {γ : a' ⟶ a''}
    {b'' : B.Ob a''} (g' : (B.transp α b) ⟶[γ] b'') (c'' : C.Ob b'') :
    ((push α c) ⟶[[g']] c'') ≃ (c ⟶[[B.olift α b ≫ᵈ g']] c'') where
  toFun ψ := pushLift α c ≫ᵈᵈ ψ
  invFun χ := DoubleDisplayed.IsOpcartesian.desc (pushLift_opcartesian α c) g' χ
  left_inv _ :=
    (DoubleDisplayed.IsOpcartesian.desc_uniq (pushLift_opcartesian α c) _ rfl).symm
  right_inv χ := DoubleDisplayed.IsOpcartesian.desc_fac (pushLift_opcartesian α c) g' χ

@[simp]
theorem pushDescEquiv_apply (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) {a'' : A} {γ : a' ⟶ a''}
    {b'' : B.Ob a''} (g' : (B.transp α b) ⟶[γ] b'') (c'' : C.Ob b'')
    (ψ : (push α c) ⟶[[g']] c'') : pushDescEquiv α c g' c'' ψ = pushLift α c ≫ᵈᵈ ψ := rfl

/-- Cartesian lifting along the chosen pullback lift, as a bijection of hom-sets. -/
noncomputable def pullLiftEquiv {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) :
    (c₀ ⟶[[β₀]] (pull β c)) ≃ (c₀ ⟶[[β₀ ≫ᵈ β]] c) where
  toFun ξ := ξ ≫ᵈᵈ pullLift β c
  invFun χ := pullDesc β c β₀ c₀ χ
  left_inv _ := (pullDesc_uniq β c β₀ c₀ _ rfl).symm
  right_inv χ := pullDesc_fac β c β₀ c₀ χ

@[simp]
theorem pullLiftEquiv_apply {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (ξ : c₀ ⟶[[β₀]] (pull β c)) :
    pullLiftEquiv β c β₀ c₀ ξ = ξ ≫ᵈᵈ pullLift β c := rfl

/-- Any displayed morphism is heterogeneously the chosen lift followed by its factorization. -/
theorem olift_factor_heq (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') :
    g ≍ B.olift α b ≫ᵈ B.factor g :=
  ((heq_of_eq (B.olift_factor g)).trans (B.castHom_heq g _)).symm

/-- **The two-sided hom equivalence** (the paper's `hom(α_! c, β^* c') ≅ hom(c, c')`): morphisms of
`C` over `g : B.Hom α b b'` correspond to *vertical* morphisms `push α c ⟶ pull (B.factor g) c'` in
the fiber over `B.transp α b`. This is the bridge used by M9's counit isomorphism. -/
noncomputable def d2sHomEquiv (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : C.Ob b) (c' : C.Ob b') :
    (c ⟶[[g]] c') ≃ ((push α c) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) c')) :=
  (C.castHomEquiv (Category.comp_id α).symm (B.olift_factor g).symm).trans
    ((pushDescEquiv α c (B.factor g) c').symm.trans
      ((C.castHomEquiv (Category.comp_id (𝟙 a')) (B.id_comp (B.factor g))).symm.trans
        (pullLiftEquiv (B.factor g) c' (B.id (B.transp α b)) (push α c)).symm))

/-- The inverse of `d2sHomEquiv`, unfolded: it composes with the two chosen lifts, up to the two
`castHom`s absorbing `α ≫ 𝟙 a' = α` and `𝟙 a' ≫ 𝟙 a' = 𝟙 a'`. -/
theorem d2sHomEquiv_symm_apply (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : C.Ob b) (c' : C.Ob b')
    (f : (push α c) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) c')) :
    (d2sHomEquiv α g c c').symm f
      = C.castHom (pushLift α c ≫ᵈᵈ C.castHom (f ≫ᵈᵈ pullLift (B.factor g) c')
          (Category.comp_id (𝟙 a')) (B.id_comp (B.factor g))) := rfl

/-- The inverse of `d2sHomEquiv` is "compose with the two chosen lifts", up to `castHom`. -/
theorem d2sHomEquiv_symm_apply_heq (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : C.Ob b) (c' : C.Ob b')
    (f : (push α c) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) c')) :
    (d2sHomEquiv α g c c').symm f
      ≍ pushLift α c ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.factor g) c') := by
  rw [d2sHomEquiv_symm_apply]
  refine (C.castHom_heq _ _ _).trans ?_
  exact C.heq_comp_right (Category.comp_id (𝟙 a')).symm rfl
    (B.id_comp_heq (B.factor g)).symm HEq.rfl (C.castHom_heq _ _ _)

/-- Characterization of `d2sHomEquiv`: it is the unique factorization through the two chosen
lifts. -/
theorem d2sHomEquiv_heq (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') (c : C.Ob b)
    (c' : C.Ob b') (θ : c ⟶[[g]] c') :
    pushLift α c ≫ᵈᵈ (d2sHomEquiv α g c c' θ ≫ᵈᵈ pullLift (B.factor g) c') ≍ θ :=
  ((d2sHomEquiv_symm_apply_heq α g c c' _).symm.trans
    (heq_of_eq ((d2sHomEquiv α g c c').symm_apply_apply θ)))

/-- Uniqueness half of `d2sHomEquiv`: a vertical morphism whose composite with the two chosen lifts
is `θ` is `d2sHomEquiv θ`. -/
theorem d2sHomEquiv_eq_of_heq (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c')
    (f : (push α c) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) c'))
    (hf : pushLift α c ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.factor g) c') ≍ θ) :
    f = d2sHomEquiv α g c c' θ := by
  have h : (d2sHomEquiv α g c c').symm f = θ :=
    eq_of_heq ((d2sHomEquiv_symm_apply_heq α g c c' f).trans hf)
  rw [← h, Equiv.apply_symm_apply]

end HomEquiv

section SigmaBridge

/-! The `≍`-heavy computations that remain for M9 (`d2sHomEquiv_comp`, see `DEVIATIONS.md` D24) are
best done in the honest category `(C.sigma).Total`, exactly as M8's prerequisites were done in
`D.Total` (`Displayed.heq_of_totalHom_eq`). This section provides that bridge one level up. -/

variable {a a' a'' : A}

/-- A `C`-morphism, viewed as a morphism of the honest total category of `C.sigma`. -/
def totC {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') {c : C.Ob b} {c' : C.Ob b'}
    (θ : c ⟶[[g]] c') :
    (C.sigma).tot (⟨b, c⟩ : (C.sigma).Ob a) ⟶ (C.sigma).tot (⟨b', c'⟩ : (C.sigma).Ob a') :=
  (C.sigma).totalMk α ⟨g, θ⟩

omit [SplitOpfib B] [D2SFib C] in
@[simp]
theorem totC_comp {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}
    (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') {c : C.Ob b} {c' : C.Ob b'} {c'' : C.Ob b''}
    (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    totC g θ ≫ totC g' θ' = totC (g ≫ᵈ g') (θ ≫ᵈᵈ θ') := rfl

omit [SplitOpfib B] [D2SFib C] in
/-- **The `sigma`-level bridge**: a `≍` of `C`-morphisms with common endpoints follows from an
equality of the corresponding morphisms of the honest category `(C.sigma).Total`, where
reassociation is `Category.assoc`. -/
theorem heq_of_totC_eq {α α₂ : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'}
    {g₂ : b ⟶[α₂] b'} {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'} {θ₂ : c ⟶[[g₂]] c'}
    (h : totC g θ = totC g₂ θ₂) : θ ≍ θ₂ := by
  have hb : α = α₂ := congrArg Total.Hom.base h
  subst hb
  have h2 : (⟨g, θ⟩ : DoubleDisplayed.Sigma.Hom C α ⟨b, c⟩ ⟨b', c'⟩) = ⟨g₂, θ₂⟩ :=
    eq_of_heq (heq_of_totalHom_eq (C.sigma) h)
  injection h2 with _ h3

omit [SplitOpfib B] [D2SFib C] in
/-- The converse bridge: a `≍` of `C`-morphisms with common endpoints gives an equality in
`(C.sigma).Total`. Together with `heq_of_totC_eq` this lets a whole `≍`-computation be carried out
as a `rw`-chain in an honest category. -/
theorem totC_eq_of_heq {α α₂ : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'}
    {g₂ : b ⟶[α₂] b'} {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'} {θ₂ : c ⟶[[g₂]] c'}
    (hα : α = α₂) (hg : g ≍ g₂) (h : θ ≍ θ₂) : totC g θ = totC g₂ θ₂ := by
  subst hα
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq h
  rfl

omit [SplitOpfib B] [D2SFib C] in
/-- Objects of `(C.sigma).Total` are equal when their components are. -/
theorem sigmaTotEq {b b₂ : B.Ob a} {c : C.Ob b} {c₂ : C.Ob b₂} (hb : b = b₂) (hc : c ≍ c₂) :
    (C.sigma).tot (⟨b, c⟩ : (C.sigma).Ob a) = (C.sigma).tot (⟨b₂, c₂⟩ : (C.sigma).Ob a) := by
  subst hb; obtain rfl := eq_of_heq hc; rfl

omit [SplitOpfib B] [D2SFib C] in
/-- Vertical `C`-morphisms compose in `(C.sigma).Total` as they do in the fiber. -/
@[simp] theorem totC_vert_comp {b : B.Ob a} {c c' c'' : C.Fiber b} (u : c ⟶ c') (v : c' ⟶ c'') :
    totC (B.id b) u ≫ totC (B.id b) v = totC (B.id b) (u ≫ v) := by
  rw [totC_comp]
  refine totC_eq_of_heq (by simp) (B.id_comp_heq (B.id b)) ?_
  rw [DoubleDisplayed.Fiber.comp_def]
  exact (C.castHom_heq _ _ _).symm

omit [SplitOpfib B] [D2SFib C] in
/-- A fiber `eqToHom`, viewed in `(C.sigma).Total`, is an `eqToHom`. -/
theorem totC_vert_eqToHom {b : B.Ob a} {c c' : C.Fiber b} (h : c = c') :
    totC (B.id b) (eqToHom h) = eqToHom (sigmaTotEq rfl (heq_of_eq h)) := by
  subst h; rfl

omit [SplitOpfib B] [D2SFib C] in
/-- Conjugation form of the bridge: a `≍` of `C`-morphisms with `≍` endpoints becomes an equality
in `(C.sigma).Total` after conjugating by `eqToHom`s. -/
theorem totC_heq_conj {α α₂ : a ⟶ a'} {b b₂ : B.Ob a} {b' b'₂ : B.Ob a'}
    {g : b ⟶[α] b'} {g₂ : b₂ ⟶[α₂] b'₂} {c : C.Ob b} {c₂ : C.Ob b₂}
    {c' : C.Ob b'} {c'₂ : C.Ob b'₂} {θ : c ⟶[[g]] c'} {θ₂ : c₂ ⟶[[g₂]] c'₂}
    (hb : b = b₂) (hc : c ≍ c₂) (hb' : b' = b'₂) (hc' : c' ≍ c'₂)
    (hα : α = α₂) (hg : g ≍ g₂) (hθ : θ ≍ θ₂) :
    totC g θ
      = eqToHom (sigmaTotEq hb hc) ≫ totC g₂ θ₂ ≫ eqToHom (sigmaTotEq hb' hc').symm := by
  subst hb; subst hb'; obtain rfl := eq_of_heq hc; obtain rfl := eq_of_heq hc'
  subst hα; obtain rfl := eq_of_heq hg; obtain rfl := eq_of_heq hθ
  simp

/-- `pull` respects heterogeneous equality in the *domain* of the vertical morphism. -/
theorem pull_congr_dom {b b₂ b' : B.Ob a} {β : b ⟶[𝟙 a] b'} {β₂ : b₂ ⟶[𝟙 a] b'}
    (hb : b = b₂) (hβ : β ≍ β₂) (c : C.Ob b') : pull β c ≍ pull β₂ c := by
  subst hb; obtain rfl := eq_of_heq hβ; rfl

/-- `pullLift` respects heterogeneous equality in the *domain* of the vertical morphism. -/
theorem pullLift_congr_dom {b b₂ b' : B.Ob a} {β : b ⟶[𝟙 a] b'} {β₂ : b₂ ⟶[𝟙 a] b'}
    (hb : b = b₂) (hβ : β ≍ β₂) (c : C.Ob b') : pullLift β c ≍ pullLift β₂ c := by
  subst hb; obtain rfl := eq_of_heq hβ; rfl

/-! ### Compatibility of `d2sHomEquiv` with composition -/

/-- The pullback along the factorization of a composite, split up. -/
theorem pull_factor_comp_heq (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') (c'' : C.Ob b'') :
    pull (B.factor (g ≫ᵈ g')) c''
      ≍ pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c'') :=
  (pull_congr_dom (B.transp_comp α α' b) (B.factor_comp_heq g g') c'').trans
    (heq_of_eq (pull_comp (B.transpMap α' (B.factor g)) (B.factor g') c''))

set_option maxHeartbeats 1000000 in
-- The proof is one long `rw`-chain in `(C.sigma).Total`; elaborating its large displayed-morphism
-- terms exceeds the default heartbeat budget.
/-- **`d2sHomEquiv` is compatible with composition** (the paper's pasted-square diagram): the
vertical morphism classifying `θ ≫ᵈᵈ θ'` is the evident composite of those classifying `θ` and
`θ'`. Stated in "hypothesis style": any `X` heterogeneously equal to that composite *is*
`d2sHomEquiv` of the composite. -/
theorem d2sHomEquiv_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'')
    (X : (push (α ≫ α') c) ⟶[[B.id (B.transp (α ≫ α') b)]] (pull (B.factor (g ≫ᵈ g')) c''))
    (hX : X ≍ (pushFunctor α' (B.transp α b)).map (d2sHomEquiv α g c c' θ)
        ≫ eqToHom (push_pull α' (B.factor g) c')
        ≫ (pullFunctor (B.transpMap α' (B.factor g))).map (d2sHomEquiv α' g' c' c'' θ')) :
    X = d2sHomEquiv (α ≫ α') (g ≫ᵈ g') c c'' (θ ≫ᵈᵈ θ') := by
  -- restate `hX` with the functor applications unfolded, so that the objects appearing in the
  -- composite are syntactically the ones the `push`/`pull` lemmas produce
  have hX' : X ≍ @CategoryStruct.comp (C.Fiber (B.transp α' (B.transp α b))) _
      (push α' (push α c)) (push α' (pull (B.factor g) c'))
      (pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c''))
      (pushMap α' (d2sHomEquiv α g c c' θ))
      (@CategoryStruct.comp (C.Fiber (B.transp α' (B.transp α b))) _
        (push α' (pull (B.factor g) c'))
        (pull (B.transpMap α' (B.factor g)) (push α' c'))
        (pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c''))
        (eqToHom (push_pull α' (B.factor g) c'))
        (pullMap (B.transpMap α' (B.factor g)) (d2sHomEquiv α' g' c' c'' θ'))) := hX
  clear hX
  -- the object/base equalities relating the two bracketings
  have hbP : B.transp (α ≫ α') b = B.transp α' (B.transp α b) := B.transp_comp α α' b
  have hcP : push (α ≫ α') c ≍ push α' (push α c) := push_comp_heq α α' c
  have hgQ : B.factor (g ≫ᵈ g')
      ≍ (B.transpMap α' (B.factor g) ≫ B.factor g' : B.transp α' (B.transp α b) ⟶ b'') :=
    B.factor_comp_heq g g'
  have hgQ' : B.factor (g ≫ᵈ g') ≍ B.transpMap α' (B.factor g) ≫ᵈ B.factor g' := by
    refine hgQ.trans ?_
    rw [Displayed.Fiber.comp_def]
    exact B.castHom_heq _ _
  have hcQ : pull (B.factor (g ≫ᵈ g')) c''
      ≍ pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c'') :=
    pull_factor_comp_heq α α' g g' c''
  have hlQ : pullLift (B.factor (g ≫ᵈ g')) c''
      ≍ pullLift (B.transpMap α' (B.factor g)) (pull (B.factor g') c'')
        ≫ᵈᵈ pullLift (B.factor g') c'' :=
    (pullLift_congr_dom hbP hgQ c'').trans
      (pullLift_comp_heq (B.transpMap α' (B.factor g)) (B.factor g') c'')
  have hgfac : ∀ {x : A} {y : A} (u : x ⟶ y) {p : B.Ob x} {q : B.Ob y} (v : p ⟶[u] q),
      v ≍ B.olift u p ≫ᵈ (B.id (B.transp u p) ≫ᵈ B.factor v) := by
    intro x y u p q v
    exact (olift_factor_heq u v).trans
      (B.heq_comp rfl (by simp) rfl rfl rfl HEq.rfl (B.id_comp_heq (B.factor v)).symm)
  -- the three `eqToHom`-conjugation steps
  have hL0 : totC (B.olift (α ≫ α') b) (pushLift (α ≫ α') c) ≫ eqToHom (sigmaTotEq hbP hcP)
      = totC (B.olift α b) (pushLift α c)
        ≫ totC (B.olift α' (B.transp α b)) (pushLift α' (push α c)) := by
    rw [totC_comp, totC_heq_conj (θ₂ := pushLift α c ≫ᵈᵈ pushLift α' (push α c))
      rfl HEq.rfl hbP hcP rfl (B.olift_comp_heq α α' b) (pushLift_comp_heq α α' c)]
    simp
  have hL2 : eqToHom (sigmaTotEq hbP hcQ).symm
        ≫ totC (B.factor (g ≫ᵈ g')) (pullLift (B.factor (g ≫ᵈ g')) c'')
      = totC (B.transpMap α' (B.factor g))
            (pullLift (B.transpMap α' (B.factor g)) (pull (B.factor g') c''))
        ≫ totC (B.factor g') (pullLift (B.factor g') c'') := by
    rw [totC_comp, totC_heq_conj hbP hcQ rfl HEq.rfl (by simp) hgQ' hlQ]
    simp
  have hXeq := totC_heq_conj hbP hcP hbP hcQ rfl (by rw [hbP] : B.id (B.transp (α ≫ α') b)
      ≍ B.id (B.transp α' (B.transp α b))) hX'
  -- the six steps of the pasted square
  have hd : totC (B.olift α' (B.transp α b)) (pushLift α' (push α c))
        ≫ totC (B.id (B.transp α' (B.transp α b))) (pushMap α' (d2sHomEquiv α g c c' θ))
      = totC (B.id (B.transp α b)) (d2sHomEquiv α g c c' θ)
        ≫ totC (B.olift α' (B.transp α b)) (pushLift α' (pull (B.factor g) c')) := by
    rw [totC_comp, totC_comp]
    refine totC_eq_of_heq (by simp) ((B.comp_id_heq _).trans (B.id_comp_heq _).symm) ?_
    rw [pushLift_pushMap]
    exact C.castHom_heq _ _ _
  have hc_ : totC (B.olift α' (B.transp α b)) (pushLift α' (pull (B.factor g) c'))
        ≫ totC (B.id (B.transp α' (B.transp α b)))
            (@eqToHom (C.Fiber (B.transp α' (B.transp α b))) _ _ _
              (push_pull α' (B.factor g) c'))
      = totC (B.olift α' (B.transp α b))
          (push_pull α' (B.factor g) c' ▸ pushLift α' (pull (B.factor g) c')) := by
    rw [totC_vert_eqToHom,
      totC_heq_conj (θ := push_pull α' (B.factor g) c' ▸ pushLift α' (pull (B.factor g) c'))
        (θ₂ := pushLift α' (pull (B.factor g) c')) rfl HEq.rfl rfl
        (heq_of_eq (push_pull α' (B.factor g) c').symm) rfl HEq.rfl (eqRec_heq_self _ _)]
    simp
  have hsq : totC (B.olift α' (B.transp α b))
          (push_pull α' (B.factor g) c' ▸ pushLift α' (pull (B.factor g) c'))
        ≫ totC (B.transpMap α' (B.factor g))
            (pullLift (B.transpMap α' (B.factor g)) (push α' c'))
      = totC (B.factor g) (pullLift (B.factor g) c')
        ≫ totC (B.olift α' b') (pushLift α' c') := by
    rw [totC_comp, totC_comp]
    exact (totC_eq_of_heq (by simp) (B.olift_transpMap_heq α' (B.factor g)).symm
      (pushLift_pullLift_square α' (B.factor g) c')).symm
  have hf_ : totC (B.id (B.transp α' (B.transp α b)))
          (pullMap (B.transpMap α' (B.factor g)) (d2sHomEquiv α' g' c' c'' θ'))
        ≫ totC (B.transpMap α' (B.factor g))
            (pullLift (B.transpMap α' (B.factor g)) (pull (B.factor g') c''))
      = totC (B.transpMap α' (B.factor g))
            (pullLift (B.transpMap α' (B.factor g)) (push α' c'))
        ≫ totC (B.id (B.transp α' b')) (d2sHomEquiv α' g' c' c'' θ') := by
    rw [totC_comp, totC_comp]
    refine totC_eq_of_heq (by simp) ((B.id_comp_heq _).trans (B.comp_id_heq _).symm) ?_
    rw [pullMap_pullLift]
    exact C.castHom_heq _ _ _
  have ha : totC (B.olift α b) (pushLift α c)
        ≫ totC (B.id (B.transp α b)) (d2sHomEquiv α g c c' θ)
        ≫ totC (B.factor g) (pullLift (B.factor g) c')
      = totC g θ := by
    rw [totC_comp, totC_comp]
    exact totC_eq_of_heq (by simp) (hgfac α g).symm (d2sHomEquiv_heq α g c c' θ)
  have hb_ : totC (B.olift α' b') (pushLift α' c')
        ≫ totC (B.id (B.transp α' b')) (d2sHomEquiv α' g' c' c'' θ')
        ≫ totC (B.factor g') (pullLift (B.factor g') c'')
      = totC g' θ' := by
    rw [totC_comp, totC_comp]
    exact totC_eq_of_heq (by simp) (hgfac α' g').symm (d2sHomEquiv_heq α' g' c' c'' θ')
  -- assemble
  refine d2sHomEquiv_eq_of_heq (α ≫ α') (g ≫ᵈ g') (θ ≫ᵈᵈ θ') X ?_
  refine heq_of_totC_eq ?_
  rw [← totC_comp, ← totC_comp, ← totC_comp, hXeq, ← totC_vert_comp, ← totC_vert_comp]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hL0]
  slice_lhs 6 7 => rw [hL2]
  slice_lhs 2 3 => rw [hd]
  slice_lhs 3 4 => rw [hc_]
  slice_lhs 4 5 => rw [hf_]
  slice_lhs 3 4 => rw [hsq]
  slice_lhs 1 3 => rw [ha]
  slice_lhs 2 4 => rw [hb_]


omit [SplitOpfib B] [D2SFib C] in
/-- A `totC` whose data is heterogeneously an identity is an `eqToHom`. -/
theorem totC_eq_eqToHom {b b₂ : B.Ob a} {c : C.Ob b} {c₂ : C.Ob b₂} {g : b ⟶[𝟙 a] b₂}
    {θ : c ⟶[[g]] c₂} (hb : b = b₂) (hc : c ≍ c₂) (hg : g ≍ B.id b) (hθ : θ ≍ C.id c) :
    totC g θ = eqToHom (sigmaTotEq hb hc) := by
  subst hb; obtain rfl := eq_of_heq hc; obtain rfl := eq_of_heq hg; obtain rfl := eq_of_heq hθ
  rfl

omit [SplitOpfib B] [D2SFib C] in
/-- The displayed identity, viewed in `(C.sigma).Total`, is the identity. -/
@[simp] theorem totC_id {b : B.Ob a} (c : C.Ob b) :
    totC (B.id b) (C.id c) = 𝟙 ((C.sigma).tot (⟨b, c⟩ : (C.sigma).Ob a)) := rfl

/-- The chosen cartesian lift along an `eqToHom` is heterogeneously an identity. -/
theorem pullLift_eqToHom {b b' : B.Fiber a} (h : b = b') (c : C.Ob b') :
    pullLift (eqToHom h) c ≍ C.id c := by
  subst h
  exact pullLift_id_heq c

/-- Two objects of the same fiber of `C` that are both heterogeneously `c` are equal. -/
theorem pull_factor_olift_eq (α : a ⟶ a') (b : B.Ob a) (c : C.Ob b) :
    push α c = pull (B.factor (B.olift α b)) (push α c) := by
  rw [B.factor_olift]; exact (pull_id (push α c)).symm

/-- The vertical factorization of a chosen opcartesian lift is the identity. -/
theorem factor_olift_eq_id (α : a ⟶ a') (b : B.Ob a) :
    B.factor (B.olift α b) = B.id (B.transp α b) := by
  rw [B.factor_olift]; rfl

/-- `d2sHomEquiv` of a chosen opcartesian lift is the canonical `eqToHom`. -/
theorem d2sHomEquiv_pushLift (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) :
    d2sHomEquiv α (B.olift α b) c (push α c) (pushLift α c)
      = @eqToHom (C.Fiber (B.transp α b)) _ _ _ (pull_factor_olift_eq α b c) := by
  have hfo := factor_olift_eq_id (B := B) α b
  have hpo : pullLift (B.factor (B.olift α b)) (push α c)
      ≍ C.id (pull (B.factor (B.olift α b)) (push α c)) := by
    rw [hfo]
    refine (pullLift_id_heq (push α c)).trans ?_
    rw [pull_id]
  refine (d2sHomEquiv_eq_of_heq α (B.olift α b) (pushLift α c) _ ?_).symm
  refine heq_of_totC_eq ?_
  rw [← totC_comp, ← totC_comp, totC_vert_eqToHom,
    totC_eq_eqToHom (θ := pullLift (B.factor (B.olift α b)) (push α c)) rfl
      (heq_of_eq (pull_factor_olift_eq α b c).symm) (heq_of_eq hfo) hpo]
  simp


omit [SplitOpfib B] [D2SFib C] in
/-- `eqToHom` in a fiber of `B` is heterogeneously the displayed identity. -/
theorem base_eqToHom_heq {b b' : B.Fiber a} (h : b = b') : eqToHom h ≍ B.id b := by
  subst h; rfl

omit [SplitOpfib B] [D2SFib C] in
/-- `C.id` respects heterogeneous equality of objects. -/
theorem id_congr_heq {b b₂ : B.Ob a} {c : C.Ob b} {c₂ : C.Ob b₂} (hb : b = b₂) (hc : c ≍ c₂) :
    C.id c ≍ C.id c₂ := by subst hb; obtain rfl := eq_of_heq hc; rfl

/-- The two descriptions of the identity's fiber, over `B.transp (𝟙 a) b`. -/
theorem push_id_eq_pull_factor_id {b : B.Ob a} (c : C.Ob b) :
    push (𝟙 a) c = pull (B.factor (B.id b)) c := by
  refine eq_of_heq ((push_id_heq c).trans ?_)
  rw [B.factor_id]
  exact (pull_eqToHom (B.transp_id b) c).symm

/-- `d2sHomEquiv` of a displayed identity is the canonical `eqToHom`. -/
theorem d2sHomEquiv_id {b : B.Ob a} (c : C.Ob b) :
    d2sHomEquiv (𝟙 a) (B.id b) c c (C.id c)
      = @eqToHom (C.Fiber (B.transp (𝟙 a) b)) _ _ _ (push_id_eq_pull_factor_id c) := by
  have hfi : B.factor (B.id b) ≍ B.id (B.transp (𝟙 a) b) := by
    rw [B.factor_id]; exact base_eqToHom_heq _
  have hpc : pull (B.factor (B.id b)) c ≍ c := by
    rw [B.factor_id]; exact pull_eqToHom (B.transp_id b) c
  have hpl : pullLift (B.factor (B.id b)) c ≍ C.id (pull (B.factor (B.id b)) c) := by
    rw [B.factor_id]
    exact (pullLift_eqToHom (B.transp_id b) c).trans
      (id_congr_heq (B.transp_id b).symm (pull_eqToHom (B.transp_id b) c).symm)
  refine (d2sHomEquiv_eq_of_heq (𝟙 a) (B.id b) (C.id c) _ ?_).symm
  refine heq_of_totC_eq ?_
  rw [← totC_comp, ← totC_comp, totC_vert_eqToHom,
    totC_eq_eqToHom (θ := pullLift (B.factor (B.id b)) c) (B.transp_id b) hpc hfi hpl,
    totC_eq_eqToHom (θ := pushLift (𝟙 a) c) (B.transp_id b).symm (push_id_heq c).symm
      (B.olift_id_heq b) (pushLift_id_heq c)]
  simp

/-- The two descriptions of a chosen cartesian lift's fiber. -/
theorem push_id_pull_eq_pull_factor {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    push (𝟙 a) (pull β c) = pull (B.factor β) c := by
  refine eq_of_heq ((push_id_heq (pull β c)).trans ?_)
  exact (pull_congr_dom (B.transp_id b) (B.factor_vert_heq β) c).symm

/-- `d2sHomEquiv` of a chosen cartesian lift is the canonical `eqToHom`. -/
theorem d2sHomEquiv_pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    d2sHomEquiv (𝟙 a) β (pull β c) c (pullLift β c)
      = @eqToHom (C.Fiber (B.transp (𝟙 a) b)) _ _ _ (push_id_pull_eq_pull_factor β c) := by
  refine (d2sHomEquiv_eq_of_heq (𝟙 a) β (pullLift β c) _ ?_).symm
  refine heq_of_totC_eq ?_
  rw [← totC_comp, ← totC_comp, totC_vert_eqToHom,
    totC_heq_conj (θ := pullLift (B.factor β) c) (B.transp_id b)
      (pull_congr_dom (B.transp_id b) (B.factor_vert_heq β) c) rfl HEq.rfl rfl
      (B.factor_vert_heq β) (pullLift_congr_dom (B.transp_id b) (B.factor_vert_heq β) c),
    totC_eq_eqToHom (θ := pushLift (𝟙 a) (pull β c)) (B.transp_id b).symm
      (push_id_heq (pull β c)).symm (B.olift_id_heq _) (pushLift_id_heq _)]
  simp

/-- `d2sHomEquiv` reflects heterogeneous equality. -/
theorem heq_of_d2sHomEquiv_heq (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'}
    (g : b ⟶[α] b') {c₁ c₂ : C.Ob b} {c'₁ c'₂ : C.Ob b'} (hc : c₁ = c₂) (hc' : c'₁ = c'₂)
    {θ₁ : c₁ ⟶[[g]] c'₁} {θ₂ : c₂ ⟶[[g]] c'₂}
    (h : d2sHomEquiv α g c₁ c'₁ θ₁ ≍ d2sHomEquiv α g c₂ c'₂ θ₂) : θ₁ ≍ θ₂ := by
  subst hc; subst hc'
  exact heq_of_eq ((d2sHomEquiv α g _ _).injective (eq_of_heq h))

end SigmaBridge

end D2SFib

section FiberHelpers

variable {B : Displayed A}

/-- The hom-type of a fiber of `C`, as an abbreviation carrying the fiber's `Category` instance
(so that `≫` and `eqToHom` elaborate at hom-types written with `push`/`pull`). -/
abbrev fiberHom (C : DoubleDisplayed B) {a : A} (b : B.Ob a) (c c' : C.Fiber b) : Type v₃ := c ⟶ c'

/-! ### Congruence helpers for fiber categories -/

variable {C : DoubleDisplayed B} {a : A}

/-- Composition in fibers respects heterogeneous equality of the fiber index. -/
theorem fiber_comp_heq {b b₂ : B.Ob a} (hb : b = b₂) {x y z : C.Fiber b} {x₂ y₂ z₂ : C.Fiber b₂}
    (hx : x ≍ x₂) (hy : y ≍ y₂) (hz : z ≍ z₂) {u : x ⟶ y} {u₂ : x₂ ⟶ y₂} {v : y ⟶ z}
    {v₂ : y₂ ⟶ z₂} (hu : u ≍ u₂) (hv : v ≍ v₂) : u ≫ v ≍ u₂ ≫ v₂ := by
  subst hb; obtain rfl := eq_of_heq hx; obtain rfl := eq_of_heq hy; obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hu; obtain rfl := eq_of_heq hv; rfl

/-- `eqToHom`s in fibers respect heterogeneous equality of the fiber index. -/
theorem fiber_eqToHom_heq' {b b₂ : B.Ob a} (hb : b = b₂) {x y : C.Fiber b} {x₂ y₂ : C.Fiber b₂}
    (hx : x ≍ x₂) (hy : y ≍ y₂) (h : x = y) (h₂ : x₂ = y₂) :
    (eqToHom h : x ⟶ y) ≍ (eqToHom h₂ : x₂ ⟶ y₂) := by
  subst hb; obtain rfl := eq_of_heq hx; obtain rfl := eq_of_heq hy; rfl

end FiberHelpers

end Nfib
