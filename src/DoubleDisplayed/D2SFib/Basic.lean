import DoubleDisplayed.Cartesian
import DoubleDisplayed.Total
import Displayed.Opfibration.DualOp

/-!
# Dependent 2-sided split fibrations (`D2SFib`)

`D2SFib C` is a data-carrying class on a doubly displayed category `C : DoubleDisplayed B`
(with `B` a split opfibration over `A`). It packages, in the displayed setting:

1. a *local split fibration*: chosen cartesian lifts `pull`/`pullLift` of the vertical morphisms of
   `B`, cartesian among morphisms of the same fiber;
2.–3. a *split opfibration over `A`*: chosen opcartesian lifts `push`/`pushLift`, typed over the
   chosen lifts `B.olift` of `B` (so their compatibility is absorbed into the type of `pushLift`);
4. a strict *push/pull interchange* `push_pull`/`pushLift_pullLift`.

As for (op)fibrations of displayed categories, there are three classes: `D2SFib` (cloven) holds
the chosen lifts, `PreSplitD2SFib` adds the laws on objects (`pull_id`, `pull_comp`, `push_id`,
`push_comp`, `push_pull`), which are rewrite rules, and `SplitD2SFib` the laws on lifts, which are
then plain equations, and rules too, except for the interchange `pushLift_pullLift`.

We derive the fiberwise actions `pushMap`/`pullMap`, whose functoriality and interchange hold on the
nose (again as rewrite rules), and the two-sided hom equivalence `d2sHomEquiv`, together with its
compatibility with composition, identities and the chosen lifts.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed

open CategoryTheory Displayed DoubleDisplayed

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

/-- A dependent 2-sided fibration structure (cloven) on a doubly displayed category `C` over a
split opfibration `B`: chosen cartesian lifts along the vertical morphisms of `B`, and chosen
opcartesian lifts over the chosen lifts of `B`. -/
class D2SFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  /-- Chosen pullback along a vertical morphism `β : b ⟶ b'`. -/
  pull : {a : A} → {b b' : B.Ob a} → (β : b ⟶[𝟙 a] b') → C.Ob b' → C.Ob b
  /-- Chosen cartesian lift over `β`. -/
  pullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'), pull β c ⟶[[β]] c
  /-- The chosen pullback lifts are cartesian (among morphisms of the same fiber). -/
  isCartesianPullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    DoubleDisplayed.IsCartesian (pullLift β c)
  /-- Chosen pushforward along `α : a ⟶ a'`, over `B`'s pushforward `B.push`. -/
  push : {a a' : A} → (α : a ⟶ a') → {b : B.Ob a} → C.Ob b → C.Ob (B.push α b)
  /-- Chosen opcartesian lift over `B.olift α b`. -/
  pushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b), c ⟶[[B.olift α b]] push α c
  /-- The chosen pushforward lifts are opcartesian over `B`. -/
  isOpcartesianPushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    DoubleDisplayed.IsOpcartesian (pushLift α c)

/-- A pre-split D2SFib: the chosen pullbacks and pushforwards are strictly functorial on objects
and interchange. These axioms are rewrite rules. -/
class PreSplitD2SFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) extends D2SFib C where
  pull_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), pull (B.id b) c = c
  pull_comp : ∀ {a : A} {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    (c : C.Ob b''), pull (β ≫ᵈ γ) c = pull β (pull γ c)
  push_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), push (𝟙 a) c = c
  push_comp : ∀ {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b),
    push (α ≫ α') c = push α' (push α c)
  push_pull : ∀ {a a' : A} (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    push α (pull β c) = pull (B.pushMap α β) (push α c)

attribute [rewrite_rule] PreSplitD2SFib.pull_id PreSplitD2SFib.pull_comp PreSplitD2SFib.push_id
  PreSplitD2SFib.push_comp PreSplitD2SFib.push_pull

/-- A dependent 2-sided split fibration: a pre-split D2SFib whose chosen lifts are strictly
functorial and interchange. As for `SplitOpfib`, the pre-split structure is an instance field rather
than a parent, so that its rules apply to the axioms on lifts. -/
class SplitD2SFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  /-- The underlying pre-split D2SFib. -/
  [toPreSplitD2SFib : PreSplitD2SFib C]
  pullLift_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), D2SFib.pullLift (B.id b) c = C.id c
  pullLift_comp : ∀ {a : A} {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    (c : C.Ob b''),
    D2SFib.pullLift (β ≫ᵈ γ) c = D2SFib.pullLift β (D2SFib.pull γ c) ≫ᵈᵈ D2SFib.pullLift γ c
  pushLift_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), D2SFib.pushLift (𝟙 a) c = C.id c
  pushLift_comp : ∀ {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b),
    D2SFib.pushLift (α ≫ α') c = D2SFib.pushLift α c ≫ᵈᵈ D2SFib.pushLift α' (D2SFib.push α c)
  /-- Strict push/pull interchange on lifts: the two ways around the pull/push square agree. Its
  two sides lie over `β ≫ᵈ B.olift α b'` and `B.olift α b ≫ᵈ B.pushMap α β`, which the
  interchange rule of `B` identifies, so this is a plain equation, but not a rule. -/
  pushLift_pullLift : ∀ {a a' : A} (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    (c : C.Ob b'),
    D2SFib.pullLift β c ≫ᵈᵈ D2SFib.pushLift α c
      = D2SFib.pushLift α (D2SFib.pull β c) ≫ᵈᵈ
          D2SFib.pullLift (B.pushMap α β) (D2SFib.push α c)

attribute [instance_reducible, instance] SplitD2SFib.toPreSplitD2SFib

attribute [rewrite_rule] SplitD2SFib.pullLift_id SplitD2SFib.pullLift_comp SplitD2SFib.pushLift_id
  SplitD2SFib.pushLift_comp

namespace D2SFib

variable {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} [SplitD2SFib C]

section Interchange

variable {a a' a'' : A}

theorem pushLift_pullLift (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    pullLift β c ≫ᵈᵈ pushLift α c
      = pushLift α (pull β c) ≫ᵈᵈ pullLift (B.pushMap α β) (push α c) :=
  SplitD2SFib.pushLift_pullLift α β c

theorem pushLift_pullLift_assoc (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    {f' : a' ⟶ a''} {b'' : B.Ob a''} {g : B.push α b' ⟶[f'] b''} {e : C.Ob b''}
    (h : push α c ⟶[[g]] e) :
    pullLift β c ≫ᵈᵈ (pushLift α c ≫ᵈᵈ h)
      = pushLift α (pull β c) ≫ᵈᵈ (pullLift (B.pushMap α β) (push α c) ≫ᵈᵈ h) :=
  congrArg (· ≫ᵈᵈ h) (pushLift_pullLift α β c)

end Interchange

section PushMap

variable {a a' a'' : A}

/-- Functorial action of pushforward on vertical morphisms. -/
def pushMap (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    push α c ⟶ push α c' :=
  DoubleDisplayed.IsOpcartesian.desc (isOpcartesianPushLift α c) (B.id (B.push α b))
    (f ≫ᵈᵈ pushLift α c' :)

/-- Descent characterization of `pushMap`. -/
theorem pushLift_pushMap (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    pushLift α c ≫ᵈᵈ pushMap α f = f ≫ᵈᵈ pushLift α c' :=
  DoubleDisplayed.IsOpcartesian.desc_fac (isOpcartesianPushLift α c) (B.id (B.push α b)) _

theorem pushLift_pushMap_assoc (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c')
    {f' : a' ⟶ a''} {b'' : B.Ob a''} {g : B.push α b ⟶[f'] b''} {e : C.Ob b''}
    (h : push α c' ⟶[[g]] e) :
    pushLift α c ≫ᵈᵈ (pushMap α f ≫ᵈᵈ h) = f ≫ᵈᵈ (pushLift α c' ≫ᵈᵈ h) :=
  congrArg (· ≫ᵈᵈ h) (pushLift_pushMap α f)

/-- `pushMap` preserves identities. -/
theorem pushMap_id (α : a ⟶ a') {b : B.Ob a} (c : C.Fiber b) :
    pushMap α (𝟙ᵈᵈ c) = 𝟙ᵈᵈ (push α c) :=
  DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift α c) (isOpcartesianPushLift α c)
    (pushLift_pushMap α (𝟙ᵈᵈ c))

/-- `pushMap` preserves composition. -/
theorem pushMap_comp (α : a ⟶ a') {b : B.Ob a} {c c' c'' : C.Fiber b} (f : c ⟶ c')
    (g : c' ⟶ c'') : pushMap α (f ≫ᵈᵈ g) = pushMap α f ≫ᵈᵈ pushMap α g := by
  refine DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift α c) (isOpcartesianPushLift α c) ?_
  refine (pushLift_pushMap α (f ≫ᵈᵈ g)).trans ?_
  refine (congrArg (f ≫ᵈᵈ ·) (pushLift_pushMap α g).symm).trans ?_
  exact (pushLift_pushMap_assoc α f (pushMap α g)).symm

/-- Pushforward along the identity acts trivially. -/
theorem pushMap_idBase {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') : pushMap (𝟙 a) f = f :=
  pushLift_pushMap (𝟙 a) f

/-- Pushforward along a composite is the composite of pushforwards. -/
theorem pushMap_compBase (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {c c' : C.Fiber b}
    (f : c ⟶ c') : pushMap (α ≫ α') f = pushMap α' (pushMap α f) := by
  refine DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift (α ≫ α') c)
    (isOpcartesianPushLift (α ≫ α') c) ?_
  refine (pushLift_pushMap (α ≫ α') f).trans ?_
  refine (pushLift_pushMap_assoc α f (pushLift α' (push α c'))).symm.trans ?_
  exact congrArg (pushLift α c ≫ᵈᵈ ·) (pushLift_pushMap α' (pushMap α f)).symm

end PushMap

section PullMap

variable {a : A}

/-- The unique factorization through a chosen cartesian lift. -/
def pullDesc {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (χ : c₀ ⟶[[β₀ ≫ᵈ β]] c) : c₀ ⟶[[β₀]] (pull β c) :=
  (isCartesianPullLift β c).lift β₀ χ

theorem pullDesc_fac {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) (χ : c₀ ⟶[[β₀ ≫ᵈ β]] c) :
    pullDesc β c β₀ c₀ χ ≫ᵈᵈ pullLift β c = χ :=
  (isCartesianPullLift β c).lift_fac β₀ χ

theorem pullDesc_uniq {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : C.Ob b₀) {χ : c₀ ⟶[[β₀ ≫ᵈ β]] c}
    (ξ : c₀ ⟶[[β₀]] (pull β c)) (hξ : ξ ≫ᵈᵈ pullLift β c = χ) : ξ = pullDesc β c β₀ c₀ χ :=
  (isCartesianPullLift β c).lift_uniq ξ hξ

/-- Two maps into `pull β c` agreeing after postcomposition with `pullLift β c` are equal. -/
theorem pull_hom_ext {b b' b₀ : B.Ob a} {β : b ⟶[𝟙 a] b'} {c : C.Ob b'}
    {β₀ : b₀ ⟶[𝟙 a] b} {c₀ : C.Ob b₀} {ξ ξ' : c₀ ⟶[[β₀]] (pull β c)}
    (h : ξ ≫ᵈᵈ pullLift β c = ξ' ≫ᵈᵈ pullLift β c) : ξ = ξ' :=
  (pullDesc_uniq β c β₀ c₀ ξ rfl).trans (pullDesc_uniq β c β₀ c₀ ξ' h.symm).symm

/-- Functorial action of pullback on vertical morphisms. -/
def pullMap {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'} (f : c ⟶ c') :
    pull β c ⟶ pull β c' :=
  pullDesc β c' (B.id b) (pull β c) (pullLift β c ≫ᵈᵈ f :)

/-- Descent characterization of `pullMap`. -/
theorem pullMap_pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'} (f : c ⟶ c') :
    pullMap β f ≫ᵈᵈ pullLift β c' = pullLift β c ≫ᵈᵈ f :=
  pullDesc_fac β c' (B.id b) (pull β c) _

theorem pullMap_pullLift_assoc {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') {a' : A} {f' : a ⟶ a'} {b'' : B.Ob a'} {g : b' ⟶[f'] b''} {e : C.Ob b''}
    (h : c' ⟶[[g]] e) :
    pullMap β f ≫ᵈᵈ (pullLift β c' ≫ᵈᵈ h) = pullLift β c ≫ᵈᵈ (f ≫ᵈᵈ h) :=
  (C.assoc _ _ _).symm.trans ((congrArg (· ≫ᵈᵈ h) (pullMap_pullLift β f)).trans (C.assoc _ _ _))

/-- `pullMap` preserves identities. -/
theorem pullMap_id {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Fiber b') :
    pullMap β (𝟙ᵈᵈ c) = 𝟙ᵈᵈ (pull β c) :=
  pull_hom_ext (pullMap_pullLift β (𝟙ᵈᵈ c))

/-- `pullMap` preserves composition. -/
theorem pullMap_comp {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' c'' : C.Fiber b'}
    (f : c ⟶ c') (g : c' ⟶ c'') : pullMap β (f ≫ᵈᵈ g) = pullMap β f ≫ᵈᵈ pullMap β g := by
  refine pull_hom_ext ?_
  refine (pullMap_pullLift β (f ≫ᵈᵈ g)).trans ?_
  refine (pullMap_pullLift_assoc β f g).symm.trans ?_
  exact congrArg (pullMap β f ≫ᵈᵈ ·) (pullMap_pullLift β g).symm

/-- Pullback along the vertical identity acts trivially. -/
theorem pullMap_idBase {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') : pullMap (B.id b) f = f :=
  pullMap_pullLift (B.id b) f

/-- Pullback along a composite is the (reversed) composite of pullbacks. -/
theorem pullMap_compBase {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : C.Fiber b''} (f : c ⟶ c') : pullMap (β ≫ᵈ γ) f = pullMap β (pullMap γ f) := by
  refine pull_hom_ext (β := β ≫ᵈ γ) (c := c') ?_
  refine (pullMap_pullLift (β ≫ᵈ γ) f).trans ?_
  refine (congrArg (pullLift β (pull γ c) ≫ᵈᵈ ·) (pullMap_pullLift γ f).symm).trans ?_
  exact (pullMap_pullLift_assoc β (pullMap γ f) (pullLift γ c')).symm

end PullMap

section Interchange

variable {a a' : A}

/-- The push/pull interchange on morphisms. -/
theorem pushMap_pullMap (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') : pushMap α (pullMap β f) = pullMap (B.pushMap α β) (pushMap α f) := by
  refine pull_hom_ext (β := B.pushMap α β) (c := push α c') ?_
  refine DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift α (pull β c))
    (isOpcartesianPushLift α _) ?_
  refine (pushLift_pushMap_assoc α (pullMap β f)
    (pullLift (B.pushMap α β) (push α c'))).trans ?_
  refine (congrArg (pullMap β f ≫ᵈᵈ ·) (pushLift_pullLift α β c').symm).trans ?_
  refine (pullMap_pullLift_assoc β f (pushLift α c')).trans ?_
  refine (congrArg (pullLift β c ≫ᵈᵈ ·) (pushLift_pushMap α f).symm).trans ?_
  refine (pushLift_pullLift_assoc α β c (pushMap α f)).trans ?_
  exact congrArg (pushLift α (pull β c) ≫ᵈᵈ ·)
    (pullMap_pullLift (B.pushMap α β) (pushMap α f)).symm

end Interchange

attribute [rewrite_rule] pushMap_id pushMap_comp pushMap_idBase pushMap_compBase pullMap_id
  pullMap_comp pullMap_idBase pullMap_compBase pushMap_pullMap

section Functors

variable {a a' : A}

/-- The pushforward functor on fibers. -/
def pushFunctor (α : a ⟶ a') (b : B.Ob a) :
    C.Fiber b ⥤ C.Fiber (B.push α b) where
  obj c := push α c
  map f := pushMap α f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem pushFunctor_obj (α : a ⟶ a') (b : B.Ob a) (c : C.Fiber b) :
    (pushFunctor α b).obj c = push α c := rfl

@[simp] theorem pushFunctor_map (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    (pushFunctor α b).map f = pushMap α f := rfl

/-- The pullback functor on fibers. -/
def pullFunctor {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') : C.Fiber b' ⥤ C.Fiber b where
  obj c := pull β c
  map f := pullMap β f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem pullFunctor_obj {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Fiber b') :
    (pullFunctor β).obj c = pull β c := rfl

@[simp] theorem pullFunctor_map {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') : (pullFunctor β).map f = pullMap β f := rfl

theorem pullFunctor_id {b : B.Ob a} : pullFunctor (C := C) (B.id b) = 𝟭 (C.Fiber b) := rfl

theorem pushFunctor_id (b : B.Ob a) : pushFunctor (C := C) (𝟙 a) b = 𝟭 (C.Fiber b) := rfl

end Functors

section TotalBridge

/-! Equations between morphisms of `C` lying over `B`-morphisms that are equal, but not
recognizably so by the rewrite rules, are computed in the total category of `C.total`: there a
morphism carries its `B`-base as data, and composites are compared factor by factor. -/

variable {a a' : A}

/-- A morphism of `C`, viewed as a morphism of the total category of `C.total`. -/
def totC {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') {c : C.Ob b} {c' : C.Ob b'}
    (θ : c ⟶[[g]] c') :
    C.total.tot (⟨b, c⟩ : C.total.Ob a) ⟶ C.total.tot (⟨b', c'⟩ : C.total.Ob a') :=
  C.total.totalMk α ⟨g, θ⟩

omit [SplitOpfib B] [SplitD2SFib C] in
theorem totC_comp {a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    totC g θ ≫ totC g' θ' = totC (g ≫ᵈ g') (θ ≫ᵈᵈ θ') := rfl

omit [SplitOpfib B] [SplitD2SFib C] in
theorem totC_injective {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'} {c : C.Ob b}
    {c' : C.Ob b'} {θ θ₂ : c ⟶[[g]] c'} (h : totC g θ = totC g θ₂) : θ = θ₂ := by
  unfold totC totalMk at h
  injection h with _ h'
  injection h' with _ h''

end TotalBridge

section HomEquiv

variable {a a' a'' : A}

/-- **The two-sided hom equivalence** `hom(α_! c, β^* c') ≅ hom(c, c')`: morphisms of
`C` over `g : B.Hom α b b'` correspond to *vertical* morphisms
`push α c ⟶ pull (B.opcartesianFactor g) c'` in the fiber over `B.push α b`. Its inverse composes
with the two chosen lifts. -/
def d2sHomEquiv (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : C.Ob b) (c' : C.Ob b') : (c ⟶[[g]] c') ≃ (push α c ⟶ pull (B.opcartesianFactor g) c') where
  toFun θ := pullDesc (B.opcartesianFactor g) c' (B.id (B.push α b)) (push α c)
    (DoubleDisplayed.IsOpcartesian.desc (isOpcartesianPushLift α c) (B.opcartesianFactor g) θ)
  invFun f := pushLift α c ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.opcartesianFactor g) c')
  left_inv θ :=
    (congrArg (pushLift α c ≫ᵈᵈ ·) (pullDesc_fac (B.opcartesianFactor g) c' (B.id (B.push α b))
      (push α c) _)).trans
      (DoubleDisplayed.IsOpcartesian.desc_fac (isOpcartesianPushLift α c) (B.opcartesianFactor g) θ)
  right_inv f := by
    have h : DoubleDisplayed.IsOpcartesian.desc (isOpcartesianPushLift α c) (B.opcartesianFactor g)
        (pushLift α c ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.opcartesianFactor g) c')) =
          f ≫ᵈᵈ pullLift (B.opcartesianFactor g) c' :=
      (DoubleDisplayed.IsOpcartesian.desc_uniq (isOpcartesianPushLift α c) _ rfl).symm
    exact (congrArg (pullDesc (B.opcartesianFactor g) c' (B.id (B.push α b)) (push α c)) h).trans
      (pullDesc_uniq _ _ _ _ f rfl).symm

theorem d2sHomEquiv_symm_apply (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : C.Ob b) (c' : C.Ob b') (f : push α c ⟶ pull (B.opcartesianFactor g) c') :
    (d2sHomEquiv α g c c').symm f =
      pushLift α c ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.opcartesianFactor g) c') := rfl

/-! The following lemmas state the pieces of `d2sHomEquiv_comp` in the total category of
`C.total`, for arbitrary base morphisms. Proving them for variables is cheap, and their instances at
composites need not be rechecked. -/

theorem totC_symm (α : a ⟶ a') {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') (c : C.Ob b)
    (c' : C.Ob b') (f : push α c ⟶ pull (B.opcartesianFactor g) c') :
    totC g ((d2sHomEquiv α g c c').symm f)
      = totC (B.olift α b) (pushLift α c)
        ≫ (totC (B.id _) f
          ≫ totC (B.opcartesianFactor g) (pullLift (B.opcartesianFactor g) c')) := rfl

theorem totC_eq_symm {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b') {c : C.Ob b}
    {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    totC g θ = totC (B.olift α b) (pushLift α c)
      ≫ (totC (B.id _) (d2sHomEquiv α g c c' θ)
        ≫ totC (B.opcartesianFactor g) (pullLift (B.opcartesianFactor g) c')) :=
  (congrArg (totC g) ((d2sHomEquiv α g c c').symm_apply_apply θ)).symm.trans (totC_symm _ _ _ _ _)

theorem totC_pushLift_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : C.Ob b) :
    totC (B.olift (α ≫ α') b) (pushLift (α ≫ α') c)
      = totC (B.olift α b) (pushLift α c) ≫ totC (B.olift α' _) (pushLift α' (push α c)) := rfl

omit [SplitOpfib B] [SplitD2SFib C] in
theorem totC_vert_comp {b : B.Ob a} {c c' c'' : C.Fiber b} (f : c ⟶ c') (f' : c' ⟶ c'') :
    totC (B.id b) (f ≫ f') = totC (B.id b) f ≫ totC (B.id b) f' := rfl

theorem totC_pullLift_factor_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') (c'' : C.Ob b'') :
    totC (B.opcartesianFactor (g ≫ᵈ g')) (pullLift (B.opcartesianFactor (g ≫ᵈ g')) c'')
      = totC (B.pushMap α' (B.opcartesianFactor g))
          (pullLift (B.pushMap α' (B.opcartesianFactor g)) (pull (B.opcartesianFactor g') c''))
        ≫ totC (B.opcartesianFactor g') (pullLift (B.opcartesianFactor g') c'') := rfl

theorem totC_pushLift_pushMap (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    totC (B.olift α b) (pushLift α c) ≫ totC (B.id _) (pushMap α f)
      = totC (B.id b) f ≫ totC (B.olift α b) (pushLift α c') := by
  rw [totC_comp, totC_comp]
  exact congrArg (totC _) (pushLift_pushMap α f)

theorem totC_pushLift_pushMap_assoc (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c')
    {z : C.total.Total} (h : C.total.tot (⟨_, push α c'⟩ : C.total.Ob a') ⟶ z) :
    totC (B.olift α b) (pushLift α c) ≫ (totC (B.id _) (pushMap α f) ≫ h)
      = totC (B.id b) f ≫ (totC (B.olift α b) (pushLift α c') ≫ h) := by
  rw [← Category.assoc, totC_pushLift_pushMap, Category.assoc]

theorem totC_pullMap_pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') :
    totC (B.id _) (pullMap β f) ≫ totC β (pullLift β c')
      = totC β (pullLift β c) ≫ totC (B.id b') f := by
  rw [totC_comp, totC_comp]
  exact congrArg (totC _) (pullMap_pullLift β f)

theorem totC_pullMap_pullLift_assoc {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') {z : C.total.Total} (h : C.total.tot (⟨b', c'⟩ : C.total.Ob a) ⟶ z) :
    totC (B.id _) (pullMap β f) ≫ (totC β (pullLift β c') ≫ h)
      = totC β (pullLift β c) ≫ (totC (B.id b') f ≫ h) := by
  rw [← Category.assoc, totC_pullMap_pullLift, Category.assoc]

theorem totC_pushLift_pullLift (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    totC (B.olift α b) (pushLift α (pull β c))
        ≫ totC (B.pushMap α β) (pullLift (B.pushMap α β) (push α c))
      = totC β (pullLift β c) ≫ totC (B.olift α b') (pushLift α c) := by
  rw [totC_comp, totC_comp]
  exact congrArg (totC _) (pushLift_pullLift α β c).symm

theorem totC_pushLift_pullLift_assoc (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    (c : C.Ob b') {z : C.total.Total} (h : C.total.tot (⟨_, push α c⟩ : C.total.Ob a') ⟶ z) :
    totC (B.olift α b) (pushLift α (pull β c))
        ≫ (totC (B.pushMap α β) (pullLift (B.pushMap α β) (push α c)) ≫ h)
      = totC β (pullLift β c) ≫ (totC (B.olift α b') (pushLift α c) ≫ h) := by
  rw [← Category.assoc, totC_pushLift_pullLift, Category.assoc]

/-- **`d2sHomEquiv` is compatible with composition**: the
vertical morphism classifying `θ ≫ᵈᵈ θ'` is the evident composite of those classifying `θ` and
`θ'`. -/
theorem d2sHomEquiv_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    d2sHomEquiv (α ≫ α') (g ≫ᵈ g') c c'' (θ ≫ᵈᵈ θ')
      = pushMap α' (d2sHomEquiv α g c c' θ)
          ≫ pullMap (B.pushMap α' (B.opcartesianFactor g)) (d2sHomEquiv α' g' c' c'' θ') := by
  refine ((Equiv.symm_apply_eq (d2sHomEquiv (α ≫ α') (g ≫ᵈ g') c c'')).mp ?_).symm
  apply totC_injective
  rw [totC_symm, totC_pushLift_comp, totC_vert_comp, totC_pullLift_factor_comp, ← totC_comp g g',
    totC_eq_symm g θ, totC_eq_symm g' θ']
  let u := d2sHomEquiv α g c c' θ
  let v := d2sHomEquiv α' g' c' c'' θ'
  let t := B.pushMap α' (B.opcartesianFactor g)
  let k := B.opcartesianFactor g
  let k' := B.opcartesianFactor g'
  calc _ = totC (B.olift α b) (pushLift α c) ≫ (totC (B.olift α' _) (pushLift α' (push α c))
          ≫ (totC (B.id _) (pushMap α' u) ≫ (totC (B.id _) (pullMap t v)
          ≫ (totC t (pullLift t (pull k' c''))
          ≫ totC k' (pullLift k' c''))))) := rfl
    _ = totC (B.olift α b) (pushLift α c) ≫ (totC (B.olift α' _) (pushLift α' (push α c))
          ≫ (totC (B.id _) (pushMap α' u) ≫ (totC t (pullLift t (push α' c'))
          ≫ (totC (B.id _) v ≫ totC k' (pullLift k' c''))))) :=
          congrArg (fun k => totC (B.olift α b) (pushLift α c) ≫
            (totC (B.olift α' _) (pushLift α' (push α c)) ≫ (totC (B.id _) (pushMap α' u) ≫ k)))
            (totC_pullMap_pullLift_assoc t v (totC k' (pullLift k' c'')))
    _ = totC (B.olift α b) (pushLift α c) ≫ (totC (B.id _) u
          ≫ (totC (B.olift α' _) (pushLift α' (pull k c'))
          ≫ (totC t (pullLift t (push α' c'))
          ≫ (totC (B.id _) v ≫ totC k' (pullLift k' c''))))) :=
          congrArg (totC (B.olift α b) (pushLift α c) ≫ ·)
            (totC_pushLift_pushMap_assoc α' u (totC t (pullLift t (push α' c'))
              ≫ (totC (B.id _) v ≫ totC k' (pullLift k' c''))))
    _ = totC (B.olift α b) (pushLift α c) ≫ (totC (B.id _) u
          ≫ (totC k (pullLift k c') ≫ (totC (B.olift α' b') (pushLift α' c')
          ≫ (totC (B.id _) v ≫ totC k' (pullLift k' c''))))) :=
          congrArg (fun k => totC (B.olift α b) (pushLift α c) ≫ (totC (B.id _) u ≫ k))
            (totC_pushLift_pullLift_assoc α' k c'
              (totC (B.id _) v ≫ totC k' (pullLift k' c'')))
    _ = _ := rfl

/-- `d2sHomEquiv` of a chosen opcartesian lift is the identity. -/
theorem d2sHomEquiv_pushLift (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) :
    d2sHomEquiv α (B.olift α b) c (push α c) (pushLift α c) = 𝟙ᵈᵈ (push α c) :=
  ((d2sHomEquiv α (B.olift α b) c (push α c)).symm_apply_eq (x := 𝟙ᵈᵈ (push α c))
    (y := pushLift α c)).mp rfl |>.symm

/-- `d2sHomEquiv` of a displayed identity is the identity. -/
theorem d2sHomEquiv_id {b : B.Ob a} (c : C.Ob b) :
    d2sHomEquiv (𝟙 a) (B.id b) c c (C.id c) = 𝟙ᵈᵈ c :=
  ((d2sHomEquiv (𝟙 a) (B.id b) c c).symm_apply_eq (x := 𝟙ᵈᵈ c) (y := C.id c)).mp rfl |>.symm

/-- `d2sHomEquiv` of a chosen cartesian lift is the identity. -/
theorem d2sHomEquiv_pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    d2sHomEquiv (𝟙 a) β (pull β c) c (pullLift β c) = 𝟙ᵈᵈ (pull β c) :=
  ((d2sHomEquiv (𝟙 a) β (pull β c) c).symm_apply_eq (x := 𝟙ᵈᵈ (pull β c))
    (y := pullLift β c)).mp rfl |>.symm

end HomEquiv

end D2SFib

end DoubleDisplayed
