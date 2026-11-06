import DoubleDisplayed.D2SFib.Basic
import DoubleDisplayed.Functor
import Displayed.Opfibration.OpcartesianFunctor
import Tactic.KernelTactic

/-!
# Maps of D2SFibs over an opcartesian functor

For split opfibrations `B` over `A` and `B'` over `A'`, and an opcartesian functor
`H : OpcartesianFunctor u B B'` over `u : A ⥤ A'`, a *map of D2SFibs over `H`* from a split D2SFib
`C` over `B` to a split D2SFib `C'` over `B'` is a doubly displayed functor over `H` preserving the
chosen cartesian and opcartesian lifts on the nose (`D2SFibMap H C C'`). Over the identity of `B`,
these are the morphisms of the category `D2SFibCat B` (`D2SFib/Category.lean`).

As for `D2SFib`, the preservation of the chosen pullbacks and pushforwards on objects is in a
separate structure (`D2SFibMapObj`), and is a rewrite rule, so that the preservation of the chosen
lifts compares morphisms with definitionally equal endpoints. The pullback along `β` goes to the
pullback along `H β`, and the pushforward along `α` to the pushforward along `u α`, which the rules
of `H` make well typed. Both are rules, and so is the derived preservation of `pushMap` and
`pullMap`. D2SFib maps have identities and compose, with laws by `rfl`.

A split D2SFib `C'` over `B'` reindexes along `H` to a split D2SFib `C'.reindex H` over `B`: its
chosen lifts along `β` and `α` are those of `C'` along `H β` and `u α`, and its laws are those of
`C'`, by the rules of `H`. The identity `D2SFibMap.reindexLift` from it to `C'` is a map of D2SFibs
over `H`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ v₇ u₇ v₈ u₈ v₉ u₉

namespace DoubleDisplayed

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]
  {A' : Type u₄} [Category.{v₄} A'] {B' : Displayed.{v₄, u₄, v₅, u₅} A'} [SplitOpfib B']
  {u : A ⥤ A'}

/-- A doubly displayed functor over `H` preserving the chosen pullbacks and pushforwards of
objects. -/
structure D2SFibMapObj (H : OpcartesianFunctor u B B')
    (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)
    (C' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₆, u₆} B') [SplitD2SFib C] [SplitD2SFib C'] extends
    DDFunctor H.toDispFunctor C C' where
  /-- Preserves chosen pullbacks on objects. -/
  obj_pull : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    obj (D2SFib.pull β c) = D2SFib.pull (H.toPre.map β) (obj c) := by intros; rfl
  /-- Preserves chosen pushforwards on objects. -/
  obj_push : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    obj (D2SFib.push α c) = D2SFib.push (u.map α) (obj c) := by intros; rfl

attribute [rewrite_rule] D2SFibMapObj.obj_pull D2SFibMapObj.obj_push

/-- **A map of D2SFibs over `H`**: a doubly displayed functor over `H` preserving the chosen
cartesian and opcartesian lifts strictly. -/
structure D2SFibMap (H : OpcartesianFunctor u B B')
    (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)
    (C' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₆, u₆} B') [SplitD2SFib C] [SplitD2SFib C'] where
  /-- The underlying doubly displayed functor, preserving the chosen objects. -/
  toObj : D2SFibMapObj H C C'
  /-- Preserves chosen cartesian lifts. -/
  map_pullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    toObj.map (pullLift β c) = pullLift (H.toPre.map β) (toObj.obj c) := by intros; rfl
  /-- Preserves chosen opcartesian lifts. -/
  map_pushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    toObj.map (pushLift α c) = pushLift (u.map α) (toObj.obj c) := by intros; rfl

attribute [rewrite_rule] D2SFibMap.map_pullLift D2SFibMap.map_pushLift

namespace D2SFibMap

variable {H : OpcartesianFunctor u B B'} {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
  {C' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₆, u₆} B'} [SplitD2SFib C] [SplitD2SFib C']

/-- The underlying doubly displayed functor. -/
abbrev toDDFunctor (Φ : D2SFibMap H C C') : DDFunctor H.toDispFunctor C C' := Φ.toObj.toDDFunctor

/-- D2SFib maps are determined by their underlying doubly displayed functors. -/
theorem ext {Φ Ψ : D2SFibMap H C C'} (h : Φ.toDDFunctor = Ψ.toDDFunctor) : Φ = Ψ := by
  obtain ⟨⟨Φ, _, _⟩, _, _⟩ := Φ
  obtain ⟨⟨Ψ, _, _⟩, _, _⟩ := Ψ
  obtain rfl : Φ = Ψ := h
  rfl

/-- Maps of D2SFibs over equal opcartesian functors are equal, heterogeneously, when their actions
on objects and morphisms are. -/
theorem hext {H' : OpcartesianFunctor u B B'} (hH : H = H') {Φ : D2SFibMap H C C'}
    {Ψ : D2SFibMap H' C C'}
    (hobj : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), Φ.toObj.obj c ≍ Ψ.toObj.obj c)
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {c : C.Ob b}
      {c' : C.Ob b'} (θ : c ⟶[[g]] c'), Φ.toObj.map θ ≍ Ψ.toObj.map θ) : Φ ≍ Ψ := by
  subst hH
  exact heq_of_eq (ext (DDFunctor.ext (fun c => eq_of_heq (hobj c)) hmap))

/-- The identity map of D2SFibs, over the identity opcartesian functor. -/
protected def id (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [SplitD2SFib C] :
    D2SFibMap (OpcartesianFunctor.id B) C C where
  toObj := { toDDFunctor := DDFunctor.id C }

/-- Composition of maps of D2SFibs, over the composite opcartesian functor. -/
def comp {A'' : Type u₇} [Category.{v₇} A''] {B'' : Displayed.{v₇, u₇, v₈, u₈} A''}
    [SplitOpfib B''] {u' : A' ⥤ A''} {H' : OpcartesianFunctor u' B' B''}
    {C'' : DoubleDisplayed.{v₇, u₇, v₈, u₈, v₉, u₉} B''} [SplitD2SFib C'']
    (Φ : D2SFibMap H C C') (Ψ : D2SFibMap H' C' C'') : D2SFibMap (H.comp H') C C'' where
  toObj := { toDDFunctor := Φ.toDDFunctor.comp Ψ.toDDFunctor }

variable (Φ : D2SFibMap H C C')

/-- A map of D2SFibs preserves the pushforward action on morphisms. -/
theorem map_pushMap {a a' : A} (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    Φ.toObj.map (pushMap α f) = pushMap (u.map α) (Φ.toObj.map f : Φ.toObj.obj c ⟶ _) := by
  refine DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift (u.map α) (Φ.toObj.obj c))
    (isOpcartesianPushLift _ _) ?_
  refine (congrArg Φ.toObj.map (pushLift_pushMap α f)).trans ?_
  exact (pushLift_pushMap (u.map α) (Φ.toObj.map f : Φ.toObj.obj c ⟶ _)).symm

/-- A map of D2SFibs preserves the pullback action on morphisms. -/
theorem map_pullMap {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') :
    Φ.toObj.map (pullMap β f) = pullMap (H.toPre.map β) (Φ.toObj.map f : Φ.toObj.obj c ⟶ _) := by
  refine pull_hom_ext (β := H.toPre.map β) (c := Φ.toObj.obj c') ?_
  refine (congrArg Φ.toObj.map (pullMap_pullLift β f)).trans ?_
  exact (pullMap_pullLift (H.toPre.map β) (Φ.toObj.map f : Φ.toObj.obj c ⟶ _)).symm

attribute [rewrite_rule] map_pushMap map_pullMap

end D2SFibMap

/-! ## Reindexing -/

section Reindex

variable (H : OpcartesianFunctor u B B') (C' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₆, u₆} B')
  [SplitD2SFib C']

/-- The chosen lifts of the reindexing of `C'` along `H`: those of `C'` along `H β` and `u α`. -/
instance reindexD2SFib : D2SFib (C'.reindex H.toDispFunctor) where
  pull β c := D2SFib.pull (C := C') (H.toPre.map β) c
  pullLift β c := D2SFib.pullLift (C := C') (H.toPre.map β) c
  isCartesianPullLift β c :=
    { lift := fun {_} g₀ {_} χ => (isCartesianPullLift (H.toPre.map β) c).lift (H.toPre.map g₀) χ
      lift_fac := fun {_} g₀ {_} χ =>
        (isCartesianPullLift (H.toPre.map β) c).lift_fac (H.toPre.map g₀) χ
      lift_uniq := fun {_ _ _ _} ψ h => (isCartesianPullLift (H.toPre.map β) c).lift_uniq ψ h }
  push α _ c := D2SFib.push (C := C') (u.map α) c
  pushLift α _ c := D2SFib.pushLift (C := C') (u.map α) c
  isOpcartesianPushLift α _ c :=
    { desc := fun {_ _ _} g' {_} χ => (isOpcartesianPushLift (u.map α) c).desc (H.toPre.map g') χ
      desc_fac := fun {_ _ _} g' {_} χ =>
        (isOpcartesianPushLift (u.map α) c).desc_fac (H.toPre.map g') χ
      desc_uniq := fun {_ _ _ _ _ _} ψ h => (isOpcartesianPushLift (u.map α) c).desc_uniq ψ h }

instance reindexPreSplitD2SFib : PreSplitD2SFib (C'.reindex H.toDispFunctor) := {}

/-- **The reindexing of a split D2SFib** along an opcartesian functor is a split D2SFib. -/
instance reindexSplitD2SFib : SplitD2SFib (C'.reindex H.toDispFunctor) where
  pushLift_pullLift α _ _ β c := SplitD2SFib.pushLift_pullLift (u.map α) (H.toPre.map β) c


/-- The map of D2SFibs over `H` from the reindexing of `C'` along `H` to `C'`, the identity on
objects and morphisms. -/
def D2SFibMap.reindexLift : D2SFibMap H (C'.reindex H.toDispFunctor) C' where
  toObj := { toDDFunctor := C'.reindexLift H.toDispFunctor }

/-- The factorization through `D2SFibMap.reindexLift` of a map of D2SFibs over a composite
`H₀ ⋙ H`: the same doubly displayed functor, over `H₀`, into the reindexing of `C'` along `H`. -/
def D2SFibMap.liftReindex {A₀ : Type u₇} [Category.{v₇} A₀] {B₀ : Displayed.{v₇, u₇, v₈, u₈} A₀}
    [SplitOpfib B₀] {u₀ : A₀ ⥤ A} {H₀ : OpcartesianFunctor u₀ B₀ B}
    {C₀ : DoubleDisplayed.{v₇, u₇, v₈, u₈, v₉, u₉} B₀} [SplitD2SFib C₀]
    (χ : D2SFibMap (H₀.comp H) C₀ C') : D2SFibMap H₀ C₀ (C'.reindex H.toDispFunctor) where
  toObj :=
    { obj := fun c => χ.toObj.obj c
      map := fun θ => χ.toObj.map θ
      map_id := fun c => χ.toObj.map_id c
      map_comp := fun θ θ' => χ.toObj.map_comp θ θ'
      obj_pull := fun β c => χ.toObj.obj_pull β c
      obj_push := fun α _ c => χ.toObj.obj_push α c }
  map_pullLift β c := χ.map_pullLift β c
  map_pushLift α _ c := χ.map_pushLift α c

end Reindex

end DoubleDisplayed
