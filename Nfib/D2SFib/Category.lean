import Nfib.D2SFib.Basic

/-!
# The category of dependent 2-sided split fibrations

We define the morphisms of D2SFibs — vertical functors preserving the chosen pull/push data on the
nose (`D2SFibHom`) — and bundle D2SFibs into the category `D2SFibCat B`, the displayed adaptation
of the paper's `D2SFib(A, B)`.

As for `D2SFib`, the preservation of chosen pullbacks and pushforwards on objects lives in a
separate structure `D2SFibHomObj`, and is a rewrite rule, so that the preservation of the chosen
lifts
compares morphisms with definitionally equal endpoints. Both are rewrite rules, and so is the
derived preservation of `pushMap`/`pullMap`.

This is part of milestone **M5** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

/-- A vertical functor preserving the chosen pullbacks and pushforwards of objects. -/
structure D2SFibHomObj (C C' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]
    [D2SFib C'] extends DoubleDisplayed.VertFunctor C C' where
  /-- Preserves chosen pullbacks on objects. It is stated with the fields of the cleavages, which
the chosen pullbacks `pull β c` unfold to, so that the rule matches both. -/
  obj_pull : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    obj ((D2SFib.cleavage (C := C)).pull β c) = (D2SFib.cleavage (C := C')).pull β (obj c)
  /-- Preserves chosen pushforwards on objects. -/
  obj_push : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    obj ((D2SFib.cleavage (C := C)).push α c) = (D2SFib.cleavage (C := C')).push α (obj c)

attribute [rewrite_rule] D2SFibHomObj.obj_pull D2SFibHomObj.obj_push

/-- A morphism of D2SFibs: a vertical functor over `B` preserving the chosen cartesian and
opcartesian lifts strictly. -/
structure D2SFibHom (C C' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]
    [D2SFib C'] where
  /-- The underlying vertical functor, preserving the chosen objects. -/
  toObj : D2SFibHomObj C C'
  /-- Preserves chosen cartesian lifts. -/
  map_pullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    toObj.map (pullLift β c) = pullLift β (toObj.obj c)
  /-- Preserves chosen opcartesian lifts. -/
  map_pushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    toObj.map (pushLift α c) = pushLift α (toObj.obj c)

attribute [rewrite_rule] D2SFibHom.map_pullLift D2SFibHom.map_pushLift

namespace D2SFibHom

variable {C C' C'' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} [D2SFib C] [D2SFib C']
  [D2SFib C'']

/-- The underlying vertical functor. -/
abbrev toVertFunctor (Φ : D2SFibHom C C') : VertFunctor C C' := Φ.toObj.toVertFunctor

/-- Extensionality: a `D2SFibHom` is determined by its underlying vertical functor. -/
theorem ext {F G : D2SFibHom C C'} (h : F.toVertFunctor = G.toVertFunctor) : F = G := by
  obtain ⟨⟨F, _, _⟩, _, _⟩ := F
  obtain ⟨⟨G, _, _⟩, _, _⟩ := G
  obtain rfl : F = G := h
  rfl

/-- The identity D2SFib morphism. -/
def id (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C] : D2SFibHom C C where
  toObj := { toVertFunctor := VertFunctor.id C, obj_pull := by intros; rfl,
             obj_push := by intros; rfl }
  map_pullLift _ _ := rfl
  map_pushLift := by intros; rfl

/-- Composition of D2SFib morphisms. -/
def comp (F : D2SFibHom C C') (G : D2SFibHom C' C'') : D2SFibHom C C'' where
  toObj := { toVertFunctor := F.toVertFunctor.comp G.toVertFunctor,
             obj_pull := by intros; rfl, obj_push := by intros; rfl }
  map_pullLift _ _ := rfl
  map_pushLift := by intros; rfl

@[simp] theorem id_toVertFunctor (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C] :
    (D2SFibHom.id C).toVertFunctor = VertFunctor.id C := rfl

@[simp] theorem comp_toVertFunctor (F : D2SFibHom C C') (G : D2SFibHom C' C'') :
    (F.comp G).toVertFunctor = F.toVertFunctor.comp G.toVertFunctor := rfl

variable (Φ : D2SFibHom C C')

/-- A D2SFib morphism preserves the pushforward action on morphisms. -/
theorem map_pushMap {a a' : A} (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b} (f : c ⟶ c') :
    Φ.toObj.map (pushMap α f) = pushMap α (Φ.toObj.map f) := by
  refine DoubleDisplayed.IsOpcartesian.hom_ext (θ := pushLift α (Φ.toObj.obj c))
    (pushLift_opcartesian α _) ?_
  refine (congrArg Φ.toObj.map (pushLift_pushMap α f)).trans ?_
  exact (pushLift_pushMap α (Φ.toObj.map f)).symm

/-- A D2SFib morphism preserves the pullback action on morphisms. -/
theorem map_pullMap {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : C.Fiber b'}
    (f : c ⟶ c') : Φ.toObj.map (pullMap β f) = pullMap β (Φ.toObj.map f) := by
  refine pull_hom_ext (β := β) (c := Φ.toObj.obj c') ?_
  refine (congrArg Φ.toObj.map (pullMap_pullLift β f)).trans ?_
  exact (pullMap_pullLift β (Φ.toObj.map f)).symm

attribute [rewrite_rule] map_pushMap map_pullMap

/-- On fibers, `Φ` commutes with the pushforward functor on the nose. -/
theorem fiber_pushFunctor {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    pushFunctor (C := C) α b ⋙ Φ.toVertFunctor.fiber (B.transp α b)
      = Φ.toVertFunctor.fiber b ⋙ pushFunctor (C := C') α b := rfl

/-- On fibers, `Φ` commutes with the pullback functor on the nose. -/
theorem fiber_pullFunctor {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    pullFunctor (C := C) β ⋙ Φ.toVertFunctor.fiber b
      = Φ.toVertFunctor.fiber b' ⋙ pullFunctor (C := C') β := rfl

/-- `d2sHomEquiv` is natural in the D2SFib: its inverse commutes with `Φ`. -/
theorem map_d2sHomEquiv_symm {a a' : A} {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'}
    {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (f : push α c ⟶ pull (B.factor g) c') :
    Φ.toObj.map ((d2sHomEquiv α g c c').symm f)
      = (d2sHomEquiv α g (Φ.toObj.obj c) (Φ.toObj.obj c')).symm (Φ.toObj.map f) := rfl

end D2SFibHom

/-- Bundled D2SFibs: the objects of the category `D2SFib(A, B)`. -/
structure D2SFibCat (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] where
  /-- The underlying doubly displayed category. -/
  C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B
  /-- Its D2SFib structure. -/
  [str : D2SFib C]

attribute [instance] D2SFibCat.str

/-- The category structure on bundled D2SFibs. -/
instance : Category (D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  Hom E E' := D2SFibHom E.C E'.C
  id E := D2SFibHom.id E.C
  comp F G := F.comp G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end Nfib
