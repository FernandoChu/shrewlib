import Nfib.D2SFib.Basic

/-!
# The category of dependent 2-sided split fibrations

We define the morphisms of D2SFibs — vertical functors preserving the chosen pull/push data on the
nose (`D2SFibHom`) — and bundle D2SFibs into the category `D2SFibCat B`, the displayed adaptation
of the paper's `D2SFib(A, B)`.

This is part of milestone **M5** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A} [SplitOpfib B]

/-- A morphism of D2SFibs: a vertical functor over `B` preserving the chosen cartesian and
opcartesian lifts strictly. -/
structure D2SFibHom (C C' : DoubleDisplayed B) [D2SFib C] [D2SFib C'] extends
    DoubleDisplayed.VertFunctor C C' where
  /-- Preserves chosen pullbacks on objects. -/
  obj_pull : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    obj (pull β c) = pull β (obj c)
  /-- Preserves chosen cartesian lifts. -/
  map_pullLift : ∀ {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b'),
    map (pullLift β c) ≍ pullLift β (obj c)
  /-- Preserves chosen pushforwards on objects. -/
  obj_push : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    obj (push α c) = push α (obj c)
  /-- Preserves chosen opcartesian lifts. -/
  map_pushLift : ∀ {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    map (pushLift α c) ≍ pushLift α (obj c)

namespace D2SFibHom

variable {C C' C'' : DoubleDisplayed B} [D2SFib C] [D2SFib C'] [D2SFib C'']

/-- Extensionality: a `D2SFibHom` is determined by its underlying vertical functor. -/
theorem ext {F G : D2SFibHom C C'} (h : F.toVertFunctor = G.toVertFunctor) : F = G := by
  cases F; cases G; cases h; rfl

/-- The identity D2SFib morphism. -/
def id (C : DoubleDisplayed B) [D2SFib C] : D2SFibHom C C where
  toVertFunctor := VertFunctor.id C
  obj_pull β c := rfl
  map_pullLift β c := HEq.rfl
  obj_push := by intro a a' α b c; rfl
  map_pushLift := by intro a a' α b c; exact HEq.rfl

/-- Composition of D2SFib morphisms. -/
def comp (F : D2SFibHom C C') (G : D2SFibHom C' C'') : D2SFibHom C C'' where
  toVertFunctor := F.toVertFunctor.comp G.toVertFunctor
  obj_pull β c := by
    change G.obj (F.obj (pull β c)) = pull β (G.obj (F.obj c))
    rw [F.obj_pull, G.obj_pull]
  map_pullLift β c := by
    change G.map (F.map (pullLift β c)) ≍ pullLift β (G.obj (F.obj c))
    refine (G.toVertFunctor.map_heq rfl rfl rfl HEq.rfl (heq_of_eq (F.obj_pull β c)) HEq.rfl
      (F.map_pullLift β c)).trans (G.map_pullLift β (F.obj c))
  obj_push := by
    intro a a' α b c
    change G.obj (F.obj (push α c)) = push α (G.obj (F.obj c))
    rw [F.obj_push, G.obj_push]
  map_pushLift := by
    intro a a' α b c
    change G.map (F.map (pushLift α c)) ≍ pushLift α (G.obj (F.obj c))
    refine (G.toVertFunctor.map_heq rfl rfl rfl HEq.rfl HEq.rfl (heq_of_eq (F.obj_push α c))
      (F.map_pushLift α c)).trans (G.map_pushLift α (F.obj c))

@[simp] theorem id_toVertFunctor (C : DoubleDisplayed B) [D2SFib C] :
    (D2SFibHom.id C).toVertFunctor = VertFunctor.id C := rfl

@[simp] theorem comp_toVertFunctor (F : D2SFibHom C C') (G : D2SFibHom C' C'') :
    (F.comp G).toVertFunctor = F.toVertFunctor.comp G.toVertFunctor := rfl

/-- A D2SFib morphism preserves the pushforward action on morphisms (heterogeneously). -/
theorem map_pushMap (Φ : D2SFibHom C C') {a a' : A} (α : a ⟶ a') {b : B.Ob a} {c c' : C.Fiber b}
    (f : c ⟶ c') : Φ.map (pushMap α f) ≍ pushMap α (Φ.map f) := by
  have hθ₂ : ((Φ.obj_push α c).symm ▸ pushLift α (Φ.obj c)) ≍ pushLift α (Φ.obj c) :=
    eqRec_heq_self _ _
  have hL : ((Φ.obj_push α c).symm ▸ pushLift α (Φ.obj c)) ≫ᵈᵈ Φ.map (pushMap α f)
      ≍ Φ.map f ≫ᵈᵈ pushLift α (Φ.obj c') := by
    refine (C'.heq_comp_left rfl rfl HEq.rfl HEq.rfl
      (hθ₂.trans (Φ.map_pushLift α c).symm)).trans ?_
    refine (heq_of_eq (Φ.toVertFunctor.map_comp (pushLift α c) (pushMap α f))).symm.trans ?_
    refine (heq_of_eq (congrArg Φ.map (pushLift_pushMap α f))).trans ?_
    refine (Φ.toVertFunctor.map_heq rfl rfl (by simp)
      ((B.comp_id_heq (B.olift α b)).trans (B.id_comp_heq (B.olift α b)).symm) HEq.rfl HEq.rfl
      (C.castHom_heq _ _ _)).trans ?_
    refine (heq_of_eq (Φ.toVertFunctor.map_comp f (pushLift α c'))).trans ?_
    exact C'.heq_comp_right rfl rfl HEq.rfl (heq_of_eq (Φ.obj_push α c')) (Φ.map_pushLift α c')
  have hR : pushLift α (Φ.obj c) ≫ᵈᵈ pushMap α (Φ.map f) ≍ Φ.map f ≫ᵈᵈ pushLift α (Φ.obj c') :=
    (heq_of_eq (pushLift_pushMap α (Φ.map f))).trans (C'.castHom_heq _ _ _)
  exact (DoubleDisplayed.IsOpcartesian.hom_ext_heq (pushLift_opcartesian α (Φ.obj c))
    rfl HEq.rfl (heq_of_eq (Φ.obj_push α c).symm) hθ₂.symm
    rfl HEq.rfl (heq_of_eq (Φ.obj_push α c').symm) (hR.trans hL.symm)).symm

/-- A D2SFib morphism preserves the pullback action on morphisms (heterogeneously). -/
theorem map_pullMap (Φ : D2SFibHom C C') {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : C.Fiber b'} (f : c ⟶ c') : Φ.map (pullMap β f) ≍ pullMap β (Φ.map f) := by
  have hθ₂ : ((Φ.obj_pull β c').symm ▸ pullLift β (Φ.obj c')) ≍ pullLift β (Φ.obj c') :=
    eqRec_heq_self _ _
  have hL : Φ.map (pullMap β f) ≫ᵈᵈ ((Φ.obj_pull β c').symm ▸ pullLift β (Φ.obj c'))
      ≍ pullLift β (Φ.obj c) ≫ᵈᵈ Φ.map f := by
    refine (C'.heq_comp_right rfl rfl HEq.rfl HEq.rfl
      (hθ₂.trans (Φ.map_pullLift β c').symm)).trans ?_
    refine (heq_of_eq (Φ.toVertFunctor.map_comp (pullMap β f) (pullLift β c'))).symm.trans ?_
    refine (heq_of_eq (congrArg Φ.map (pullMap_pullLift β f))).trans ?_
    refine (Φ.toVertFunctor.map_heq rfl rfl (by simp)
      ((B.id_comp_heq β).trans (B.comp_id_heq β).symm) HEq.rfl HEq.rfl (C.castHom_heq _ _ _)).trans ?_
    refine (heq_of_eq (Φ.toVertFunctor.map_comp (pullLift β c) f)).trans ?_
    exact C'.heq_comp_left rfl rfl HEq.rfl (heq_of_eq (Φ.obj_pull β c)) (Φ.map_pullLift β c)
  have hR : pullMap β (Φ.map f) ≫ᵈᵈ pullLift β (Φ.obj c') ≍ pullLift β (Φ.obj c) ≫ᵈᵈ Φ.map f :=
    (heq_of_eq (pullMap_pullLift β (Φ.map f))).trans (C'.castHom_heq _ _ _)
  exact (DoubleDisplayed.IsCartesian.hom_ext_heq (pullLift_isCartesian β (Φ.obj c'))
    rfl rfl rfl HEq.rfl (heq_of_eq (Φ.obj_pull β c').symm) hθ₂.symm
    rfl HEq.rfl (heq_of_eq (Φ.obj_pull β c).symm) (hR.trans hL.symm)).symm

/-- On fibers, `Φ` commutes with the pushforward functor on the nose. -/
theorem fiber_pushFunctor (Φ : D2SFibHom C C') {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    pushFunctor (C := C) α b ⋙ Φ.toVertFunctor.fiber (B.transp α b)
      = Φ.toVertFunctor.fiber b ⋙ pushFunctor (C := C') α b := by
  refine CategoryTheory.Functor.ext (fun c => Φ.obj_push α c) (fun c c' f => ?_)
  refine (CategoryTheory.conj_eqToHom_iff_heq (C := C'.Fiber (B.transp α b)) _ _
    (Φ.obj_push α c) (Φ.obj_push α c')).mpr ?_
  exact Φ.map_pushMap α f

/-- On fibers, `Φ` commutes with the pullback functor on the nose. -/
theorem fiber_pullFunctor (Φ : D2SFibHom C C') {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    pullFunctor (C := C) β ⋙ Φ.toVertFunctor.fiber b
      = Φ.toVertFunctor.fiber b' ⋙ pullFunctor (C := C') β := by
  refine CategoryTheory.Functor.ext (fun c => Φ.obj_pull β c) (fun c c' f => ?_)
  refine (CategoryTheory.conj_eqToHom_iff_heq (C := C'.Fiber b) _ _
    (Φ.obj_pull β c) (Φ.obj_pull β c')).mpr ?_
  exact Φ.map_pullMap β f

/-- A D2SFib morphism is determined by its fibers: `Φ.map θ` is the composite of the two chosen
lifts with `Φ` applied to the vertical morphism `d2sHomEquiv θ`. -/
theorem map_heq_lifts {C C' : DoubleDisplayed B} [D2SFib C]
    [D2SFib C'] (Φ : D2SFibHom C C') {a a' : A} {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'}
    {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c')
    (f : (push α (Φ.obj c)) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) (Φ.obj c')))
    (hf : Φ.map (d2sHomEquiv α g c c' θ) ≍ f) :
    Φ.map θ ≍ pushLift α (Φ.obj c) ≫ᵈᵈ (f ≫ᵈᵈ pullLift (B.factor g) (Φ.obj c')) := by
  have hg : g ≍ B.olift α b ≫ᵈ (B.id (B.transp α b) ≫ᵈ B.factor g) :=
    (olift_factor_heq α g).trans
      (B.heq_comp rfl (by simp) rfl rfl rfl HEq.rfl (B.id_comp_heq (B.factor g)).symm)
  refine (Φ.toVertFunctor.map_heq rfl rfl (by simp) hg HEq.rfl HEq.rfl
    (d2sHomEquiv_heq α g c c' θ).symm).trans ?_
  rw [Φ.toVertFunctor.map_comp]
  refine C'.heq_comp' rfl rfl rfl rfl rfl HEq.rfl (heq_of_eq (Φ.obj_push α c)) HEq.rfl
    HEq.rfl HEq.rfl (Φ.map_pushLift α c) ?_
  rw [Φ.toVertFunctor.map_comp]
  exact C'.heq_comp' rfl rfl rfl rfl rfl (heq_of_eq (Φ.obj_push α c))
    (heq_of_eq (Φ.obj_pull (B.factor g) c')) HEq.rfl HEq.rfl HEq.rfl hf
    (Φ.map_pullLift (B.factor g) c')

/-- `d2sHomEquiv` is natural in the D2SFib: applying `Φ` to the classifying vertical morphism of
`θ` gives the classifying vertical morphism of `Φ.map θ`. -/
theorem d2sHomEquiv_map_heq {C C' : DoubleDisplayed B} [D2SFib C] [D2SFib C']
    (Φ : D2SFibHom C C') {a a' : A} {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'}
    {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    d2sHomEquiv α g (Φ.obj c) (Φ.obj c') (Φ.map θ) ≍ Φ.map (d2sHomEquiv α g c c' θ) := by
  have hty : ((Φ.obj (push α c)) ⟶[[B.id (B.transp α b)]] (Φ.obj (pull (B.factor g) c')))
      = ((push α (Φ.obj c)) ⟶[[B.id (B.transp α b)]] (pull (B.factor g) (Φ.obj c'))) := by
    rw [Φ.obj_push, Φ.obj_pull]
  have h := d2sHomEquiv_eq_of_heq α g (Φ.map θ) (cast hty (Φ.map (d2sHomEquiv α g c c' θ)))
    (map_heq_lifts Φ θ _ (cast_heq hty _).symm).symm
  exact (heq_of_eq h.symm).trans (cast_heq hty _)

end D2SFibHom

/-- Bundled D2SFibs: the objects of the category `D2SFib(A, B)`. -/
structure D2SFibCat (B : Displayed A) [SplitOpfib B] where
  /-- The underlying doubly displayed category. -/
  C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B
  /-- Its D2SFib structure. -/
  [str : D2SFib C]

attribute [instance] D2SFibCat.str

/-- The category structure on bundled D2SFibs. -/
instance : Category (D2SFibCat B) where
  Hom E E' := D2SFibHom E.C E'.C
  id E := D2SFibHom.id E.C
  comp F G := F.comp G
  id_comp _ := D2SFibHom.ext rfl
  comp_id _ := D2SFibHom.ext rfl
  assoc _ _ _ := D2SFibHom.ext rfl

end Nfib
