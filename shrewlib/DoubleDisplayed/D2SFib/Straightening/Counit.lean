import DoubleDisplayed.D2SFib.Straightening.Unstraighten
import DoubleDisplayed.D2SFib.Straightening.Straighten
import Mathlib.Tactic.IrreducibleDef

/-!
# The counit of straightening–unstraightening

The unstraightening of `straightenObj C` is isomorphic to `C` (`counitApp`). Objects
agree definitionally, and so do hom-types: a morphism of `Unstraightening (straightenObj C)` over
`g : B.Hom α b b'` is, by the rewrite rules, a vertical morphism
`push α c ⟶ pull (B.opcartesianFactor g) c'` of `C`. So the counit acts on morphisms by the
inverse of `d2sHomEquiv`, its functoriality is `d2sHomEquiv_comp`, and it preserves the chosen lifts
by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

section

namespace Counit

variable {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} [SplitD2SFib C]

variable {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}

/-- The hom-types of `Unstraightening (straightenObj C)` are the targets of `d2sHomEquiv`. -/
theorem hom_eq (g : b ⟶[α] b') (c : C.Ob b) (c' : C.Ob b') :
    (Unstraightening (straightenObj C)).Hom g c c' =
      (push α c ⟶ pull (B.opcartesianFactor g) c') := rfl

/-- The counit on morphisms. It is irreducible: its value composes with the chosen lifts, and rules
such as `VertFunctor.map_comp` would otherwise see through it. -/
irreducible_def map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (Unstraightening (straightenObj C)).Hom g c c') : c ⟶[[g]] c' :=
  (d2sHomEquiv α g c c').symm θ

/-- The counit on morphisms, backward direction. -/
irreducible_def invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    (Unstraightening (straightenObj C)).Hom g c c' :=
  d2sHomEquiv α g c c' θ

theorem map_invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    map (C := C) (invMap θ) = θ := by
  rw [map_def (C := C), invMap_def (C := C)]; exact (d2sHomEquiv α g c c').symm_apply_apply θ

theorem invMap_map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (Unstraightening (straightenObj C)).Hom g c c') : invMap (C := C) (map θ) = θ := by
  rw [map_def (C := C), invMap_def (C := C)]; exact (d2sHomEquiv α g c c').apply_symm_apply θ

theorem map_id' (c : C.Ob b) :
    map (C := C) (DoubleDisplayed.id (Unstraightening (straightenObj C)) c) = C.id c := by
  rw [map_def (C := C)]; rfl

set_option maxHeartbeats 800000 in
-- Composition in `Unstraightening (straightenObj C)` unfolds to the composite of `d2sHomEquiv_comp`
-- through the fibers of `straightenObj C`, which is a long definitional computation.
theorem invMap_comp {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    invMap (C := C) (θ ≫ᵈᵈ θ') = invMap θ ≫ᵈᵈ invMap θ' := by
  rw [invMap_def (C := C), invMap_def (C := C), invMap_def (C := C)]
  exact d2sHomEquiv_comp α α' g g' θ θ'

theorem map_comp {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : (Unstraightening (straightenObj C)).Hom g c c')
    (θ' : (Unstraightening (straightenObj C)).Hom g' c' c'') :
    map (C := C) (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ' := by
  rw [← invMap_map θ, ← invMap_map θ', ← invMap_comp, map_invMap, map_invMap, map_invMap]

theorem map_pullLift {b₀ b₁ : B.Ob a} (β : b₀ ⟶[𝟙 a] b₁) (c : C.Ob b₁) :
    map (C := C) (pullLift (C := Unstraightening (straightenObj C)) β c) = pullLift β c :=
  (map_def (C := C) _).trans rfl

theorem map_pushLift (c : C.Ob b) :
    map (C := C) (pushLift (C := Unstraightening (straightenObj C)) α c) = pushLift α c :=
  (map_def (C := C) _).trans rfl

theorem invMap_pullLift {b₀ b₁ : B.Ob a} (β : b₀ ⟶[𝟙 a] b₁) (c : C.Ob b₁) :
    invMap (C := C) (pullLift β c) = pullLift (C := Unstraightening (straightenObj C)) β c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_pullLift β c

theorem invMap_pushLift (c : C.Ob b) :
    invMap (C := C) (pushLift α c) = pushLift (C := Unstraightening (straightenObj C)) α c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_pushLift α c

theorem invMap_id (c : C.Ob b) :
    invMap (C := C) (C.id c) = DoubleDisplayed.id (Unstraightening (straightenObj C)) c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_id c

/-- **The counit component**, forward direction: the identity on objects, `d2sHomEquiv⁻¹` on
morphisms. -/
def homD2S : D2SFibMap (OpcartesianFunctor.id B) (Unstraightening (straightenObj C)) C where
  toObj :=
    { obj := fun c => c
      map := fun θ => map (C := C) θ
      map_id := fun c => map_id' (C := C) c
      map_comp := fun θ θ' => map_comp (C := C) θ θ'
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; exact map_pullLift (C := C) _ _
  map_pushLift := by intros; exact map_pushLift (C := C) _

/-- **The counit component**, backward direction. -/
def invD2S : D2SFibMap (OpcartesianFunctor.id B) C (Unstraightening (straightenObj C)) where
  toObj :=
    { obj := fun c => c
      map := fun θ => invMap (C := C) θ
      map_id := fun c => invMap_id (C := C) c
      map_comp := fun θ θ' => invMap_comp (C := C) θ θ'
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; exact invMap_pullLift (C := C) _ _
  map_pushLift := by intros; exact invMap_pushLift (C := C) _

end Counit

/-- **The counit at `E`**: the unstraightening of
`straightenObj E.C` is isomorphic to `E`, by the identity on objects and `d2sHomEquiv` on
morphisms. -/
def counitApp (E : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) :
    unstraightenObj (straightenObj E.C) ≅ E where
  hom := Counit.homD2S (C := E.C)
  inv := Counit.invD2S (C := E.C)
  hom_inv_id := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.invMap_map (C := E.C) θ)))
  inv_hom_id := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.map_invMap (C := E.C) θ)))

end

end DoubleDisplayed.D2SFib.Straightening
