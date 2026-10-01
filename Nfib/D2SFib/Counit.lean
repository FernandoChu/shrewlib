import Nfib.D2SFib.Grothendieck
import Nfib.D2SFib.ToFunctor
import Mathlib.Tactic.IrreducibleDef

/-!
# The counit `Ψ ⋙ Φ ≅ 𝟭`

Milestone **M9** of `PLAN.md`, following the paper's argument: the D2S Grothendieck construction of
`Ψ C` is isomorphic to `C`. Objects agree definitionally, and so do hom-types: a morphism of
`D2SGC (Ψ C)` over `g : B.Hom α b b'` is, by the rewrite rules, a vertical morphism
`push α c ⟶ pull (B.opcartesianFactor g) c'` of `C`. So the counit acts on morphisms by
`d2sHomEquiv⁻¹`, its functoriality is `d2sHomEquiv_comp`, and it preserves the chosen lifts by
`rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

noncomputable section

namespace Counit

variable {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} [D2SFib C]

variable {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}

/-- The hom-types of `D2SGC (Ψ C)` are the targets of `d2sHomEquiv`. -/
theorem hom_eq (g : b ⟶[α] b') (c : C.Ob b) (c' : C.Ob b') :
    (D2SGC (toFunctorObj C)).Hom g c c' = (push α c ⟶ pull (B.opcartesianFactor g) c') := rfl

/-- The counit on morphisms. It is irreducible: its value composes with the chosen lifts, and rules
such as `VertFunctor.map_comp` would otherwise see through it. -/
irreducible_def map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (D2SGC (toFunctorObj C)).Hom g c c') : c ⟶[[g]] c' :=
  (d2sHomEquiv α g c c').symm θ

/-- The counit on morphisms, backward direction. -/
irreducible_def invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    (D2SGC (toFunctorObj C)).Hom g c c' :=
  d2sHomEquiv α g c c' θ

theorem map_invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    map (C := C) (invMap θ) = θ := by
  rw [map_def (C := C), invMap_def (C := C)]; exact (d2sHomEquiv α g c c').symm_apply_apply θ

theorem invMap_map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (D2SGC (toFunctorObj C)).Hom g c c') : invMap (C := C) (map θ) = θ := by
  rw [map_def (C := C), invMap_def (C := C)]; exact (d2sHomEquiv α g c c').apply_symm_apply θ

theorem map_id' (c : C.Ob b) :
    map (C := C) (DoubleDisplayed.id (D2SGC (toFunctorObj C)) c) = C.id c := by
  rw [map_def (C := C)]; rfl

set_option maxHeartbeats 800000 in
-- Composition in `D2SGC (Ψ C)` unfolds to the composite of `d2sHomEquiv_comp` through the fibers of
-- `Ψ C`, which is a long definitional computation.
theorem invMap_comp {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    invMap (C := C) (θ ≫ᵈᵈ θ') = invMap θ ≫ᵈᵈ invMap θ' := by
  rw [invMap_def (C := C), invMap_def (C := C), invMap_def (C := C)]
  exact d2sHomEquiv_comp α α' g g' θ θ'

theorem map_comp {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : (D2SGC (toFunctorObj C)).Hom g c c')
    (θ' : (D2SGC (toFunctorObj C)).Hom g' c' c'') :
    map (C := C) (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ' := by
  rw [← invMap_map θ, ← invMap_map θ', ← invMap_comp, map_invMap, map_invMap, map_invMap]

theorem map_pullLift {b₀ b₁ : B.Ob a} (β : b₀ ⟶[𝟙 a] b₁) (c : C.Ob b₁) :
    map (C := C) (pullLift (C := D2SGC (toFunctorObj C)) β c) = pullLift β c :=
  (map_def (C := C) _).trans rfl

theorem map_pushLift (c : C.Ob b) :
    map (C := C) (pushLift (C := D2SGC (toFunctorObj C)) α c) = pushLift α c :=
  (map_def (C := C) _).trans rfl

theorem invMap_pullLift {b₀ b₁ : B.Ob a} (β : b₀ ⟶[𝟙 a] b₁) (c : C.Ob b₁) :
    invMap (C := C) (pullLift β c) = pullLift (C := D2SGC (toFunctorObj C)) β c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_pullLift β c

theorem invMap_pushLift (c : C.Ob b) :
    invMap (C := C) (pushLift α c) = pushLift (C := D2SGC (toFunctorObj C)) α c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_pushLift α c

theorem invMap_id (c : C.Ob b) :
    invMap (C := C) (C.id c) = DoubleDisplayed.id (D2SGC (toFunctorObj C)) c := by
  rw [invMap_def (C := C)]; exact d2sHomEquiv_id c

/-- **The counit component**, forward direction: the identity on objects, `d2sHomEquiv⁻¹` on
morphisms. -/
def homD2S : D2SFibHom (D2SGC (toFunctorObj C)) C where
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
def invD2S : D2SFibHom C (D2SGC (toFunctorObj C)) where
  toObj :=
    { obj := fun c => c
      map := fun θ => invMap (C := C) θ
      map_id := fun c => invMap_id (C := C) c
      map_comp := fun θ θ' => invMap_comp (C := C) θ θ'
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; exact invMap_pullLift (C := C) _ _
  map_pushLift := by intros; exact invMap_pushLift (C := C) _

/-- The counit commutes with D2SFib morphisms. -/
theorem map_naturality {E E' : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B} (Φ : E ⟶ E') {g : b ⟶[α] b'}
    {c : E.C.Ob b} {c' : E.C.Ob b'} (θ : (D2SGC (toFunctorObj E.C)).Hom g c c') :
    Φ.toObj.map (map (C := E.C) θ) = map (C := E'.C) ((D2SGCMap (toFunctorMap Φ)).toObj.map θ) :=
  (congrArg Φ.toObj.map (map_def (C := E.C) θ)).trans (map_def (C := E'.C) _).symm

end Counit

/-- **The counit component of the equivalence** (the paper's `F`/`G` pair): the D2S Grothendieck
construction of `Ψ E` is isomorphic to `E`, by the identity on objects and `d2sHomEquiv` on
morphisms. -/
def counitApp (E : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) : D2SGCFib (toFunctorObj E.C) ≅ E where
  hom := Counit.homD2S (C := E.C)
  inv := Counit.invD2S (C := E.C)
  hom_inv_id := D2SFibHom.ext (VertFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.invMap_map (C := E.C) θ)))
  inv_hom_id := D2SFibHom.ext (VertFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.map_invMap (C := E.C) θ)))

/-- **The counit** `Ψ ⋙ Φ ≅ 𝟭` of the equivalence. -/
def counitIso : toFunctor ⋙ D2SGCFunctor ≅ 𝟭 (D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) :=
  NatIso.ofComponents (fun E => counitApp E) (fun Φ =>
    D2SFibHom.ext (VertFunctor.ext (fun _ => rfl)
      (fun θ => heq_of_eq (Counit.map_naturality Φ θ).symm)))

end

end Nfib
