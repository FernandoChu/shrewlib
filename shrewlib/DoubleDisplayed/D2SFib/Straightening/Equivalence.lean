import DoubleDisplayed.D2SFib.Straightening.Unstraighten
import DoubleDisplayed.D2SFib.Straightening.Straighten
import DoubleDisplayed.Equivalence
import Mathlib.Tactic.IrreducibleDef
import Tactic.KernelTactic

/-!
# Straightening–unstraightening for D2SFibs

The unstraightening of dependent profunctors is an equivalence between `DProf`, doubly displayed
over `ICatStr`, and `D2SFibStr`, doubly displayed over `SplitOpfibStr`, lying over the
straightening–unstraightening equivalence `straighteningEquivStr : ICatStr ≃ SplitOpfibStr` of
split opfibrations (`straighteningEquiv`). Its functors are `unstraighten` and `straighten`: a
dependent profunctor over an indexed category `F` is the same as a split D2SFib over its
unstraightening `∫ F`, naturally in `F`.

* The unit at `P` lies over the unit of `straighteningEquivStr`, whose components are identities.
  It is the identity on each `P ⟨a, x⟩`, which is the fiber of `Unstraightening P` over `x` on the
  nose (`unitApp`). Its naturality is the factorization of a morphism of
  `(∫ (F ⋙ opFunctor')).Total` into a chosen horizontal and a chosen vertical morphism,
  `Unstraightening.map_eq`. Its laws and its naturality hold by `rfl`, checked in the kernel.
* The counit at `E`, over `B`, lies over the counit `counitStrHom B : ∫ (straightenObj B) ⟶ B` of
  `straighteningEquivStr`, which sends a morphism `g` over `α` to `olift α ≫ g`. Its objects are
  those of `E`, and so are its hom-types: a morphism of `Unstraightening (straightenDProf E)` over
  `g` is, by the rewrite rules, a vertical morphism `push α c ⟶ pull (opcartesianFactor g') c'` of
  `E`, for `g' = olift α ≫ g` (`Counit.hom_eq`). So the counit acts on morphisms by the inverse of
  `d2sHomEquiv` at `g'` (`Counit.map`), and its inverse, over `counitStrInv B`, by `d2sHomEquiv`
  (`Counit.invMap`). Their functoriality is `d2sHomEquiv_comp`, and they preserve the chosen lifts
  by `rfl`. The naturality of the counit holds because a map of D2SFibs preserves the chosen lifts.

The base objects of the equivalence, such as `(straightenStr ⋙ᵥ unstraightenStr).obj B`, are not
reducibly split opfibrations of the expected form, so instance search fails on the D2SFibs over
them. The components are therefore stated over `∫ (straightenObj B)` and `B`, along
`counitStrHom B` and the unstraightening of `straightenStrMap H`, whose types have this form, and
the kernel checks that they have the types that `EquivalenceOver` asks for.
-/

universe v₃ u₃ v₂ u₂ v₁ u₁

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed Displayed.Opfibration.Straightening

open Displayed.Opfibration.Straightening (ICatStr StrictTrans counitStrHom counitStrInv)

/-! ## The unit -/

section Unit

namespace Unstraightening

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v₂, u₂}}
  (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) {a : A}

/-- The unit component, forward direction: the fiber of `Unstraightening P` over `b` is
`P.obj ⟨a, b⟩`. -/
def unitFiberFunctor (b : (∫ F).Ob a) :
    P.obj ((∫ (F ⋙ opFunctor')).tot b) ⥤ (Unstraightening P).Fiber b where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component, backward direction. -/
def unitFiberInv (b : (∫ F).Ob a) :
    (Unstraightening P).Fiber b ⥤ P.obj ((∫ (F ⋙ opFunctor')).tot b) where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component as an isomorphism of `Cat`. -/
def unitFiberIso (b : (∫ F).Ob a) :
    P.obj ((∫ (F ⋙ opFunctor')).tot b) ≅ Cat.of ((Unstraightening P).Fiber b) where
  hom := (unitFiberFunctor P b).toCatHom
  inv := (unitFiberInv P b).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end Unstraightening

/-- **The unit at `P`**: `P ≅ straightenObj (Unstraightening P)`, by identity functors. -/
def unitApp {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v₂, u₂}}
    (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) :
    P ≅ straightenObj (Unstraightening P) :=
  NatIso.ofComponents (fun x => Unstraightening.unitFiberIso P x.2) (fun {x y} h => by
    apply Cat.ext
    -- `_root_.id` gives the objects of `(∫ (F ⋙ opFunctor')).Total` their type in `∫ F`, so
    -- that instance search finds the fiber categories of `Unstraightening P` over them.
    change (P.map h).toFunctor ⋙ Unstraightening.unitFiberFunctor P (@_root_.id ((∫ F).Ob y.1) y.2)
      = Unstraightening.unitFiberFunctor P (@_root_.id ((∫ F).Ob x.1) x.2)
        ⋙ (pushFunctor (C := Unstraightening P) h.base (@_root_.id ((∫ F).Ob x.1) x.2)
          ⋙ pullFunctor (C := Unstraightening P) (b := @_root_.id ((∫ F).Ob y.1) y.2)
            (b' := (∫ F).push h.base x.2) h.fiber)
    rw [Unstraightening.map_eq P h]
    exact Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))

variable {A : Cat.{v₁, u₁}} {F : ICatStr.{v₂, u₂, v₁, u₁}.Ob A}

/-- The unit at `P`, over the unit of `straighteningEquivStr`: identity functors. -/
def unitHom (P : DProf.{v₃, u₃, v₂, u₂, v₁, u₁}.Ob F) :
    P ⟶[[Opfibration.Straightening.straighteningEquivStr.unitIso.hom.app F]]
      straighten.obj (unstraighten.obj P) where
  app x := (unitApp P).hom.app x
  naturality _ _ h := (unitApp P).hom.naturality h

/-- The inverse of the unit at `P`. -/
def unitInv (P : DProf.{v₃, u₃, v₂, u₂, v₁, u₁}.Ob F) :
    straighten.obj (unstraighten.obj P)
      ⟶[[Opfibration.Straightening.straighteningEquivStr.unitIso.inv.app F]] P where
  app x := (unitApp P).inv.app x
  naturality _ _ h := (unitApp P).inv.naturality h

end Unit

/-! ## The counit -/

namespace Counit

variable {A : Cat.{v₁, u₁}} {B : SplitOpfibOb.{v₂, u₂} A}
  {E : D2SFibCat.{v₃, u₃} B.toDisplayed}

section

variable {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''}
  {b : (∫ (Opfibration.Straightening.straightenObj B)).Ob a}
  {b' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a'}
  {b'' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a''}

/-- The hom-types of `Unstraightening (straightenDProf E)` over `g` are the targets of
`d2sHomEquiv` at `olift α ≫ g`. -/
theorem hom_eq (g : b ⟶[α] b') (c : E.C.Ob b) (c' : E.C.Ob b') :
    (Unstraightening (straightenDProf E)).Hom g c c' =
      (push α c ⟶ pull (B.toDisplayed.opcartesianFactor ((counitStrHom B).toPre.map g)) c') :=
  rfl

/-- The counit on morphisms. It is irreducible: its value composes with the chosen lifts, and rules
such as `VertFunctor.map_comp` would otherwise see through it. -/
irreducible_def map {g : b ⟶[α] b'} {c : E.C.Ob b} {c' : E.C.Ob b'}
    (θ : (Unstraightening (straightenDProf E)).Hom g c c') :
    c ⟶[[(counitStrHom B).toPre.map g]] c' :=
  (d2sHomEquiv α ((counitStrHom B).toPre.map g) c c').symm θ

theorem map_id' (c : E.C.Ob b) :
    map (DoubleDisplayed.id (Unstraightening (straightenDProf E)) c) = E.C.id c := by
  rw [map_def]; rfl

theorem map_pullLift {b₀ b₁ : (∫ (Opfibration.Straightening.straightenObj B)).Ob a}
    (β : b₀ ⟶[𝟙 a] b₁) (c : E.C.Ob b₁) :
    map (pullLift (C := Unstraightening (straightenDProf E)) β c) =
      pullLift ((counitStrHom B).toPre.map β) c :=
  (map_def _).trans rfl

theorem map_pushLift (c : E.C.Ob b) :
    map (pushLift (C := Unstraightening (straightenDProf E)) α c) =
      pushLift ((𝟙 A : A ⟶ A).toFunctor.map α) c :=
  (map_def _).trans rfl

end

section

variable {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.toDisplayed.Ob a}
  {b' : B.toDisplayed.Ob a'} {b'' : B.toDisplayed.Ob a''}

/-- The inverse of the counit on morphisms. -/
irreducible_def invMap {g : b ⟶[α] b'} {c : E.C.Ob b} {c' : E.C.Ob b'} (θ : c ⟶[[g]] c') :
    (Unstraightening (straightenDProf E)).Hom ((counitStrInv B).toPre.map g) c c' :=
  d2sHomEquiv α g c c' θ

theorem invMap_id (c : E.C.Ob b) :
    invMap (E.C.id c) = DoubleDisplayed.id (Unstraightening (straightenDProf E)) c := by
  rw [invMap_def]; exact d2sHomEquiv_id c

set_option maxHeartbeats 800000 in
-- Composition in `Unstraightening (straightenDProf E)` unfolds to the composite of
-- `d2sHomEquiv_comp` through the fibers of `straightenDProf E`, which is a long definitional
-- computation.
theorem invMap_comp {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : E.C.Ob b} {c' : E.C.Ob b'}
    {c'' : E.C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') :
    invMap (θ ≫ᵈᵈ θ') = invMap θ ≫ᵈᵈ invMap θ' := by
  rw [invMap_def, invMap_def, invMap_def]
  exact d2sHomEquiv_comp α α' g g' θ θ'

theorem invMap_pullLift {b₀ b₁ : B.toDisplayed.Ob a} (β : b₀ ⟶[𝟙 a] b₁) (c : E.C.Ob b₁) :
    invMap (pullLift β c) =
      pullLift (C := Unstraightening (straightenDProf E)) ((counitStrInv B).toPre.map β) c := by
  rw [invMap_def]; exact d2sHomEquiv_pullLift β c

theorem invMap_pushLift (c : E.C.Ob b) :
    invMap (pushLift α c) =
      pushLift (C := Unstraightening (straightenDProf E)) ((𝟙 A : A ⟶ A).toFunctor.map α) c := by
  rw [invMap_def]; exact d2sHomEquiv_pushLift α c

/-- The counit, then its inverse, on morphisms. -/
theorem invMap_map {b : (∫ (Opfibration.Straightening.straightenObj B)).Ob a}
    {b' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a'} {g : b ⟶[α] b'}
    {c : E.C.Ob b} {c' : E.C.Ob b'}
    (θ : (Unstraightening (straightenDProf E)).Hom g c c') : invMap (map θ) = θ :=
  (invMap_def (map θ)).trans ((congrArg (d2sHomEquiv α _ c c') (map_def θ)).trans
    ((d2sHomEquiv α ((counitStrHom B).toPre.map g) c c').apply_symm_apply θ))

/-- The inverse of the counit, then the counit, on morphisms. -/
theorem map_invMap {g : b ⟶[α] b'} {c : E.C.Ob b} {c' : E.C.Ob b'} (θ : c ⟶[[g]] c') :
    map (invMap θ) = θ :=
  (map_def (invMap θ)).trans ((congrArg (d2sHomEquiv α _ c c').symm (invMap_def θ)).trans
    ((d2sHomEquiv α g c c').symm_apply_apply θ))

end

theorem map_comp {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''}
    {b : (∫ (Opfibration.Straightening.straightenObj B)).Ob a}
    {b' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a'}
    {b'' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a''} {g : b ⟶[α] b'}
    {g' : b' ⟶[α'] b''} {c : E.C.Ob b} {c' : E.C.Ob b'} {c'' : E.C.Ob b''}
    (θ : (Unstraightening (straightenDProf E)).Hom g c c')
    (θ' : (Unstraightening (straightenDProf E)).Hom g' c' c'') :
    map (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ' :=
  have h : invMap (map θ ≫ᵈᵈ map θ') = θ ≫ᵈᵈ θ' :=
    (invMap_comp (map θ) (map θ')).trans
      (congrArg₂ (· ≫ᵈᵈ ·) (invMap_map θ) (invMap_map θ'))
  (congrArg map h.symm).trans (map_invMap _)

end Counit

section Counit

variable {A : Cat.{v₁, u₁}} {B : SplitOpfibOb.{v₂, u₂} A}
  (E : D2SFibCat.{v₃, u₃} B.toDisplayed)

/-- **The counit at `E`**, over `counitStrHom B`: the identity on objects, and `d2sHomEquiv⁻¹` on
morphisms. -/
def counitHom :
    D2SFibMap (counitStrHom B) (Unstraightening (straightenDProf E)) E.C where
  toObj :=
    { obj := fun c => c
      map := fun θ => Counit.map θ
      map_id := fun c => Counit.map_id' c
      map_comp := fun θ θ' => Counit.map_comp θ θ' }
  map_pullLift := by intros; exact Counit.map_pullLift _ _
  map_pushLift := by intros; exact Counit.map_pushLift _

/-- **The inverse of the counit at `E`**, over `counitStrInv B`: the identity on objects, and
`d2sHomEquiv` on morphisms. -/
def counitInv :
    D2SFibMap (counitStrInv B) E.C (Unstraightening (straightenDProf E)) where
  toObj :=
    { obj := fun c => c
      map := fun θ => Counit.invMap θ
      map_id := fun c => Counit.invMap_id c
      map_comp := fun θ θ' => Counit.invMap_comp θ θ' }
  map_pullLift := by intros; exact Counit.invMap_pullLift _ _
  map_pushLift := by intros; exact Counit.invMap_pushLift _

/-- The counit at `E` followed by its inverse is the identity. -/
theorem counitHom_comp_counitInv :
    (counitHom E).comp (counitInv E) ≍ D2SFibMap.id (Unstraightening (straightenDProf E)) :=
  D2SFibMap.hext (by kernel_rfl') (fun _ => HEq.rfl) fun θ => heq_of_eq (Counit.invMap_map θ)

/-- The inverse of the counit at `E` followed by the counit is the identity. -/
theorem counitInv_comp_counitHom : (counitInv E).comp (counitHom E) ≍ D2SFibMap.id E.C :=
  D2SFibMap.hext (by kernel_rfl') (fun _ => HEq.rfl) fun θ => heq_of_eq (Counit.map_invMap θ)

end Counit

section Naturality

variable {A A' : Cat.{v₁, u₁}} {u : A ⟶ A'} {B : SplitOpfibOb.{v₂, u₂} A}
  {B' : SplitOpfibOb.{v₂, u₂} A'}

/-- The counit commutes with maps of D2SFibs over arbitrary opcartesian functors. -/
theorem Counit.map_naturality {H : OpcartesianFunctor u.toFunctor B.toDisplayed B'.toDisplayed}
    {E : D2SFibCat.{v₃, u₃} B.toDisplayed}
    {E' : D2SFibCat.{v₃, u₃} B'.toDisplayed} (Φ : D2SFibMap H E.C E'.C) {a a' : A}
    {α : a ⟶ a'} {b : (∫ (Opfibration.Straightening.straightenObj B)).Ob a}
    {b' : (∫ (Opfibration.Straightening.straightenObj B)).Ob a'} {g : b ⟶[α] b'}
    {c : E.C.Ob b} {c' : E.C.Ob b'}
    (θ : (Unstraightening (straightenDProf E)).Hom g c c') :
    Φ.toObj.map (Counit.map θ) =
      Counit.map (E := E')
        ((unstraightenStrMap (τ := Opfibration.Straightening.straightenStrMap H)
          (straightenMap Φ)).toObj.map θ) :=
  (congrArg Φ.toObj.map (Counit.map_def θ)).trans (Counit.map_def _).symm

/-- The counit is natural with respect to maps of D2SFibs over arbitrary opcartesian functors. -/
theorem counitHom_naturality {H : OpcartesianFunctor u.toFunctor B.toDisplayed B'.toDisplayed}
    {E : D2SFibCat.{v₃, u₃} B.toDisplayed}
    {E' : D2SFibCat.{v₃, u₃} B'.toDisplayed} (Φ : D2SFibMap H E.C E'.C) :
    (unstraightenStrMap (τ := Opfibration.Straightening.straightenStrMap H)
      (straightenMap Φ)).comp (counitHom E') ≍ (counitHom E).comp Φ :=
  D2SFibMap.hext (by kernel_exact Opfibration.Straightening.counitStrIso.hom.naturality H)
    (fun _ => HEq.rfl) fun θ => heq_of_eq (Counit.map_naturality Φ θ).symm

end Naturality

/-! ## The equivalence -/

/-- **Straightening–unstraightening for D2SFibs**: the unstraightening of dependent profunctors is
an equivalence between `DProf` over `ICatStr` and `D2SFibStr` over `SplitOpfibStr`, lying over the
straightening–unstraightening equivalence `ICatStr ≃ SplitOpfibStr`, with inverse the
straightening. -/
def straighteningEquiv :
    EquivalenceOver Opfibration.Straightening.straighteningEquivStr DProf.{v₃, u₃, v₂, u₂, v₁, u₁}
      D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁} where
  functor := unstraighten
  inverse := straighten
  unitHom P := unitHom P
  unitInv P := unitInv P
  unitHom_unitInv _ := by kernel_rfl'
  unitInv_unitHom _ := by kernel_rfl'
  unitHom_naturality _ := by kernel_rfl'
  counitHom E := counitHom E
  counitInv E := counitInv E
  counitHom_counitInv E := by kernel_exact counitHom_comp_counitInv E
  counitInv_counitHom E := by kernel_exact counitInv_comp_counitHom E
  counitHom_naturality Φ := by kernel_exact counitHom_naturality Φ

end DoubleDisplayed.D2SFib.Straightening
