import DoubleDisplayed.D2SFib.Straightening.Str.Unstraighten
import DoubleDisplayed.D2SFib.Straightening.Str.Straighten
import DoubleDisplayed.D2SFib.Straightening.Unit
import DoubleDisplayed.D2SFib.Straightening.Counit
import DoubleDisplayed.Equivalence
import Tactic.KernelTactic

/-!
# Straightening–unstraightening for D2SFibs

The unstraightening of dependent profunctors is an equivalence between `DProf`, doubly displayed
over `ICatStr`, and `D2SFibStr`, doubly displayed over `SplitOpfibStr`, lying over the
straightening–unstraightening equivalence `straighteningEquivStr : ICatStr ≃ SplitOpfibStr` of
split opfibrations (`straighteningEquiv`). Its functors are `unstraighten` and `straighten`: a
dependent profunctor over an indexed category `F` is the same as a split D2SFib over its
unstraightening `∫ F`, naturally in `F`.

The unit and counit are given explicitly, by components defined for a single split opfibration
(`D2SFib/Straightening/Unit.lean` and `Counit.lean`):

* The unit at `P` lies over the unit of `straighteningEquivStr`, whose components are identities.
  It is the identity on each `P ⟨a, x⟩`, which is the fiber of `Unstraightening P` over `x` on the
  nose (`unitHom`, `unitInv`). Its laws and its naturality hold by `rfl`, checked in the kernel.
* The counit at `E`, over `B`, lies over the counit `∫ (straightenObj B) ⟶ B` of
  `straighteningEquivStr` (`baseCounitHom`), which sends a morphism `φ` over `α` to `olift α ≫ φ`.
  It is the composite of the unstraightening of the identity transformation
  `straightenDProf E ⟶ baseCounitHom.dualOp.total ⋙ straightenObj E.C` (`counitNat`) with the counit
  `Unstraightening (straightenObj E.C) ⟶ E.C` over `B` (`Counit.homD2S`), and similarly for its
  inverse. Its laws are `Counit.invMap_map` and `Counit.map_invMap`, and its naturality is
  `Counit.map_naturality_str`: a map of D2SFibs preserves the chosen lifts.

The base objects of the equivalence, such as `(straightenStr ⋙ᵥ unstraightenStr).obj B`, are not
reducibly split opfibrations of the expected form, so instance search fails on the D2SFibs over
them. The components are therefore stated over `∫ (straightenObj B)` and `B` (`baseCounitHom`,
`baseStraightenMap`), and the kernel checks that they have the types that `EquivalenceOver` asks
for.
-/

universe v₃ u₃ u

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed Displayed.Opfibration.Straightening

open Displayed.Opfibration.Straightening (ICatStr StrictTrans)

/-! ## The unit -/

section Unit

variable {A : Cat.{u, u}} {F : ICatStr.{u}.Ob A}

/-- The unit at `P`, over the unit of `straighteningEquivStr`: identity functors. -/
def unitHom (P : DProf.{u, v₃, u₃}.Ob F) :
    P ⟶[[Opfibration.Straightening.straighteningEquivStr.unitIso.hom.app F]]
      straighten.obj (unstraighten.obj P) where
  app x := (unitApp P).hom.app x
  naturality _ _ u := (unitApp P).hom.naturality u

/-- The inverse of the unit at `P`. -/
def unitInv (P : DProf.{u, v₃, u₃}.Ob F) :
    straighten.obj (unstraighten.obj P)
      ⟶[[Opfibration.Straightening.straighteningEquivStr.unitIso.inv.app F]] P where
  app x := (unitApp P).inv.app x
  naturality _ _ u := (unitApp P).inv.naturality u

end Unit

/-! ## The counit -/

namespace Counit

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {B : Displayed.{u, u, u, u} A}
  {B' : Displayed.{u, u, u, u} A'} [SplitOpfib B] [SplitOpfib B']
  {H : OpcartesianFunctor u.toFunctor B B'} {C : DoubleDisplayed.{u, u, u, u, v₃, u₃} B}
  {C' : DoubleDisplayed.{u, u, u, u, v₃, u₃} B'} [SplitD2SFib C] [SplitD2SFib C']

/-- The counit commutes with maps of D2SFibs over arbitrary opcartesian functors. -/
theorem map_naturality_str (Φ : D2SFibMap H C C') {a a' : A} {α : a ⟶ a'} {b : B.Ob a}
    {b' : B.Ob a'} {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (Unstraightening (straightenObj C)).Hom g c c') :
    Φ.toObj.map (Counit.map (C := C) θ) =
      Counit.map (C := C') ((unstraightenStrMap (straightenStrMap Φ)).toObj.map θ) :=
  (congrArg Φ.toObj.map (Counit.map_def (C := C) θ)).trans (Counit.map_def (C := C') _).symm

end Counit

section Counit

variable {A : Cat.{u, u}} {B : SplitOpfibOb.{u, u, u, u} A}
  (E : D2SFibCat.{u, u, u, u, v₃, u₃} B.toDisplayed)

/-- The counit of `straighteningEquivStr` at `B`, `φ ↦ olift α ≫ φ`, with its source and target in
their simplest form. -/
def baseCounitHom :
    OpcartesianFunctor (𝟙 A : A ⟶ A).toFunctor (∫ (Opfibration.Straightening.straightenObj B))
      B.toDisplayed :=
  (Opfibration.Straightening.counitStrApp B).hom

/-- The inverse of the counit of `straighteningEquivStr` at `B`. -/
def baseCounitInv :
    OpcartesianFunctor (𝟙 A : A ⟶ A).toFunctor B.toDisplayed
      (∫ (Opfibration.Straightening.straightenObj B)) :=
  (Opfibration.Straightening.counitStrApp B).inv

/-- The straightening of `E` is `straightenObj E.C` along `baseCounitHom`, by identities. -/
def counitNat :
    straightenDProf E ⟶ (baseCounitHom (B := B)).dualOp.total ⋙
      (straightenObj E.C : B.toDisplayedᵒᵖ.Total ⥤ Cat.{v₃, u₃}) where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- `straightenObj E.C` is the straightening of `E` along `baseCounitInv`, by identities. -/
def counitNatInv :
    straightenObj E.C ⟶ (baseCounitInv (B := B)).dualOp.total ⋙ straightenDProf E where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- The counit at `E`, over `baseCounitHom`: the identity on objects, and `d2sHomEquiv⁻¹` on
morphisms. -/
def counitHom :
    D2SFibMap (baseCounitHom (B := B)) (Unstraightening (straightenDProf E)) E.C :=
  (unstraightenStrMap (counitNat E)).comp (Counit.homD2S (C := E.C))

/-- The inverse of the counit at `E`, over `baseCounitInv`. -/
def counitInv :
    D2SFibMap (baseCounitInv (B := B)) E.C (Unstraightening (straightenDProf E)) :=
  (Counit.invD2S (C := E.C)).comp (unstraightenStrMap (counitNatInv E))

/-- The counit at `E` followed by its inverse is the identity. -/
theorem counitHom_comp_counitInv :
    (counitHom E).comp (counitInv E) ≍ D2SFibMap.id (Unstraightening (straightenDProf E)) :=
  D2SFibMap.hext (by kernel_rfl') (fun _ => HEq.rfl) fun {_ _ f b _ g c c'} θ => by
    kernel_exact heq_of_eq (Counit.invMap_map (C := E.C) (g := B.toDisplayed.olift f b ≫ᵈ g)
      (c := c) (c' := c') (by kernel_exact θ))

/-- The inverse of the counit at `E` followed by the counit is the identity. -/
theorem counitInv_comp_counitHom : (counitInv E).comp (counitHom E) ≍ D2SFibMap.id E.C :=
  D2SFibMap.hext (by kernel_rfl') (fun _ => HEq.rfl) fun θ => by
    kernel_exact heq_of_eq (Counit.map_invMap (C := E.C) θ)

end Counit

section Naturality

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {B : SplitOpfibOb.{u, u, u, u} A}
  {B' : SplitOpfibOb.{u, u, u, u} A'}

/-- The image of `H` under `straightenStr ⋙ unstraightenStr`, with its source and target in their
simplest form. -/
def baseStraightenMap (H : OpcartesianFunctor u.toFunctor B.toDisplayed B'.toDisplayed) :
    OpcartesianFunctor u.toFunctor (∫ (Opfibration.Straightening.straightenObj B))
      (∫ (Opfibration.Straightening.straightenObj B')) :=
  StrictTrans.unstraighten (u := u.toFunctor) (Opfibration.Straightening.straightenStr.map H)

/-- The counit is natural with respect to maps of D2SFibs over arbitrary opcartesian functors. -/
theorem counitHom_naturality {H : OpcartesianFunctor u.toFunctor B.toDisplayed B'.toDisplayed}
    {E : D2SFibCat.{u, u, u, u, v₃, u₃} B.toDisplayed}
    {E' : D2SFibCat.{u, u, u, u, v₃, u₃} B'.toDisplayed} (Φ : D2SFibMap H E.C E'.C) :
    (unstraightenStrMap (H := baseStraightenMap H) (straightenMap Φ)).comp (counitHom E') ≍
      (counitHom E).comp Φ :=
  D2SFibMap.hext (by kernel_exact Opfibration.Straightening.counitStrIso.hom.naturality H)
    (fun _ => HEq.rfl) fun {_ _ f b _ g c c'} θ => by
      kernel_exact heq_of_eq (Counit.map_naturality_str Φ (g := B.toDisplayed.olift f b ≫ᵈ g)
        (c := c) (c' := c') (by kernel_exact θ)).symm

end Naturality

/-! ## The equivalence -/

/-- **Straightening–unstraightening for D2SFibs**: the unstraightening of dependent profunctors is
an equivalence between `DProf` over `ICatStr` and `D2SFibStr` over `SplitOpfibStr`, lying over the
straightening–unstraightening equivalence `ICatStr ≃ SplitOpfibStr`, with inverse the
straightening. -/
def straighteningEquiv :
    EquivalenceOver Opfibration.Straightening.straighteningEquivStr DProf.{u, v₃, u₃}
      D2SFibStr.{u, u, u, u, v₃, u₃} where
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
