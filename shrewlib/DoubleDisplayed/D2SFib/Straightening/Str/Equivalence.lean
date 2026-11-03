import DoubleDisplayed.D2SFib.Straightening.Str.Unstraighten
import DoubleDisplayed.D2SFib.Straightening.Str.Straighten
import DoubleDisplayed.D2SFib.Straightening.Unit
import DoubleDisplayed.D2SFib.Straightening.Counit
import DoubleDisplayed.Equivalence
import Tactic.KernelTactic

/-!
# Straightening–unstraightening for D2SFibs, over `SplitOpfibStr`

The unstraightening of dependent profunctors extends to an equivalence `DProfStr ≃ D2SFibStr` over
`SplitOpfibStr` (`straighteningEquivStr`), whose functors are `unstraightenStr` and
`straightenStr`: dependent profunctors are the same as split D2SFibs, naturally in the split
opfibration they lie over. The base is in `Cat.{v₁, u₁}`, the split opfibrations are in
`Displayed.{v₁, u₁, v₂, u₂}`, and the dependent profunctors and the fibers of the D2SFibs are in
`Cat.{v₃, u₃}`, all independent. Over a single split opfibration `B`, its fiber is an equivalence
between the functors `Bᵒᵖ.Total ⥤ Cat` and the category `D2SFibCat B`.

The unit and counit are given explicitly, by components defined for a single `B`
(`D2SFib/Straightening/Unit.lean` and `Counit.lean`):

* the unit `𝟭 ≅ unstraightenStr ⋙ straightenStr` at `P` is the identity on each `P ⟨a, x⟩`, which
  is the fiber of `Unstraightening P` over `x` on the nose (`unitApp`);
* the counit `straightenStr ⋙ unstraightenStr ≅ 𝟭` at `C` is the identity on objects, and on
  morphisms composes the vertical morphism `push α c ⟶ pull (opcartesianFactor g) c'` that a
  morphism of `Unstraightening (straightenObj C)` over `g` is with the chosen lifts (`counitApp`).

Their naturality in `B` is their naturality with respect to the morphisms over arbitrary
opcartesian functors, which holds by `rfl` for the unit, and for the counit since a map of D2SFibs
preserves the chosen lifts (`Counit.map_naturality_str`).

Both functors are cartesian (`unstraightenStrCartesian`, `straightenStrCartesian`), so that this is
an equivalence of fibred categories over `SplitOpfibStr`. The unstraightening of
`H.dualOp.total ⋙ P'` is the reindexing along `H` of that of `P'`. The two agree field by field by
`rfl`, but the kernel does not accept an `rfl` between the structures, so the equation goes through
extensionality.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

/-! ## The unit -/

/-- The unit at `P`: `P ≅ straightenObj (Unstraightening P)`, by identity functors. -/
def unitStrApp {A : Cat.{v₁, u₁}} {B : SplitOpfibStr.{v₁, u₁, v₂, u₂}.Ob A}
    (P : DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}.Ob B) :
    ((VertFunctor.id DProfStr).obj P : DProfStr.Fiber B) ≅
      (unstraightenStr.comp straightenStr).obj P where
  hom := (unitApp P).hom
  inv := (unitApp P).inv
  hom_inv_id := (unitApp P).hom_inv_id
  inv_hom_id := (unitApp P).inv_hom_id

/-- **The unit** `𝟭 ≅ unstraightenStr ⋙ straightenStr` over `SplitOpfibStr`. -/
def unitStrIso :
    VertFunctor.id DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃} ≅ unstraightenStr.comp straightenStr :=
  VertNatIso.ofComponents (fun P => unitStrApp P) fun _ =>
    NatTrans.ext (funext fun _ => Cat.ext (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)))

/-! ## The counit -/

namespace Counit

variable {A A' : Cat.{v₁, u₁}} {u : A ⟶ A'} {B : Displayed.{v₁, u₁, v₂, u₂} A}
  {B' : Displayed.{v₁, u₁, v₂, u₂} A'} [SplitOpfib B] [SplitOpfib B']
  {H : OpcartesianFunctor u.toFunctor B B'} {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
  {C' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B'} [SplitD2SFib C] [SplitD2SFib C']

/-- The counit commutes with maps of D2SFibs over arbitrary opcartesian functors. -/
theorem map_naturality_str (Φ : D2SFibMap H C C') {a a' : A} {α : a ⟶ a'} {b : B.Ob a}
    {b' : B.Ob a'} {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (Unstraightening (straightenObj C)).Hom g c c') :
    Φ.toObj.map (Counit.map (C := C) θ) =
      Counit.map (C := C') ((unstraightenStrMap (straightenStrMap Φ)).toObj.map θ) :=
  (congrArg Φ.toObj.map (Counit.map_def (C := C) θ)).trans (Counit.map_def (C := C') _).symm

end Counit

/-- The counit at `E`: `unstraightenObj (straightenObj E.C) ≅ E`, by the identity on objects and
`d2sHomEquiv` on morphisms. -/
def counitStrApp {A : Cat.{v₁, u₁}} {B : SplitOpfibStr.{v₁, u₁, v₂, u₂}.Ob A}
    (E : D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃}.Ob B) :
    ((straightenStr.comp unstraightenStr).obj E : D2SFibStr.Fiber B) ≅
      (VertFunctor.id D2SFibStr).obj E where
  hom := (counitApp E).hom
  inv := (counitApp E).inv
  hom_inv_id := (counitApp E).hom_inv_id
  inv_hom_id := (counitApp E).inv_hom_id

/-- **The counit** `straightenStr ⋙ unstraightenStr ≅ 𝟭` over `SplitOpfibStr`. -/
def counitStrIso :
    straightenStr.comp unstraightenStr ≅ VertFunctor.id D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃} :=
  VertNatIso.ofComponents (fun E => counitStrApp E) fun Φ =>
    D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
      (fun θ => heq_of_eq (Counit.map_naturality_str Φ θ).symm))

/-! ## The equivalence -/

/-- **Straightening–unstraightening for D2SFibs over `SplitOpfibStr`**: the unstraightening of
dependent profunctors is an equivalence `DProfStr ≃ D2SFibStr` over `SplitOpfibStr`, with inverse
the straightening. -/
def straighteningEquivStr :
    VertEquivalence DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃} D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃} where
  functor := unstraightenStr
  inverse := straightenStr
  unitIso := unitStrIso
  counitIso := counitStrIso

/-! ## The straightening and unstraightening are cartesian -/

section Pull

variable {A A' : Cat.{v₁, u₁}} {u : A ⟶ A'} {B : Displayed.{v₁, u₁, v₂, u₂} A}
  {B' : Displayed.{v₁, u₁, v₂, u₂} A'} [SplitOpfib B] [SplitOpfib B']
  (H : OpcartesianFunctor u.toFunctor B B') (P' : B'ᵒᵖ.Total ⥤ Cat.{v₃, u₃})

theorem unstraightening_dualOp_total_comp :
    Unstraightening (H.dualOp.total ⋙ P') = (Unstraightening P').reindex H.toDispFunctor :=
  DoubleDisplayed.ext_heq (by kernel_rfl') (by kernel_rfl') (by kernel_rfl') (by kernel_rfl')

theorem unstraightenObj_dualOp_total_comp :
    unstraightenObj (H.dualOp.total ⋙ P') =
      (⟨(Unstraightening P').reindex H.toDispFunctor⟩ : D2SFibCat B) :=
  D2SFibCat.ext (unstraightening_dualOp_total_comp H P')
    (SplitD2SFib.hext (unstraightening_dualOp_total_comp H P') (by kernel_rfl') (by kernel_rfl')
      (by kernel_rfl') (by kernel_rfl'))

end Pull

/-- **The unstraightening is a cartesian functor**: the unstraightening of `H.dualOp.total ⋙ P'`
is the reindexing along `H` of that of `P'`. -/
def unstraightenStrCartesian :
    DDCartesianFunctor DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃} D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃} where
  toPre := { toVertFunctor := unstraightenStr, obj_pull := unstraightenObj_dualOp_total_comp }
  map_clift _ _ := rfl

/-- **The straightening is a cartesian functor**: the straightening of the reindexing of `C'`
along `H` is `H.dualOp.total ⋙ straightenObj C'`. -/
def straightenStrCartesian :
    DDCartesianFunctor D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃} DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃} where
  toPre := { toVertFunctor := straightenStr, obj_pull := fun _ _ => rfl }
  map_clift _ _ := rfl

end DoubleDisplayed.D2SFib.Straightening
