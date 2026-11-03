import Displayed.Opfibration.Straightening.ICatStr
import Displayed.Opfibration.SplitOpfibStr
import Displayed.Opfibration.Straightening.Equivalence

/-!
# Straightening–unstraightening for split opfibrations, with strict morphisms

The unstraightening restricts to an equivalence over `Cat` between `ICatStr`, the functors into
`Cat` and strict transformations, and `SplitOpfibStr`, the split opfibrations and opcartesian
functors (`straighteningEquivStr`).

* `unstraightenStr` sends `F` to `∫ F`, and a strict transformation `τ` to its unstraightening
  `τ.unstraighten`. It is `unstraighten` on the underlying lax data
  (`unstraightenStr_comp_forget`).
* `straightenStr` sends a split opfibration to the functor of its fibres (`straightenObj`), and an
  opcartesian functor `H` to the strict transformation whose components are `H` on the fibres:
  `H` commutes with the pushforward functors on the nose, by the rules of opcartesian functors. It
  is `straighten` on the underlying displayed functors (`straightenStr_comp_forget`).
* The unit `F ≅ straightenObj (∫ F)` is the identity, since the fibres of `∫ F` are those of `F`
  and its transport is `F`, by `unstraightenPushMap`.
* The counit `∫ (straightenObj X) ≅ X` is that of the lax equivalence (`counitHom`, `counitInv`):
  the identity on objects, and `φ ↦ olift f x ≫ φ` on morphisms, with inverse the opcartesian
  factorization. Both preserve the chosen lifts.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The functors -/

/-- **The unstraightening with strict morphisms**: `F` goes to `∫ F`, and a strict
transformation `τ` to the opcartesian functor `τ.unstraighten`. -/
def unstraightenStr : VertFunctor ICatStr.{u} SplitOpfibStr.{u} where
  obj F := { toDisplayed := ∫ (F : _ ⥤ Cat.{u, u}), splitOpfib := unstraightenSplitOpfib F }
  map {_ _ u _ _} τ := StrictTrans.unstraighten (u := u.toFunctor) τ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unstraightening with strict morphisms is the unstraightening of their underlying lax
data. -/
theorem unstraightenStr_comp_forget :
    unstraightenStr.{u} ⋙ᵥ SplitOpfibStr.forget = ICatStr.forget ⋙ᵥ unstraighten :=
  DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-- The straightening of an opcartesian functor `H` over `u`: the strict transformation
`straightenObj X ⟶ u ⋙ straightenObj Y` whose components are `H` on the fibres. -/
def straightenStrMap {A B : Cat.{u, u}} {u : A ⟶ B} {X : SplitOpfibOb A} {Y : SplitOpfibOb B}
    (H : OpcartesianFunctor u.toFunctor X.toDisplayed Y.toDisplayed) :
    StrictTrans (straightenObj X) (u.toFunctor ⋙ straightenObj Y) where
  toObj := { obj := fun x => H.toPre.obj x, obj_push := fun _ _ => rfl }
  map β := (H.toPre.map β : H.toPre.obj _ ⟶ _)
  map_id _ := rfl
  map_comp _ _ := rfl
  map_push _ _ _ _ := rfl

/-- **The straightening with strict morphisms**: a split opfibration goes to the functor of its
fibres, and an opcartesian functor to the strict transformation of its actions on the fibres. -/
def straightenStr : VertFunctor SplitOpfibStr.{u} ICatStr.{u} where
  obj X := straightenObj X
  map H := straightenStrMap H
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The straightening with strict morphisms is the straightening of their underlying displayed
functors: the 2-cells of the latter are the factorizations of the chosen lifts, which are
identities. -/
theorem straightenStr_comp_forget :
    straightenStr.{u} ⋙ᵥ ICatStr.forget = SplitOpfibStr.forget ⋙ᵥ straighten :=
  DispFunctor.ext (fun _ => rfl) fun _ =>
    heq_of_eq (LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl))

/-! ## The unit and counit -/

/-- The unit at `F`: `F ≅ straightenObj (∫ F)`, by identities. -/
def unitStrApp {A : Cat.{u, u}} (F : ICatStr.Ob A) :
    ((VertFunctor.id ICatStr).obj F : ICatStr.Fiber A) ≅ (unstraightenStr ⋙ᵥ straightenStr).obj F
    where
  hom :=
    { toObj := { obj := fun x => x, obj_push := fun _ _ => rfl }
      map := fun φ => φ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
      map_push := fun _ _ _ _ => rfl }
  inv :=
    { toObj := { obj := fun x => x, obj_push := fun _ _ => rfl }
      map := fun φ => φ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
      map_push := fun _ _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The unit** `𝟭 ≅ unstraightenStr ⋙ straightenStr`, by identities. -/
def unitStrIso : VertFunctor.id ICatStr.{u} ≅ unstraightenStr ⋙ᵥ straightenStr :=
  VertNatIso.ofComponents (fun F => unitStrApp F) fun _ =>
    StrictTrans.ext (fun _ => rfl) fun _ => HEq.rfl

/-- The counit at `X`, as opcartesian functors: `counitHom` and `counitInv`. -/
def counitStrApp {A : Cat.{u, u}} (X : SplitOpfibStr.Ob A) :
    ((straightenStr ⋙ᵥ unstraightenStr).obj X : SplitOpfibStr.Fiber A) ≅
      (VertFunctor.id SplitOpfibStr).obj X where
  hom :=
    { toPre :=
        { obj := fun x => x
          map := fun {_ _ f x _} φ => (X.toDisplayed.olift f x ≫ᵈ φ : X.toDisplayed.Hom f x _)
          map_id := fun _ => rfl
          map_comp := fun _ _ => rfl
          obj_push := fun _ _ => rfl }
      map_olift _ _ := rfl }
  inv :=
    { toPre :=
        { obj := fun x => x
          map := fun {_ _ f x _} χ =>
            (X.toDisplayed.opcartesianFactor χ : X.toDisplayed.push f x ⟶[𝟙 _] _)
          map_id := fun _ => rfl
          map_comp := fun _ _ => rfl
          obj_push := fun _ _ => rfl }
      map_olift _ _ := rfl }
  hom_inv_id := OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)
  inv_hom_id := OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)

/-- **The counit** `straightenStr ⋙ unstraightenStr ≅ 𝟭`. -/
def counitStrIso : straightenStr ⋙ᵥ unstraightenStr ≅ VertFunctor.id SplitOpfibStr.{u} :=
  VertNatIso.ofComponents (fun X => counitStrApp X) fun {_ _ _ X _} H =>
    OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun {_ _ f x _} φ =>
      heq_of_eq (H.toPre.map_comp (f := f) (g := 𝟙 _) (X.toDisplayed.olift f x) φ).symm)

/-! ## The equivalence -/

/-- **Straightening–unstraightening for split opfibrations, with strict morphisms**: the
unstraightening is an equivalence over `Cat` between `ICatStr` and `SplitOpfibStr`. -/
def straighteningEquivStr : VertEquivalence ICatStr.{u} SplitOpfibStr.{u} where
  functor := unstraightenStr
  inverse := straightenStr
  unitIso := unitStrIso
  counitIso := counitStrIso

end Displayed.Opfibration.Straightening
