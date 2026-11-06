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
* The counit `∫ (straightenObj X) ≅ X` is that of the lax equivalence (`counitStrHom`,
  `counitStrInv`): the identity on objects, and `φ ↦ olift f x ≫ φ` on morphisms, with inverse the
  opcartesian factorization. Both preserve the chosen lifts. They are stated with source and target
  `∫ (straightenObj X)` and `X`, so that instance search finds the split opfibrations, and used
  in this form by the straightening of D2SFibs.
-/

universe v₂ u₂ v₁ u₁

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The functors -/

/-- **The unstraightening with strict morphisms**: `F` goes to `∫ F`, and a strict
transformation `τ` to the opcartesian functor `τ.unstraighten`. -/
def unstraightenStr : VertFunctor ICatStr.{v₂, u₂, v₁, u₁} SplitOpfibStr.{v₂, u₂, v₁, u₁} where
  obj F := { toDisplayed := ∫ (F : _ ⥤ Cat.{v₂, u₂}), splitOpfib := unstraightenSplitOpfib F }
  map {_ _ u _ _} τ := StrictTrans.unstraighten (u := u.toFunctor) τ

/-- The unstraightening with strict morphisms is the unstraightening of their underlying lax
data. -/
theorem unstraightenStr_comp_forget :
    unstraightenStr.{v₂, u₂, v₁, u₁} ⋙ᵥ SplitOpfibStr.forget = ICatStr.forget ⋙ᵥ unstraighten :=
  DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-- The straightening of an opcartesian functor `H` over `u`: the strict transformation
`straightenObj X ⟶ u ⋙ straightenObj Y` whose components are `H` on the fibres. -/
def straightenStrMap {A B : Cat.{v₁, u₁}} {u : A ⟶ B} {X : SplitOpfibOb.{v₂, u₂} A}
    {Y : SplitOpfibOb.{v₂, u₂} B}
    (H : OpcartesianFunctor u.toFunctor X.toDisplayed Y.toDisplayed) :
    StrictTrans (straightenObj X) (u.toFunctor ⋙ straightenObj Y) where
  toObj := { obj := fun x => H.toPre.obj x }
  map β := (H.toPre.map β : H.toPre.obj _ ⟶ _)

/-- **The straightening with strict morphisms**: a split opfibration goes to the functor of its
fibres, and an opcartesian functor to the strict transformation of its actions on the fibres. -/
def straightenStr : VertFunctor SplitOpfibStr.{v₂, u₂, v₁, u₁} ICatStr.{v₂, u₂, v₁, u₁} where
  obj X := straightenObj X
  map H := straightenStrMap H

/-- The straightening with strict morphisms is the straightening of their underlying displayed
functors: the 2-cells of the latter are the factorizations of the chosen lifts, which are
identities. -/
theorem straightenStr_comp_forget :
    straightenStr.{v₂, u₂, v₁, u₁} ⋙ᵥ ICatStr.forget = SplitOpfibStr.forget ⋙ᵥ straighten :=
  DispFunctor.ext (fun _ => rfl) fun _ =>
    heq_of_eq (LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl))

/-! ## The unit and counit -/

/-- The unit at `F`: `F ≅ straightenObj (∫ F)`, by identities. -/
def unitStrApp {A : Cat.{v₁, u₁}} (F : ICatStr.{v₂, u₂}.Ob A) :
    ((VertFunctor.id ICatStr).obj F : ICatStr.Fiber A) ≅ (unstraightenStr ⋙ᵥ straightenStr).obj F
 where
  hom :=
    { toObj := { obj := fun x => x }
      map := fun φ => φ }
  inv :=
    { toObj := { obj := fun x => x }
      map := fun φ => φ }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The unit** `𝟭 ≅ unstraightenStr ⋙ straightenStr`, by identities. -/
def unitStrIso : VertFunctor.id ICatStr.{v₂, u₂, v₁, u₁} ≅ unstraightenStr ⋙ᵥ straightenStr :=
  VertNatIso.ofComponents (fun F => unitStrApp F) fun _ =>
    StrictTrans.ext (fun _ => rfl) fun _ => HEq.rfl

/-- The counit at `X`, `∫ (straightenObj X) ⟶ X`: the identity on objects, and
`φ ↦ olift f x ≫ φ` on morphisms. Its source and target are stated as `∫ (straightenObj X)` and
`X`, rather than as the images of `X` under `straightenStr ⋙ unstraightenStr` and the identity, so
that instance search finds their split opfibration structures. -/
def counitStrHom {A : Cat.{v₁, u₁}} (X : SplitOpfibOb.{v₂, u₂} A) :
    OpcartesianFunctor (𝟙 A : A ⟶ A).toFunctor (∫ (straightenObj X)) X.toDisplayed where
  toPre :=
    { obj := fun x => x
      map := fun {_ _ f x _} φ => (X.toDisplayed.olift f x ≫ᵈ φ : X.toDisplayed.Hom f x _) }

/-- The inverse of the counit at `X`, `X ⟶ ∫ (straightenObj X)`: the identity on objects, and the
opcartesian factorization on morphisms. -/
def counitStrInv {A : Cat.{v₁, u₁}} (X : SplitOpfibOb.{v₂, u₂} A) :
    OpcartesianFunctor (𝟙 A : A ⟶ A).toFunctor X.toDisplayed (∫ (straightenObj X)) where
  toPre :=
    { obj := fun x => x
      map := fun {_ _ f x _} χ =>
        (X.toDisplayed.opcartesianFactor χ : X.toDisplayed.push f x ⟶[𝟙 _] _) }

/-- The counit at `X`, as an isomorphism of `SplitOpfibStr.Fiber A`: `counitStrHom` and
`counitStrInv`. -/
def counitStrApp {A : Cat.{v₁, u₁}} (X : SplitOpfibStr.{v₂, u₂}.Ob A) :
    ((straightenStr ⋙ᵥ unstraightenStr).obj X : SplitOpfibStr.Fiber A) ≅
      (VertFunctor.id SplitOpfibStr).obj X where
  hom := counitStrHom X
  inv := counitStrInv X
  hom_inv_id := OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)
  inv_hom_id := OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)

/-- **The counit** `straightenStr ⋙ unstraightenStr ≅ 𝟭`. -/
def counitStrIso :
    straightenStr ⋙ᵥ unstraightenStr ≅ VertFunctor.id SplitOpfibStr.{v₂, u₂, v₁, u₁} :=
  VertNatIso.ofComponents (fun X => counitStrApp X) fun {_ _ _ X _} H =>
    OpcartesianFunctor.ext (DispFunctor.ext (fun _ => rfl) fun {_ _ f x _} φ =>
      heq_of_eq (H.toPre.map_comp (f := f) (g := 𝟙 _) (X.toDisplayed.olift f x) φ).symm)

/-! ## The equivalence -/

/-- **Straightening–unstraightening for split opfibrations, with strict morphisms**: the
unstraightening is an equivalence over `Cat` between `ICatStr` and `SplitOpfibStr`. -/
def straighteningEquivStr :
    VertEquivalence ICatStr.{v₂, u₂, v₁, u₁} SplitOpfibStr.{v₂, u₂, v₁, u₁} where
  functor := unstraightenStr
  inverse := straightenStr
  unitIso := unitStrIso
  counitIso := counitStrIso

end Displayed.Opfibration.Straightening
