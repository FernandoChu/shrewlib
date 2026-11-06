import Displayed.Fibration.Straightening.Straighten
import Displayed.Fibration.Straightening.Unstraighten
import Displayed.Displayed.Equivalence

/-!
# Straightening–unstraightening for split fibrations

The unstraightening `ICatOpLax ⟶ SplitFibLax` is an equivalence over `Cat`
(`straighteningEquivLax`), with inverse the straightening `straighten`.

The unit `F ≅ straightenObj (∫⁻ F)` is the identity: the fibres of `∫⁻ F` are those of `F`, and its
transport along `f` is `F f`. Its naturality holds by `rfl`: the straightening of `∫⁻ α` has the
components of `α`, and its 2-cells are the factorizations of the images of the identities, which
are the 2-cells of `α`.

The objects of `∫⁻ (straightenObj D)` over `a` are those of `D`, and its morphisms `x ⟶[f] y` are
the vertical morphisms `x ⟶ pull f y`. The counit `∫⁻ (straightenObj D) ⟶ D` is the identity on
objects and sends `φ : x ⟶ pull f y` to `φ ≫ clift f y`; its inverse sends `χ : x ⟶[f] y` to its
cartesian factorization. The two composites are identities by `rfl`: a morphism is its
factorization followed by its chosen lift, and the factorization of `φ ≫ clift f y` is `φ`. Its
naturality with respect to a displayed functor `H` is that `H (clift f y)` is its factorization
followed by the chosen lift.

This is the dual of `Opfibration/Straightening/Equivalence.lean`.
-/

universe u

namespace Displayed.Fibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : SplitFibOb A)

/-- The counit at `D`: the identity on objects, and `φ : x ⟶ pull f y` goes to
`φ ≫ clift f y`. -/
def counitHom : unstraighten.obj (straightenObj X) ⟶[𝟙 A] X where
  obj x := (x : X.toDisplayed.Ob _)
  map {_ _ f x y} φ :=
    (X.toDisplayed.comp (f := 𝟙 _) φ (X.toDisplayed.clift f y) : X.toDisplayed.Hom f x y)

/-- The inverse of the counit at `D`: the identity on objects, and a morphism goes to its
cartesian factorization. -/
def counitInv : X ⟶[𝟙 A] unstraighten.obj (straightenObj X) where
  obj x := x
  map {_ _ f x y} χ := (X.toDisplayed.cartesianFactor χ : x ⟶[𝟙 _] X.toDisplayed.pull f y)

/-- **The counit** `unstraighten.obj (straightenObj X) ≅ X`, an isomorphism over `A`. -/
def counitIso : (unstraighten.obj (straightenObj X) : SplitFibLax.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl
  inv_hom_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Counit

/-- **The counit** `straighten ⋙ unstraighten ≅ 𝟭`. -/
def counitNatIso : straighten.{u} ⋙ᵥ unstraighten ≅ VertFunctor.id SplitFibLax.{u} :=
  VertNatIso.ofComponents (fun X => counitIso X) fun {_ _ _ X _} H =>
    DispFunctor.ext (fun _ => rfl) fun {_ _ f _ y} φ =>
      heq_of_eq (H.map_comp (f := 𝟙 _) (g := f) φ (X.toDisplayed.clift f y)).symm

/-! ## The unit -/

/-- The unit at `F`: `F ≅ straightenObj (∫⁻ F)`, by identities. -/
def unitIso {A : Cat.{u, u}} (F : ICatOpLax.Ob A) :
    ((VertFunctor.id ICatOpLax).obj F : ICatOpLax.Fiber A) ≅ (unstraighten ⋙ᵥ straighten).obj F
    where
  hom :=
    { app := fun _ => 𝟭 _
      naturality := fun _ _ => 𝟙 _
      naturality_naturality := fun _ _ _ _ => rfl
      naturality_id := fun _ => rfl
      naturality_comp := fun _ _ _ => rfl }
  inv :=
    { app := fun _ => 𝟭 _
      naturality := fun _ _ => 𝟙 _
      naturality_naturality := fun _ _ _ _ => rfl
      naturality_id := fun _ => rfl
      naturality_comp := fun _ _ _ => rfl }
  hom_inv_id := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)
  inv_hom_id := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-- **The unit** `𝟭 ≅ unstraighten ⋙ straighten`, by identities. -/
def unitNatIso : VertFunctor.id ICatOpLax.{u} ≅ unstraighten ⋙ᵥ straighten :=
  VertNatIso.ofComponents (fun F => unitIso F) fun _ =>
    LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening for split fibrations**: the unstraightening is an equivalence
over `Cat` between `ICatOpLax` and the split fibrations, with all displayed functors as morphisms.
-/
def straighteningEquivLax : VertEquivalence ICatOpLax.{u} SplitFibLax.{u} where
  functor := unstraighten
  inverse := straighten
  unitIso := unitNatIso
  counitIso := counitNatIso

/-- **The unstraightening is fully faithful**, as the functor of an equivalence: displayed
functors between unstraightenings over `u` are lax transformations. -/
def unstraightenFullyFaithful : unstraighten.{u}.FullyFaithful :=
  straighteningEquivLax.fullyFaithful

/-- The induced equivalence of total categories, over `Cat`. -/
def straighteningEquivLaxTotal : ICatOpLax.{u}.Total ≌ SplitFibLax.{u}.Total :=
  straighteningEquivLax.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivLaxTotal.{u}.functor ⋙ SplitFibLax.π = ICatOpLax.π :=
  rfl

end Displayed.Fibration.Straightening
