import Displayed.Discrete.Straightening.Straighten
import Displayed.Discrete.Straightening.Unstraighten
import Displayed.Opfibration.Straightening.Equivalence

/-!
# Straightening–unstraightening for discrete opfibrations

The unstraightening `IDisc ⟶ DiscOpfibCat` is an equivalence over `Cat` (`straighteningEquiv`),
with inverse the straightening `straighten`.

Everything is that of the split opfibrations (`Opfibration/Straightening`), restricted to the
discrete ones: the counit is the identity on objects and sends `φ : push f x ⟶ y` to
`olift f x ≫ φ`, and its inverse sends a morphism to its opcartesian factorization. In the other
direction, straightening undoes unstraightening on the nose (`straightenObj_unstraightenObj`), so
the unit is the identity.
-/

universe v₂ u₂ v₁ u₁

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The counit -/

section Counit

variable {A : Cat.{v₁, u₁}} (X : DiscOpfibOb.{v₂, u₂} A)

/-- The counit at `X`: that of `X` as a split opfibration. -/
def counitHom : unstraighten.obj (straightenObj X) ⟶[𝟙 A] X :=
  Opfibration.Straightening.counitHom (DiscOpfibCat.forget.obj X)

/-- The inverse of the counit at `X`: that of `X` as a split opfibration. -/
def counitInv : X ⟶[𝟙 A] unstraighten.obj (straightenObj X) :=
  Opfibration.Straightening.counitInv (DiscOpfibCat.forget.obj X)

/-- **The counit** `unstraighten.obj (straightenObj X) ≅ X`, an isomorphism over `A`. -/
def counitIso : (unstraighten.obj (straightenObj X) : DiscOpfibCat.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl
  inv_hom_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Counit

/-- **The counit** `straighten ⋙ unstraighten ≅ 𝟭`. -/
def counitNatIso :
    straighten.{v₂, u₂, v₁, u₁} ⋙ᵥ unstraighten ≅ VertFunctor.id DiscOpfibCat.{v₂, u₂, v₁, u₁} :=
  VertNatIso.ofComponents (fun X => counitIso X) fun {_ _ _ X _} H =>
    DispFunctor.ext (fun _ => rfl) fun {_ _ f x _} φ =>
      heq_of_eq (H.map_comp (f := f) (g := 𝟙 _) (X.toDisplayed.olift f x) φ).symm

/-! ## Straightening–unstraightening -/

/-- Straightening undoes unstraightening on the nose: the fibres of `∫ X` are the values of `X`,
and its pushforwards are those of `X`. -/
theorem straightenObj_unstraightenObj {A : Cat.{v₁, u₁}} (X : IDiscOb.{v₂, u₂} A) :
    straightenObj (unstraightenObj X) = X :=
  rfl

/-- **Straightening–unstraightening for discrete opfibrations**: the unstraightening is an
equivalence over `Cat` between the functors into discrete categories and the discrete
opfibrations. -/
def straighteningEquiv : VertEquivalence IDisc.{v₂, u₂, v₁, u₁} DiscOpfibCat.{v₂, u₂, v₁, u₁} where
  functor := unstraighten
  inverse := straighten
  unitIso := VertNatIso.ofComponents (fun X => Iso.refl X) fun _ =>
    Opfibration.Straightening.LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl)
      (fun _ _ => HEq.rfl)
  counitIso := counitNatIso

/-- **The unstraightening is fully faithful**, as the functor of an equivalence: displayed
functors between unstraightenings over `u` are lax transformations. -/
def unstraightenFullyFaithful : unstraighten.{v₂, u₂, v₁, u₁}.FullyFaithful :=
  straighteningEquiv.fullyFaithful

end Displayed.Discrete.Straightening
