import Displayed.Discrete.Straightening.Straighten
import Displayed.Discrete.Straightening.Unstraighten
import Displayed.Opfibration.Straightening.Equivalence

/-!
# Straightening–unstraightening for discrete opfibrations

The unstraightening `IDisc ⟶ DiscOpfibCat` is an equivalence over `Cat` (`straighteningEquiv`). It
is fully faithful (`unstraightenFullyFaithful`), and every discrete opfibration `X` over `A` is
isomorphic over `A` to the unstraightening of its straightening (`counitIso`), so
`VertEquivalence.ofFullyFaithful` assembles the equivalence.

Everything is that of the split opfibrations (`Opfibration/Straightening`), restricted to the
discrete ones: the counit is the identity on objects and sends `φ : push f x ⟶ y` to
`olift f x ≫ φ`, and its inverse sends a morphism to its opcartesian factorization. In the other
direction, straightening undoes unstraightening on the nose (`straightenObj_unstraightenObj`).
-/

universe u

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : DiscOpfibOb A)

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

/-! ## Straightening–unstraightening -/

/-- Straightening undoes unstraightening on the nose: the fibres of `∫ X` are the values of `X`,
and its pushforwards are those of `X`. -/
theorem straightenObj_unstraightenObj {A : Cat.{u, u}} (X : IDiscOb.{u} A) :
    straightenObj (unstraightenObj X) = X :=
  rfl

/-- **Straightening–unstraightening for discrete opfibrations**: the unstraightening is an
equivalence over `Cat` between the functors into discrete categories and the discrete
opfibrations. -/
def straighteningEquiv : VertEquivalence IDisc.{u} DiscOpfibCat.{u} :=
  VertEquivalence.ofFullyFaithful unstraightenFullyFaithful (fun X => straightenObj X)
    (fun X => counitIso X)

end Displayed.Discrete.Straightening
