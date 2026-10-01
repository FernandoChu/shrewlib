import Nfib.Displayed.Functor
import Nfib.Displayed.Opfib
import Nfib.Displayed.Fib

/-!
# Transfer of cleavages along displayed equivalences

A cleavage of a fibration (`Fib`) or of an opfibration (`Opfib`) transfers along an equivalence over
the base, since displayed equivalences preserve (op)cartesian morphisms and these are stable under
vertical isomorphisms.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
  {E : Displayed.{v₁, u₁, v₃, u₃} A}

/-- A cleavage transfers along an equivalence over `A`: the chosen lift at `y` is the image of the
chosen lift at `G y`, followed by the counit. -/
@[instance_reducible]
def DEquivalence.fib (e : DEquivalence D E) [Fib D] : Fib E where
  pull f y := e.functor.obj (D.pull f (e.inverse.obj y))
  clift f y := (e.functor.map (D.clift f (e.inverse.obj y)) ≫ᵈ e.counitIso.app y :)
  clift_cartesian f y :=
    IsCartesian.comp_iso (e.isCartesian_map (D.clift_cartesian f _)) _ (e.counitIso.inv y)
      (e.counitIso.inv_app y) (e.counitIso.app_inv y)

/-- An opcleavage transfers along an equivalence over `A`: the chosen lift at `x` is the inverse
of the counit, followed by the image of the chosen lift at `G x`. -/
@[instance_reducible]
def DEquivalence.opfib (e : DEquivalence D E) [Opfib D] : Opfib E where
  push f x := e.functor.obj (D.push f (e.inverse.obj x))
  olift f x := (e.counitIso.inv x ≫ᵈ e.functor.map (D.olift f (e.inverse.obj x)) :)
  olift_opcartesian f x :=
    IsOpcartesian.iso_comp (e.isOpcartesian_map (D.olift_opcartesian f _)) _ (e.counitIso.app x)
      (e.counitIso.app_inv x) (e.counitIso.inv_app x)

end Displayed

end Nfib
