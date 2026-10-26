import Displayed.Opfibration.Straightening.Straighten
import Displayed.Opfibration.Straightening.Unstraighten
import Displayed.Displayed.Equivalence

/-!
# Straightening–unstraightening for split opfibrations

The unstraightening `ICat ⟶ SplitOpfibCat` is an equivalence over `Cat`
(`straighteningEquiv`). It is fully faithful (`unstraightenFullyFaithful`), and every split
opfibration `D` over `A` is isomorphic over `A` to the unstraightening of its straightening
(`counitIso`), so `VertEquivalence.ofFullyFaithful` assembles the equivalence. Its inverse is the
straightening on objects, and on morphisms the preimage under the unstraightening of the
conjugate by the counit.

The objects of `∫ Str D` over `a` are those of `D`, and its morphisms `x ⟶[f] y` are the vertical
morphisms `push f x ⟶ y`. The counit `∫ Str D ⟶ D` is the identity on objects and sends
`φ : push f x ⟶ y` to `olift f x ≫ φ`; its inverse sends `χ : x ⟶[f] y` to its opcartesian
factorization. The two composites are identities by `rfl`: a morphism is its chosen lift followed
by its factorization, and the factorization of `olift f x ≫ φ` is `φ`.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : SplitOpfibOb A)

/-- The counit at `D`: the identity on objects, and `φ : push f x ⟶ y` goes to
`olift f x ≫ φ`. -/
def counitHom : unstraighten.obj (straightenObj X) ⟶[𝟙 A] X where
  obj x := (x : X.toDisplayed.Ob _)
  map {_ _ f x y} φ := (X.toDisplayed.olift f x ≫ᵈ φ : X.toDisplayed.Hom f x y)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of the counit at `D`: the identity on objects, and a morphism goes to its
opcartesian factorization. -/
def counitInv : X ⟶[𝟙 A] unstraighten.obj (straightenObj X) where
  obj x := x
  map {_ _ f x y} χ := (X.toDisplayed.opcartesianFactor χ : X.toDisplayed.push f x ⟶[𝟙 _] y)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The counit** `Unstr (Str D) ≅ D`, an isomorphism over `A`. -/
def counitIso : (unstraighten.obj (straightenObj X) : SplitOpfibCat.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl
  inv_hom_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Counit

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening for split opfibrations**: the unstraightening is an
equivalence over `Cat` between `ICat` and the split opfibrations, with all displayed functors as
morphisms. -/
def straighteningEquiv : VertEquivalence ICat.{u} SplitOpfibCat.{u} :=
  VertEquivalence.ofFullyFaithful unstraightenFullyFaithful (fun X => straightenObj X)
    (fun X => counitIso X)

/-- The induced equivalence of total categories, over `Cat`. -/
def straighteningEquivTotal : ICat.{u}.Total ≌ SplitOpfibCat.{u}.Total :=
  straighteningEquiv.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivTotal.{u}.functor ⋙ SplitOpfibCat.π = ICat.π :=
  rfl

end Displayed.Opfibration.Straightening
