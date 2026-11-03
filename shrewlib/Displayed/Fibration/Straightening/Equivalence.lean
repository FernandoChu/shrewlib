import Displayed.Fibration.Straightening.Straighten
import Displayed.Fibration.Straightening.Unstraighten
import Displayed.Displayed.Equivalence

/-!
# Straightening–unstraightening for split fibrations

The unstraightening `ICatOpLax ⟶ SplitFibLax` is an equivalence over `Cat`
(`straighteningEquivLax`). It is fully faithful (`unstraightenFullyFaithful`), and every split
fibration `D` over `A` is isomorphic over `A` to the unstraightening of its straightening
(`counitIso`), so `VertEquivalence.ofFullyFaithful` assembles the equivalence. Its inverse is the
straightening on objects, and on morphisms the preimage under the unstraightening of the conjugate
by the counit.

The objects of `∫⁻ (straightenObj D)` over `a` are those of `D`, and its morphisms `x ⟶[f] y` are
the vertical morphisms `x ⟶ pull f y`. The counit `∫⁻ (straightenObj D) ⟶ D` is the identity on
objects and sends `φ : x ⟶ pull f y` to `φ ≫ clift f y`; its inverse sends `χ : x ⟶[f] y` to its
cartesian factorization. The two composites are identities by `rfl`: a morphism is its
factorization followed by its chosen lift, and the factorization of `φ ≫ clift f y` is `φ`.

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
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of the counit at `D`: the identity on objects, and a morphism goes to its
cartesian factorization. -/
def counitInv : X ⟶[𝟙 A] unstraighten.obj (straightenObj X) where
  obj x := x
  map {_ _ f x y} χ := (X.toDisplayed.cartesianFactor χ : x ⟶[𝟙 _] X.toDisplayed.pull f y)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The counit** `unstraighten.obj (straightenObj X) ≅ X`, an isomorphism over `A`. -/
def counitIso : (unstraighten.obj (straightenObj X) : SplitFibLax.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl
  inv_hom_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Counit

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening for split fibrations**: the unstraightening is an equivalence
over `Cat` between `ICatOpLax` and the split fibrations, with all displayed functors as morphisms.
-/
def straighteningEquivLax : VertEquivalence ICatOpLax.{u} SplitFibLax.{u} :=
  VertEquivalence.ofFullyFaithful unstraightenFullyFaithful (fun X => straightenObj X)
    (fun X => counitIso X)

/-- The induced equivalence of total categories, over `Cat`. -/
def straighteningEquivLaxTotal : ICatOpLax.{u}.Total ≌ SplitFibLax.{u}.Total :=
  straighteningEquivLax.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivLaxTotal.{u}.functor ⋙ SplitFibLax.π = ICatOpLax.π :=
  rfl

end Displayed.Fibration.Straightening
