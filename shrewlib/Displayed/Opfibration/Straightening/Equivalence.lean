import Displayed.Opfibration.Straightening.Straighten
import Displayed.Opfibration.Straightening.Unstraighten
import Displayed.Displayed.Equivalence

/-!
# Straightening–unstraightening for split opfibrations

The unstraightening `ICatLax ⟶ SplitOpfibLax` is an equivalence over `Cat`
(`straighteningEquivLax`), with inverse the straightening `straighten`.

The unit `F ≅ straightenObj (∫ F)` is the identity: the fibres of `∫ F` are those of `F`, and its
transport along `f` is `F f` (`unstraightenPushMap`). Its naturality holds by `rfl`: the
straightening of `∫ α` has the components of `α`, and its 2-cells are the factorizations of the
images of the identities, which are the 2-cells of `α`.

The objects of `∫ (straightenObj D)` over `a` are those of `D`, and its morphisms `x ⟶[f] y` are
the vertical morphisms `push f x ⟶ y`. The counit `∫ (straightenObj D) ⟶ D` is the identity on
objects and sends `φ : push f x ⟶ y` to `olift f x ≫ φ`; its inverse sends `χ : x ⟶[f] y` to its
opcartesian factorization. The two composites are identities by `rfl`: a morphism is its chosen
lift followed by its factorization, and the factorization of `olift f x ≫ φ` is `φ`. Its
naturality with respect to a displayed functor `H` is that `H (olift f x)` is the chosen lift
followed by its factorization.
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

/-- **The counit** `unstraighten.obj (straightenObj X) ≅ X`, an isomorphism over `A`. -/
def counitIso : (unstraighten.obj (straightenObj X) : SplitOpfibLax.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl
  inv_hom_id := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Counit

/-- **The counit** `straighten ⋙ unstraighten ≅ 𝟭`. -/
def counitNatIso : straighten.{u} ⋙ᵥ unstraighten ≅ VertFunctor.id SplitOpfibLax.{u} :=
  VertNatIso.ofComponents (fun X => counitIso X) fun {_ _ _ X _} H =>
    DispFunctor.ext (fun _ => rfl) fun {_ _ f x _} φ =>
      heq_of_eq (H.map_comp (f := f) (g := 𝟙 _) (X.toDisplayed.olift f x) φ).symm

/-! ## The unit -/

/-- The unit at `F`: `F ≅ straightenObj (∫ F)`, by identities. -/
def unitIso {A : Cat.{u, u}} (F : ICatLax.Ob A) :
    ((VertFunctor.id ICatLax).obj F : ICatLax.Fiber A) ≅ (unstraighten ⋙ᵥ straighten).obj F where
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
def unitNatIso : VertFunctor.id ICatLax.{u} ≅ unstraighten ⋙ᵥ straighten :=
  VertNatIso.ofComponents (fun F => unitIso F) fun _ =>
    LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening for split opfibrations**: the unstraightening is an
equivalence over `Cat` between `ICatLax` and the split opfibrations, with all displayed functors as
morphisms. -/
def straighteningEquivLax : VertEquivalence ICatLax.{u} SplitOpfibLax.{u} where
  functor := unstraighten
  inverse := straighten
  unitIso := unitNatIso
  counitIso := counitNatIso

/-- The induced equivalence of total categories, over `Cat`. -/
def straighteningEquivLaxTotal : ICatLax.{u}.Total ≌ SplitOpfibLax.{u}.Total :=
  straighteningEquivLax.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivLaxTotal.{u}.functor ⋙ SplitOpfibLax.π = ICatLax.π :=
  rfl

end Displayed.Opfibration.Straightening
