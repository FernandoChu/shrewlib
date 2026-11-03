import DoubleDisplayed.D2SFib.Fibred.Unstraighten
import DoubleDisplayed.D2SFib.Fibred.Straighten
import DoubleDisplayed.D2SFib.Straightening.Equivalence
import DoubleDisplayed.Equivalence

/-!
# Straightening–unstraightening for D2SFibs, over `ICatStr`

The unstraightening of dependent profunctors extends to an equivalence `DProf ≃ D2SFibDisp` over
`ICatStr` (`straighteningEquiv`), whose functors are `unstraighten` and `straighten`: dependent
profunctors are the same as split D2SFibs, naturally in the indexed category they lie over.

The unit and counit are given explicitly, by the components of the equivalence over a single `F`
(`D2SFib/Straightening/Equivalence.lean`):

* the unit `𝟭 ≅ unstraighten ⋙ straighten` at `P` is the identity on each `P ⟨a, x⟩`, which is the
  fiber of `Unstraightening P` over `x` on the nose (`unitApp`);
* the counit `straighten ⋙ unstraighten ≅ 𝟭` at `C` is the identity on objects, and on morphisms
  composes the vertical morphism `push α c ⟶ pull (opcartesianFactor g) c'` that a morphism of
  `Unstraightening (straightenObj C)` over `g` is with the chosen lifts (`counitApp`).

Their naturality in `A` and `F` is their naturality with respect to the morphisms over arbitrary
strict transformations, which holds by `rfl` for the unit, and for the counit since a map of
D2SFibs preserves the chosen lifts (`Counit.map_naturality`).
-/

universe u

namespace DoubleDisplayed.D2SFib.Fibred

open CategoryTheory Displayed DoubleDisplayed D2SFib Displayed.Opfibration.Straightening
  DoubleDisplayed.D2SFib.Straightening

open scoped Displayed DoubleDisplayed

/-! ## The unit -/

/-- The unit at `P`: `P ≅ straightenObj (Unstraightening P)`, by identity functors. -/
def unitIsoApp {A : Cat.{u, u}} {F : ICatStr.Ob A} (P : DProf.Ob F) :
    ((VertFunctor.id DProf).obj P : DProf.Fiber F) ≅ (unstraighten.comp straighten).obj P where
  hom := (unitApp P).hom
  inv := (unitApp P).inv
  hom_inv_id := (unitApp P).hom_inv_id
  inv_hom_id := (unitApp P).inv_hom_id

/-- **The unit** `𝟭 ≅ unstraighten ⋙ straighten` over `ICatStr`. -/
def unitIso : VertFunctor.id DProf.{u} ≅ unstraighten.comp straighten :=
  VertNatIso.ofComponents (fun P => unitIsoApp P) fun _ =>
    NatTrans.ext (funext fun _ => Cat.ext (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)))

/-! ## The counit -/

namespace Counit

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}}
  {τ : StrictTrans F (u.toFunctor ⋙ G)} {C : DoubleDisplayed.{u, u, u, u, u, u} (∫ F)}
  {C' : DoubleDisplayed.{u, u, u, u, u, u} (∫ G)} [SplitD2SFib C] [SplitD2SFib C']

/-- The counit commutes with maps of D2SFibs over arbitrary strict transformations. -/
theorem map_naturality (Φ : D2SFibMap τ.unstraighten C C') {a a' : A} {α : a ⟶ a'}
    {b : F.obj a} {b' : F.obj a'} {g : (∫ F).Hom α b b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (Unstraightening (straightenObj C)).Hom g c c') :
    Φ.toObj.map (Straightening.Counit.map (C := C) θ) =
      Straightening.Counit.map (C := C') ((unstraightenMap (straightenMap Φ)).toObj.map θ) :=
  (congrArg Φ.toObj.map (Straightening.Counit.map_def (C := C) θ)).trans
    (Straightening.Counit.map_def (C := C') _).symm

end Counit

/-- The counit at `E`: `unstraightenObj (straightenObj E.C) ≅ E`, by the identity on objects and
`d2sHomEquiv` on morphisms. -/
def counitIsoApp {A : Cat.{u, u}} {F : ICatStr.Ob A} (E : D2SFibDisp.Ob F) :
    ((straighten.comp unstraighten).obj E : D2SFibDisp.Fiber F) ≅ (VertFunctor.id D2SFibDisp).obj E
    where
  hom := (counitApp E).hom
  inv := (counitApp E).inv
  hom_inv_id := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Straightening.Counit.invMap_map (C := E.C) θ)))
  inv_hom_id := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Straightening.Counit.map_invMap (C := E.C) θ)))

/-- **The counit** `straighten ⋙ unstraighten ≅ 𝟭` over `ICatStr`. -/
def counitIso : straighten.comp unstraighten ≅ VertFunctor.id D2SFibDisp.{u} :=
  VertNatIso.ofComponents (fun E => counitIsoApp E) fun Φ =>
    D2SFibMap.ext (DDFunctor.ext (fun _ => rfl)
      (fun θ => heq_of_eq (Counit.map_naturality Φ θ).symm))

/-! ## The equivalence -/

/-- **Straightening–unstraightening for D2SFibs over `ICatStr`**: the unstraightening of
dependent profunctors is an equivalence `DProf ≃ D2SFibDisp` over `ICatStr`, with inverse the
straightening. -/
def straighteningEquiv : VertEquivalence DProf.{u} D2SFibDisp.{u} where
  functor := unstraighten
  inverse := straighten
  unitIso := unitIso
  counitIso := counitIso

end DoubleDisplayed.D2SFib.Fibred
