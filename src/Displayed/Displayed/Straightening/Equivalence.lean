import Displayed.Displayed.Straightening.Straighten
import Displayed.Displayed.Straightening.Unstraighten
import Displayed.Fibration.Basic

/-!
# Straightening–unstraightening for displayed categories

Straightening–unstraightening: `(▷ᵈ)* : DCat → Cat^→` is part of an equivalence over `Cat`, in the
displayed sense (`straighteningEquiv : VertEquivalence DCat (cod Cat)`): the unit and counit are
vertical, i.e. their components lie over identities of `Cat`. Consequently:

* the equivalence of total categories `DCat.Total ≌ (cod Cat).Total` commutes with the projections
  to `Cat` (`straighteningEquiv_total`);
* both `DCat` and `Cat^→` are fibrations over `Cat`: `DCat` is a `SplitFib` by pullback, and
  `Cat^→` gets a `Fib` instance from it by transfer along the equivalence;
* both functors preserve cartesian morphisms (`isCartesianUnstraightenMap`,
  `isCartesianStraightenMap`).

The unit `F ⟶ Str (Unstr F)` sends `x` to `⟨(a, x), rfl⟩`, and its inverse transports along the
equation `X.base = a` of an object of the fibre. The counit `Unstr (Str p) ⟶ p` forgets the base
component, and its inverse sends `e` to `(p e, ⟨e, rfl⟩)`. Their naturality holds by `rfl`.
-/

universe u

namespace Displayed.Straightening

open CategoryTheory Bicategory Displayed Unstraightening

open scoped Displayed

/-! ## The unit -/

section Unit

variable {A : Cat.{u, u}} (F : LaxNormal A)

/-- The unit at `F`: `x ↦ ⟨(a, x), rfl⟩`. -/
def unitHom : ReprHom (𝟙 A) F (straightenObj (unstraightenObj F)) where
  obj {a} x := ⟨⟨a, x⟩, rfl⟩
  map {_ _ f _ _} s := ⟨⟨f, s⟩, rfl⟩
  map_id _ := rfl
  map_mul _ _ := rfl

/-- The inverse of the unit on objects: transport along `X.base = a`. -/
def unitInvObj : ∀ {a : A}, Fibre (unstraightenObj F) a → F.obj ⟨a⟩
  | _, ⟨⟨_, x⟩, rfl⟩ => x

/-- The inverse of the unit on morphisms. -/
def unitInvMap : ∀ {a a' : A} {f : a ⟶ a'} {x : Fibre (unstraightenObj F) a}
    {y : Fibre (unstraightenObj F) a'}, FibreHom (unstraightenObj F) f x y →
      (prof F f).obj (unitInvObj F x) (unitInvObj F y)
  | _, _, f, ⟨⟨_, _⟩, rfl⟩, ⟨⟨_, _⟩, rfl⟩, ⟨⟨g, s⟩, hg⟩ => (show g = f from hg) ▸ s

/-- The inverse of the unit at `F`. -/
def unitInv : ReprHom (𝟙 A) (straightenObj (unstraightenObj F)) F where
  obj x := unitInvObj F x
  map s := unitInvMap F s
  map_id := by
    rintro a ⟨⟨b, _⟩, h⟩
    obtain rfl : b = a := h
    rfl
  map_mul := by
    rintro a a' a'' f g ⟨⟨b, _⟩, hx⟩ ⟨⟨b', _⟩, hy⟩ ⟨⟨b'', _⟩, hz⟩ ⟨⟨_, s⟩, hs⟩ ⟨⟨_, t⟩, ht⟩
    obtain rfl : b = a := hx
    obtain rfl : b' = a' := hy
    obtain rfl : b'' = a'' := hz
    obtain rfl : _ = f := hs
    obtain rfl : _ = g := ht
    rfl

theorem unitHom_unitInv :
    (DCat.comp (unitHom F) (unitInv F) : DCat.Hom (𝟙 A) F F) = DCat.id F :=
  rfl

theorem unitInv_unitHom :
    (DCat.comp (unitInv F) (unitHom F) : DCat.Hom (𝟙 A) _ _) =
      DCat.id (straightenObj (unstraightenObj F)) := by
  refine ReprHom.ext (fun a x => ?_) ?_
  · obtain ⟨⟨b, _⟩, h⟩ := x
    obtain rfl : b = a := h
    rfl
  rintro a a' f ⟨⟨b, _⟩, hx⟩ ⟨⟨b', _⟩, hy⟩ ⟨⟨_, s⟩, hs⟩
  obtain rfl : b = a := hx
  obtain rfl : b' = a' := hy
  obtain rfl : _ = f := hs
  rfl

end Unit

/-- **The unit** `𝟭 ≅ Str ∘ Unstr`, vertical over `Cat`. -/
def unitIso : VertFunctor.id DCat.{u} ≅ unstraighten.comp straighten :=
  VertNatIso.ofComponents
    (fun F => ⟨unitHom F, unitInv F, unitHom_unitInv F, unitInv_unitHom F⟩) (fun _ => rfl)

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : (cod Cat.{u, u}).Ob A)

/-- The counit at `p : E ⥤ A`, as a functor: forget the base component. -/
def counitFunctor : Unstraightening (straightenObj X) ⥤ X.dom where
  obj Y := Y.fiber.1
  map g := g.fiber.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of the counit, as a functor: `e ↦ (p e, ⟨e, rfl⟩)`. -/
def counitInvFunctor : X.dom ⥤ Unstraightening (straightenObj X) where
  obj e := ⟨X.hom.toFunctor.obj e, ⟨e, rfl⟩⟩
  map g := ⟨X.hom.toFunctor.map g, ⟨g, rfl⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The counit at `p`. -/
def counitHom : (cod Cat.{u, u}).Hom (𝟙 A) (unstraightenObj (straightenObj X)) X :=
  ⟨(counitFunctor X).toCatHom,
    Cat.Hom.ext (CategoryTheory.Functor.ext (fun Y => Y.fiber.2)
      (fun _ _ g => FibreHom.proj_map g.fiber))⟩

/-- The inverse of the counit at `p`. -/
def counitInv : (cod Cat.{u, u}).Hom (𝟙 A) X (unstraightenObj (straightenObj X)) :=
  ⟨(counitInvFunctor X).toCatHom, rfl⟩

theorem counitHom_counitInv :
    ((cod Cat.{u, u}).comp (counitHom X) (counitInv X) : (cod Cat.{u, u}).Hom (𝟙 A) _ _) =
      (cod Cat.{u, u}).id (unstraightenObj (straightenObj X)) := by
  refine CodHom.ext (Cat.Hom.ext (Functor.hext (fun Y => ?_) ?_))
  · obtain ⟨a, _, h⟩ := Y
    obtain rfl : _ = a := h
    rfl
  rintro ⟨a, _, hx⟩ ⟨a', _, hy⟩ ⟨gb, g, hg⟩
  obtain rfl : _ = a := hx
  obtain rfl : _ = a' := hy
  have e : gb = X.hom.toFunctor.map g := hg.symm
  subst e
  rfl

theorem counitInv_counitHom :
    ((cod Cat.{u, u}).comp (counitInv X) (counitHom X) : (cod Cat.{u, u}).Hom (𝟙 A) X X) =
      (cod Cat.{u, u}).id X :=
  rfl

end Counit

/-- **The counit** `Unstr ∘ Str ≅ 𝟭`, vertical over `Cat`. -/
def counitIso : straighten.comp unstraighten ≅ VertFunctor.id (cod Cat.{u, u}) :=
  VertNatIso.ofComponents
    (fun X => ⟨counitHom X, counitInv X, counitHom_counitInv X, counitInv_counitHom X⟩)
    (fun _ => rfl)

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening**: `(▷ᵈ)* : DCat → Cat^→` is an equivalence
over `Cat`, with inverse the straightening. -/
def straighteningEquiv : VertEquivalence DCat.{u} (cod Cat.{u, u}) where
  functor := unstraighten
  inverse := straighten
  unitIso := unitIso
  counitIso := counitIso

/-- The induced equivalence `DCat ≌ Cat^→` of total categories. It commutes with the projections
to `Cat` (`straighteningEquiv_total_functor_comp_π`). -/
def straighteningEquivTotal : DCat.{u}.Total ≌ (cod Cat.{u, u}).Total :=
  straighteningEquiv.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivTotal.{u}.functor ⋙ (cod Cat.{u, u}).π = DCat.π :=
  rfl

/-- **`Cat^→` is a fibration over `Cat`**, with the cleavage transferred from `DCat` along the
equivalence. -/
instance fibCodCat : Fib (cod Cat.{u, u}) :=
  straighteningEquiv.fib

/-- **`(▷ᵈ)*` preserves cartesian morphisms.** -/
def isCartesianUnstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A}
    {G : LaxNormal B} {φ : DCat.Hom u F G} (H : IsCartesian (D := DCat) φ) :
    IsCartesian (D := cod Cat.{u, u}) (unstraighten.map φ) :=
  straighteningEquiv.isCartesianMap H

/-- **The straightening preserves cartesian morphisms.** -/
def isCartesianStraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {X : (cod Cat.{u, u}).Ob A}
    {Y : (cod Cat.{u, u}).Ob B}
    {w : (cod Cat.{u, u}).Hom u X Y} (H : IsCartesian (D := cod Cat.{u, u}) w) :
    IsCartesian (D := DCat) (straighten.map w) :=
  straighteningEquiv.symm.isCartesianMap H

end Displayed.Straightening
