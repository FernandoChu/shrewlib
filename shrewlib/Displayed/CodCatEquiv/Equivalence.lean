import Displayed.CodCatEquiv.Total
import Displayed.CodCatEquiv.Fibres

/-!
# Displayed categories over `A` are the functors into `A`

`DisplayedCat` and `cod Cat` are equivalent over `Cat` (`DisplayedCat.codEquiv`), by taking total
categories (`DisplayedCat.total`), with inverse taking fibres (`DisplayedCat.fibresFunctor`). In
particular, taking total categories is fully faithful (`DisplayedCat.totalFullyFaithful`).

The unit `D ⟶ fibres (total D)` sends `x` to `⟨⟨a, x⟩, rfl⟩`, and its inverse transports along the
equation `e.1 = a` of an object of the fibre. The counit `total (fibres X) ⟶ X` forgets the base
component, and its inverse sends `e` to `⟨p e, ⟨e, rfl⟩⟩`. Their naturality holds by `rfl`.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

namespace DisplayedCat

namespace CodEquiv

/-! ## The unit -/

section Unit

variable {A : Cat.{u, u}} (D : Displayed.{u, u, u, u} A)

/-- The unit at `D`: `x ↦ ⟨⟨a, x⟩, rfl⟩`. -/
def unitHom : DisplayedCat.Hom (𝟙 A) D (fibres (totalObj D)) where
  obj {a} x := ⟨⟨a, x⟩, rfl⟩
  map {_ _ f _ _} φ := ⟨⟨f, φ⟩, rfl⟩

/-- The inverse of the unit on objects: transport along `e.1 = a`. -/
def unitInvObj : ∀ {a : A}, Fibre (totalObj D) a → D.Ob a
  | _, ⟨⟨_, x⟩, rfl⟩ => x

/-- The inverse of the unit on morphisms. -/
def unitInvMap : ∀ {a a' : A} {f : a ⟶ a'} {x : Fibre (totalObj D) a}
    {y : Fibre (totalObj D) a'}, FibreHom (totalObj D) f x y →
      (unitInvObj D x ⟶[f] unitInvObj D y)
  | _, _, f, ⟨⟨_, _⟩, rfl⟩, ⟨⟨_, _⟩, rfl⟩, ⟨⟨g, φ⟩, hg⟩ => (show g = f from hg) ▸ φ

/-- The inverse of the unit at `D`. -/
def unitInv : DisplayedCat.Hom (𝟙 A) (fibres (totalObj D)) D where
  obj x := unitInvObj D x
  map s := unitInvMap D s
  map_id := by
    rintro a ⟨⟨b, _⟩, h⟩
    obtain rfl : b = a := h
    rfl
  map_comp := by
    rintro a a' a'' f g ⟨⟨b, _⟩, hx⟩ ⟨⟨b', _⟩, hy⟩ ⟨⟨b'', _⟩, hz⟩ ⟨⟨_, s⟩, hs⟩ ⟨⟨_, t⟩, ht⟩
    obtain rfl : b = a := hx
    obtain rfl : b' = a' := hy
    obtain rfl : b'' = a'' := hz
    obtain rfl : _ = f := hs
    obtain rfl : _ = g := ht
    rfl

theorem unitHom_unitInv :
    (DisplayedCat.comp (unitHom D) (unitInv D) : DisplayedCat.Hom (𝟙 A) D D) =
      DisplayedCat.id D :=
  rfl

theorem unitInv_unitHom :
    (DisplayedCat.comp (unitInv D) (unitHom D) : DisplayedCat.Hom (𝟙 A) _ _) =
      DisplayedCat.id (fibres (totalObj D)) := by
  refine DispFunctor.ext (fun {a} x => ?_) (fun {a a' f x y} s => ?_)
  · obtain ⟨⟨b, _⟩, h⟩ := x
    obtain rfl : b = a := h
    rfl
  obtain ⟨⟨b, _⟩, hx⟩ := x
  obtain ⟨⟨b', _⟩, hy⟩ := y
  obtain rfl : b = a := hx
  obtain rfl : b' = a' := hy
  obtain ⟨⟨_, s⟩, hs⟩ := s
  obtain rfl : _ = f := hs
  rfl

end Unit

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : (cod Cat.{u, u}).Ob A)

/-- The counit at `p : E ⥤ A`, as a functor: forget the base component. -/
def counitFunctor : (fibres X).Total ⥤ X.dom where
  obj Y := Y.2.1
  map g := g.fiber.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of the counit, as a functor: `e ↦ ⟨p e, ⟨e, rfl⟩⟩`. -/
def counitInvFunctor : X.dom ⥤ (fibres X).Total where
  obj e := ⟨X.hom.toFunctor.obj e, ⟨e, rfl⟩⟩
  map g := ⟨X.hom.toFunctor.map g, ⟨g, rfl⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The counit at `p`. -/
def counitHom : (cod Cat.{u, u}).Hom (𝟙 A) (totalObj (fibres X)) X :=
  ⟨(counitFunctor X).toCatHom,
    Cat.Hom.ext (CategoryTheory.Functor.ext (fun Y => Y.2.2)
      (fun _ _ g => FibreHom.proj_map g.fiber))⟩

/-- The inverse of the counit at `p`. -/
def counitInv : (cod Cat.{u, u}).Hom (𝟙 A) X (totalObj (fibres X)) :=
  ⟨(counitInvFunctor X).toCatHom, rfl⟩

theorem counitHom_counitInv :
    ((cod Cat.{u, u}).comp (counitHom X) (counitInv X) : (cod Cat.{u, u}).Hom (𝟙 A) _ _) =
      (cod Cat.{u, u}).id (totalObj (fibres X)) := by
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

end CodEquiv

open CodEquiv in
/-- **The unit** `VertFunctor.id DisplayedCat ≅ total ⋙ᵥ fibresFunctor`, vertical over `Cat`. -/
def codUnitIso : VertFunctor.id DisplayedCat.{u} ≅ total ⋙ᵥ fibresFunctor :=
  VertNatIso.ofComponents
    (fun D => ⟨unitHom D, unitInv D, unitHom_unitInv D, unitInv_unitHom D⟩) (fun _ => rfl)

open CodEquiv in
/-- **The counit** `fibresFunctor ⋙ᵥ total ≅ VertFunctor.id (cod Cat)`, vertical over `Cat`. -/
def codCounitIso : fibresFunctor ⋙ᵥ total ≅ VertFunctor.id (cod Cat.{u, u}) :=
  VertNatIso.ofComponents
    (fun X => ⟨counitHom X, counitInv X, counitHom_counitInv X, counitInv_counitHom X⟩)
    (fun _ => rfl)

/-- **Displayed categories over `A` are the functors into `A`**: taking total categories is an
equivalence `DisplayedCat ≃ cod Cat` over `Cat`, with inverse taking fibres. -/
def codEquiv : VertEquivalence DisplayedCat.{u} (cod Cat.{u, u}) where
  functor := total
  inverse := fibresFunctor
  unitIso := codUnitIso
  counitIso := codCounitIso

/-- **Taking total categories is fully faithful**: functors `D.Total ⥤ E.Total` over `u` are
displayed functors over `u`. -/
def totalFullyFaithful : total.{u}.FullyFaithful :=
  codEquiv.fullyFaithful

end DisplayedCat

end Displayed
