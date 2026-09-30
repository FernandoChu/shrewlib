import Straightening.Functors

/-!
# Straightening–unstraightening for displayed categories

Proposition 9: `(▷ᵈ)* : DCat → Cat^→` is part of an equivalence over `Cat`, in the displayed
sense (`straighteningEquiv : DEquivalence DCat Arr`): the unit and counit are vertical, i.e. their
components lie over identities of `Cat`. Consequently:

* the equivalence of total categories `DCat.Total ≌ Arr.Total` commutes with the projections to
  `Cat` (`straighteningEquiv_total`);
* both `DCat` and `Cat^→` are fibrations over `Cat` (`isFibration_DCat`, `isFibration_Arr`);
* both functors preserve cartesian morphisms (`isCartesian_unstraighten_map`,
  `isCartesian_straighten_map`).

The unit `F ⟶ Str (Unstr F)` sends `x` to `⟨(a, x), rfl⟩`, and its inverse transports along the
equation `X.base = a` of an object of the fibre. The counit `Unstr (Str p) ⟶ p` forgets the base
component, and its inverse sends `e` to `(p e, ⟨e, rfl⟩)`. Their naturality holds by `rfl`.
-/

universe u

namespace Straightening

open CategoryTheory Bicategory Nfib Displayed Unstraightening

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
def unitInvObj : ∀ {a : A}, Fib (unstraightenObj F) a → F.obj ⟨a⟩
  | _, ⟨⟨_, x⟩, rfl⟩ => x

/-- The inverse of the unit on morphisms. -/
def unitInvMap : ∀ {a a' : A} {f : a ⟶ a'} {x : Fib (unstraightenObj F) a}
    {y : Fib (unstraightenObj F) a'}, FibHom (unstraightenObj F) f x y →
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
def unitIso : VNatIso (DFunctor.id DCat.{u}) (unstraighten.comp straighten) where
  app F := unitHom F
  inv F := unitInv F
  app_inv F := unitHom_unitInv F
  inv_app F := unitInv_unitHom F
  naturality _ := rfl

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : ArrOb A)

/-- The counit at `p : E ⥤ A`, as a functor: forget the base component. -/
def counitFunctor : Unstraightening (straightenObj X) ⥤ X.dom where
  obj Y := Y.fiber.1
  map g := g.fiber.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of the counit, as a functor: `e ↦ (p e, ⟨e, rfl⟩)`. -/
def counitInvFunctor : X.dom ⥤ Unstraightening (straightenObj X) where
  obj e := ⟨X.proj.obj e, ⟨e, rfl⟩⟩
  map g := ⟨X.proj.map g, ⟨g, rfl⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The counit at `p`. -/
def counitHom : Arr.Hom (𝟙 A) (unstraightenObj (straightenObj X)) X :=
  ⟨counitFunctor X, Functor.ext (fun Y => Y.fiber.2) (fun _ _ g => FibHom.proj_map g.fiber)⟩

/-- The inverse of the counit at `p`. -/
def counitInv : Arr.Hom (𝟙 A) X (unstraightenObj (straightenObj X)) :=
  ⟨counitInvFunctor X, rfl⟩

theorem counitHom_counitInv :
    (Arr.comp (counitHom X) (counitInv X) : Arr.Hom (𝟙 A) _ _) =
      Arr.id (unstraightenObj (straightenObj X)) := by
  refine ArrHom.ext (Functor.hext (fun Y => ?_) ?_)
  · obtain ⟨a, _, h⟩ := Y
    obtain rfl : _ = a := h
    rfl
  rintro ⟨a, _, hx⟩ ⟨a', _, hy⟩ ⟨gb, g, hg⟩
  obtain rfl : _ = a := hx
  obtain rfl : _ = a' := hy
  have e : gb = X.proj.map g := hg.symm
  subst e
  rfl

theorem counitInv_counitHom :
    (Arr.comp (counitInv X) (counitHom X) : Arr.Hom (𝟙 A) X X) = Arr.id X :=
  rfl

end Counit

/-- **The counit** `Unstr ∘ Str ≅ 𝟭`, vertical over `Cat`. -/
def counitIso : VNatIso (straighten.comp unstraighten) (DFunctor.id Arr.{u}) where
  app X := counitHom X
  inv X := counitInv X
  app_inv X := counitHom_counitInv X
  inv_app X := counitInv_counitHom X
  naturality _ := rfl

/-! ## Proposition 9 -/

/-- **Proposition 9** (straightening–unstraightening): `(▷ᵈ)* : DCat → Cat^→` is an equivalence
over `Cat`, with inverse the straightening. -/
def straighteningEquiv : DEquivalence DCat.{u} Arr.{u} where
  functor := unstraighten
  inverse := straighten
  unitIso := unitIso
  counitIso := counitIso

/-- The induced equivalence `DCat ≌ Cat^→` of total categories. It commutes with the projections
to `Cat` (`straighteningEquiv_total_functor_comp_π`). -/
def straighteningEquivTotal : DCat.{u}.Total ≌ Arr.{u}.Total :=
  straighteningEquiv.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivTotal.{u}.functor ⋙ Arr.π = DCat.π :=
  rfl

/-- **`Cat^→` is a fibration over `Cat`**, transferred from `DCat` along the equivalence. -/
theorem isFibration_Arr : IsFibration Arr.{u} :=
  straighteningEquiv.isFibration isFibration_DCat

/-- **`(▷ᵈ)*` preserves cartesian morphisms.** -/
theorem isCartesian_unstraighten_map {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A}
    {G : LaxNormal B} {φ : DCat.Hom u F G} (H : IsCartesian (D := DCat) φ) :
    IsCartesian (D := Arr) (unstraighten.map φ) :=
  straighteningEquiv.isCartesian_map H

/-- **The straightening preserves cartesian morphisms.** -/
theorem isCartesian_straighten_map {A B : Cat.{u, u}} {u : A ⟶ B} {X : ArrOb A} {Y : ArrOb B}
    {w : Arr.Hom u X Y} (H : IsCartesian (D := Arr) w) :
    IsCartesian (D := DCat) (straighten.map w) :=
  straighteningEquiv.symm.isCartesian_map H

end Straightening
