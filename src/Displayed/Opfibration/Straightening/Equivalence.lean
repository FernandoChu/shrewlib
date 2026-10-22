import Displayed.Opfibration.Straightening.Straighten
import Tactic.KernelTactic
import Displayed.Displayed.Equivalence

/-!
# Straightening–unstraightening for split opfibrations

The unstraightening `ICat ⟶ SplitOpfibCat` is an equivalence over `Cat`
(`straighteningEquiv`). It is fully faithful (`unstraightenSplitFullyFaithful`), and every split
opfibration `p : E ⥤ A` is isomorphic over `A` to the unstraightening of its straightening
(`counitIso`), so `VertEquivalence.ofFullyFaithful` assembles the equivalence. Its inverse is the
straightening on objects, and on morphisms the preimage under the unstraightening of the
conjugate by the counit.

The counit `A ⋉ Str p ⥤ E` sends `(a, x)` to `x` and `(f, φ)` to `olift f x ≫ φ`. Its inverse
sends `e` to `(p e, e)` and a morphism `g` to `(p g, φ)`, for `φ` the opcartesian factorization of
`g` through the chosen lift. The two composites are identities: one by `rfl`, since a
morphism is its chosen lift followed by its factorization; the other since the factorization of
`olift f x ≫ φ` is `φ`.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open Displayed.Straightening (Fibre FibreHom fibres fibres.comp_val)

open Grothendieck (Hom)

open scoped Displayed

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (X : SplitOpfibOb A)

/-- The counit at `p : E ⥤ A`, as a functor: `(a, x) ↦ x`, and `(f, φ) ↦ olift f x ≫ φ`. -/
def counitFunctor : A ⋉ straightenObj X ⥤ X.ob.dom where
  obj Y := Y.fiber.1
  map {Y _} k := ((fibres X.ob).olift k.base Y.fiber ≫ᵈ k.fiber).1
  map_id _ := rfl
  -- The displayed composite is computed by the rules before its underlying morphism is taken.
  map_comp {Y Y' _} k l := (congrArg Subtype.val
    (show (fibres X.ob).olift (k ≫ l).base Y.fiber ≫ᵈ (k ≫ l).fiber =
      ((fibres X.ob).olift k.base Y.fiber ≫ᵈ k.fiber) ≫ᵈ
        ((fibres X.ob).olift l.base Y'.fiber ≫ᵈ l.fiber) from rfl)).trans (fibres.comp_val _ _)

/-- A morphism `g` of `E`, as a morphism over `p g` between the objects of the fibres. -/
def homOver {e e' : X.ob.dom} (g : e ⟶ e') :
    FibreHom X.ob (X.ob.hom.toFunctor.map g) ⟨e, rfl⟩ ⟨e', rfl⟩ :=
  ⟨g, rfl⟩

/-- The inverse of the counit, as a functor: `e ↦ (p e, e)`, and a morphism `g` goes to `p g`
with the opcartesian factorization of `g`. -/
def counitInvFunctor : X.ob.dom ⥤ A ⋉ straightenObj X where
  obj e := ⟨X.ob.hom.toFunctor.obj e, ⟨e, rfl⟩⟩
  map g := ⟨X.ob.hom.toFunctor.map g, (fibres X.ob).opcartesianFactor (homOver X g)⟩
  map_id _ := rfl
  map_comp g h := Groth.hom_mk_congr
    ((fibres X.ob).opcartesianFactor_comp (homOver X g) (homOver X h))

/-- The counit at `p`. -/
def counitHom :
    SplitOpfibCat.Hom (𝟙 A) (unstraightenSplit.obj (straightenObj X)) X :=
  ⟨(counitFunctor X).toCatHom, Cat.Hom.ext (CategoryTheory.Functor.ext (fun Y => Y.fiber.2)
    (fun _ _ k => FibreHom.proj_map ((fibres X.ob).olift k.base _ ≫ᵈ k.fiber)))⟩

/-- The inverse of the counit at `p`. -/
def counitInv :
    SplitOpfibCat.Hom (𝟙 A) X (unstraightenSplit.obj (straightenObj X)) :=
  ⟨(counitInvFunctor X).toCatHom, rfl⟩

/-- `counitInvFunctor` on morphisms, as an equation: rewriting with it keeps the rules from
splitting the image of a composite before the factorization is taken. -/
theorem counitInvFunctor_map {e e' : X.ob.dom} (g : e ⟶ e') :
    (counitInvFunctor X).map g =
      Hom.mk (X.ob.hom.toFunctor.map g) ((fibres X.ob).opcartesianFactor (homOver X g)) :=
  rfl

/-- The factorization of `olift f x ≫ φ` is `φ`. -/
theorem counitInvFunctor_map_counitFunctor_map {x y : X.ob.dom}
    (k : (⟨_, ⟨x, rfl⟩⟩ : A ⋉ straightenObj X) ⟶ ⟨_, ⟨y, rfl⟩⟩) :
    (counitInvFunctor X).map ((counitFunctor X).map k) = k := by
  obtain ⟨kb, kf⟩ := k
  rw [counitInvFunctor_map]
  have hb : X.ob.hom.toFunctor.map ((counitFunctor X).map (Hom.mk kb kf)) = kb := by
    kernel_exact ((fibres X.ob).olift kb ⟨x, rfl⟩ ≫ᵈ kf).2
  have hf := ((fibres X.ob).opcartesianFactor_heq hb (FibreHom.heq_of_val hb
    (homOver X ((counitFunctor X).map (Hom.mk kb kf)))
    ((fibres X.ob).olift kb ⟨x, rfl⟩ ≫ᵈ kf) rfl)).trans
    (heq_of_eq ((fibres X.ob).olift_comp_opcartesianFactor (kf : (fibres X.ob).Hom (𝟙 _) _ _)))
  exact Groth.Hom.ext' hb hf

theorem counitHom_counitInv :
    SplitOpfibCat.comp (counitHom X) (counitInv X) =
      SplitOpfibCat.id (unstraightenSplit.obj (straightenObj X)) := by
  refine CodHom.ext (Cat.Hom.ext (Functor.hext (fun Y => ?_) ?_))
  · obtain ⟨a, _, h⟩ := Y
    obtain rfl : _ = a := h
    rfl
  rintro ⟨a, x, hx⟩ ⟨a', y, hy⟩ k
  obtain rfl : _ = a := hx
  obtain rfl : _ = a' := hy
  exact heq_of_eq (counitInvFunctor_map_counitFunctor_map X k)

theorem counitInv_counitHom :
    SplitOpfibCat.comp (counitInv X) (counitHom X) = SplitOpfibCat.id X :=
  rfl

/-- **The counit** `Unstr (Str p) ≅ p`, an isomorphism over `A`. -/
def counitIso :
    (unstraightenSplit.obj (straightenObj X) : SplitOpfibCat.Fiber A) ≅ X where
  hom := counitHom X
  inv := counitInv X
  hom_inv_id := counitHom_counitInv X
  inv_hom_id := counitInv_counitHom X

end Counit

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening for split opfibrations**: the unstraightening is an
equivalence over `Cat` between `ICat` and the split opfibrations, with all functors over the base
as morphisms. -/
def straighteningEquiv : VertEquivalence ICat.{u} SplitOpfibCat.{u} :=
  VertEquivalence.ofFullyFaithful unstraightenSplitFullyFaithful (fun X => straightenObj X)
    (fun X => counitIso X)

/-- The induced equivalence of total categories, over `Cat`. -/
def straighteningEquivTotal : ICat.{u}.Total ≌ SplitOpfibCat.{u}.Total :=
  straighteningEquiv.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivTotal.{u}.functor ⋙ SplitOpfibCat.π = ICat.π :=
  rfl

end Displayed.Opfibration.Straightening
