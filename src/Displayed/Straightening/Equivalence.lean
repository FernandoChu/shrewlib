import Displayed.Straightening.Straighten
import Displayed.Straightening.Unstraighten
import Displayed.Fibration.CartesianFunctor
import Displayed.Fibration.DisplayedCat

/-!
# Straightening–unstraightening for displayed categories

`unstraighten : VertFunctor LaxNormalCat DisplayedCat` is an isomorphism of categories over `Cat`,
with inverse `straighten`: `straighten ⋙ᵥ unstraighten` is the identity by `rfl`
(`straighten_comp_unstraighten`), and `unstraighten ⋙ᵥ straighten` is the identity
propositionally (`unstraighten_comp_straighten`). In particular the functors between the total
categories are inverse to each other. As an equivalence over `Cat`, in the displayed sense, it is
`straighteningEquiv : VertEquivalence LaxNormalCat DisplayedCat`, whose unit and counit are
vertical, i.e. their components lie over identities of `Cat`.

Both have identity components, and their laws and naturality hold by `rfl`. The counit is the
identity: `unstraightenObj (straightenObj D)` is `D` (`unstraightenObj_straightenObj`). The unit is
the identity only propositionally (`straightenObj_unstraightenObj`). The lax normal functor
`straightenObj (unstraightenObj F)` has the elements and composition constraints of `F`, but its
fibers are those of `unstraightenObj F`, composed by the composition constraint of `F` rather than
in `F c`, and they act on the elements by it too. These agree with `F` by `mul_eq_comp`,
`lmap_eq_mul` and `rmap_eq_mul`, but not definitionally, so the proof goes through
`LaxNormal.ext`, which compares the data on heterogeneously equal arguments. On morphisms, a
transformation is sent to one with the same components (`ReprHom.hext`). Consequently:

* the equivalence of total categories `LaxNormalCat.Total ≌ DisplayedCat.Total` commutes with the
  projections to `Cat` (`straighteningEquivTotal_functor_comp_π`);
* `LaxNormalCat` and `DisplayedCat` are split fibrations over `Cat`, by restriction along `u`
  (`Displayed/Fibration/DisplayedCat` for `DisplayedCat`), and both functors are cartesian
  functors, preserving the chosen lifts strictly (`unstraightenCartesian`, `straightenCartesian`).
  `straightenObj (DisplayedCat.pull u E)` is `pullback u (straightenObj E)` by `rfl`, and
  `unstraightenObj (pullback u G)` is `DisplayedCat.pull u (unstraightenObj G)` on each component
  by `rfl` (`unstraightenObj_pullback`), but the kernel does not accept `rfl` for the whole
  displayed categories, as explained there;
* both functors preserve all cartesian morphisms (`isCartesianUnstraightenMap`,
  `isCartesianStraightenMap`).
-/

universe u

namespace Displayed.Straightening

open CategoryTheory Bicategory Displayed

open scoped Displayed

/-! ## The unit -/

section Unit

variable {A : Cat.{u, u}} (F : LaxNormal A)

/-- The unit at `F`, with identity components. -/
def unitHom : ReprHom (𝟙 A) F (straightenObj (unstraightenObj F)) where
  obj x := x
  map s := s
  map_id _ := rfl
  map_mul _ _ := rfl

/-- The inverse of the unit at `F`, with identity components. -/
def unitInv : ReprHom (𝟙 A) (straightenObj (unstraightenObj F)) F where
  obj x := x
  map s := s
  map_id _ := rfl
  map_mul _ _ := rfl

theorem unitHom_unitInv :
    (LaxNormalCat.comp (unitHom F) (unitInv F) : LaxNormalCat.Hom (𝟙 A) F F) = LaxNormalCat.id F :=
  rfl

theorem unitInv_unitHom :
    (LaxNormalCat.comp (unitInv F) (unitHom F) : LaxNormalCat.Hom (𝟙 A) _ _) =
      LaxNormalCat.id (straightenObj (unstraightenObj F)) :=
  rfl

end Unit

/-- **The unit** `VertFunctor.id LaxNormalCat ≅ unstraighten ⋙ᵥ straighten`, vertical over `Cat`. -/
def unitIso : VertFunctor.id LaxNormalCat.{u} ≅ unstraighten ⋙ᵥ straighten :=
  VertNatIso.ofComponents
    (fun F => ⟨unitHom F, unitInv F, unitHom_unitInv F, unitInv_unitHom F⟩) (fun _ => rfl)

/-! ## The unit is the identity, propositionally -/

/-- Two category structures with the same hom-types, the same identities and the same composition
are equal. The identities and composites are compared on heterogeneously equal morphisms, as the
hom-types are only equal. -/
private theorem category_eq {X : Type u} (c c' : SmallCategory X)
    (hQ : c.toQuiver = c'.toQuiver)
    (hid : ∀ x : X, @CategoryStruct.id X c.toCategoryStruct x ≍
      @CategoryStruct.id X c'.toCategoryStruct x)
    (hcomp : ∀ {x y z : X} (f : @Quiver.Hom X c.toQuiver x y) (g : @Quiver.Hom X c.toQuiver y z)
      (f' : @Quiver.Hom X c'.toQuiver x y) (g' : @Quiver.Hom X c'.toQuiver y z), f ≍ f' → g ≍ g' →
        @CategoryStruct.comp X c.toCategoryStruct x y z f g ≍
          @CategoryStruct.comp X c'.toCategoryStruct x y z f' g') :
    c = c' := by
  obtain @⟨@⟨Q, id, comp⟩, _, _, _⟩ := c
  obtain @⟨@⟨Q', id', comp'⟩, _, _, _⟩ := c'
  obtain rfl : Q = Q' := hQ
  obtain rfl : id = id' := funext fun x => eq_of_heq (hid x)
  obtain rfl : @comp = @comp' := by
    funext x y z f g
    exact eq_of_heq (hcomp f g f g HEq.rfl HEq.rfl)
  rfl

/-- **Straightening the unstraightening of `F` gives back `F`**, propositionally. The two have
the same categories `F.obj a`, but those of `straightenObj (unstraightenObj F)` compose by the
composition constraint of `F` (`mul_eq_comp`). They have the same elements, on which the morphisms
of the fibers act by the composition constraint (`lmap_eq_mul`, `rmap_eq_mul`), and the same
composition constraints. Once the categories are identified, all of these hold by `rfl`. -/
theorem straightenObj_unstraightenObj {A : Cat.{u, u}} (F : LaxNormal A) :
    straightenObj (unstraightenObj F) = F := by
  refine LaxNormal.ext (fun a => ?_) ?_ ?_ ?_ ?_
  · refine congrArg (@ProfCat.of _) (category_eq _ _ rfl (fun _ => HEq.rfl) ?_)
    intro x y z h h' k k' hk hk'
    obtain rfl := eq_of_heq hk
    obtain rfl := eq_of_heq hk'
    exact heq_of_eq (mul_eq_comp h h')
  · intro a b f x x' y y' hx hy
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq hy
    rfl
  · intro a b f x₁ x₂ x₁' x₂' y y' k k' s s' h₁ h₂ hy hk hs
    obtain rfl := eq_of_heq h₁
    obtain rfl := eq_of_heq h₂
    obtain rfl := eq_of_heq hy
    obtain rfl := eq_of_heq hk
    obtain rfl := eq_of_heq hs
    exact heq_of_eq (lmap_eq_mul (F := F) f.as k s).symm
  · intro a b f x x' y₁ y₂ y₁' y₂' k k' s s' hx h₁ h₂ hk hs
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq h₁
    obtain rfl := eq_of_heq h₂
    obtain rfl := eq_of_heq hk
    obtain rfl := eq_of_heq hs
    exact heq_of_eq (rmap_eq_mul (F := F) f.as k s).symm
  · intro a b c f g x x' y y' z z' s s' t t' hx hy hz hs ht
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq hy
    obtain rfl := eq_of_heq hz
    obtain rfl := eq_of_heq hs
    obtain rfl := eq_of_heq ht
    exact HEq.rfl

/-! ## The counit -/

section Counit

variable {A : Cat.{u, u}} (D : Displayed.{u, u, u, u} A)

/-- **Unstraightening the straightening of `D` gives back `D`**, on the nose. -/
theorem unstraightenObj_straightenObj : unstraightenObj (straightenObj D) = D :=
  rfl

/-- The counit at `D`, the identity. -/
def counitHom : DisplayedCat.Hom (𝟙 A) (unstraightenObj (straightenObj D)) D :=
  DisplayedCat.id D

/-- The inverse of the counit at `D`, the identity. -/
def counitInv : DisplayedCat.Hom (𝟙 A) D (unstraightenObj (straightenObj D)) :=
  DisplayedCat.id D

end Counit

/-- **The counit** `straighten ⋙ᵥ unstraighten ≅ VertFunctor.id DisplayedCat`, vertical over `Cat`,
the identity. -/
def counitIso : straighten ⋙ᵥ unstraighten ≅ VertFunctor.id DisplayedCat.{u} :=
  VertNatIso.ofComponents (fun D => ⟨counitHom D, counitInv D, rfl, rfl⟩) (fun _ => rfl)

/-! ## Straightening–unstraightening -/

/-- **Straightening–unstraightening**: `unstraighten : VertFunctor LaxNormalCat DisplayedCat` is an
equivalence over `Cat`, with inverse the straightening. -/
def straighteningEquiv : VertEquivalence LaxNormalCat.{u} DisplayedCat.{u} where
  functor := unstraighten
  inverse := straighten
  unitIso := unitIso
  counitIso := counitIso

/-- The induced equivalence `LaxNormalCat.Total ≌ DisplayedCat.Total` of total categories. It
commutes with the projections to `Cat` (`straighteningEquivTotal_functor_comp_π`). -/
def straighteningEquivTotal : LaxNormalCat.{u}.Total ≌ DisplayedCat.{u}.Total :=
  straighteningEquiv.total

theorem straighteningEquivTotal_functor_comp_π :
    straighteningEquivTotal.{u}.functor ⋙ DisplayedCat.{u}.π = LaxNormalCat.π :=
  rfl

/-! ## An isomorphism of categories over `Cat` -/

/-- **Straightening, then unstraightening, is the identity**, on the nose. -/
theorem straighten_comp_unstraighten :
    straighten ⋙ᵥ unstraighten = VertFunctor.id DisplayedCat.{u} :=
  rfl

/-- **Unstraightening, then straightening, is the identity**, propositionally: on objects by
`straightenObj_unstraightenObj`, and a transformation is sent to one with the same components. -/
theorem unstraighten_comp_straighten :
    unstraighten ⋙ᵥ straighten = VertFunctor.id LaxNormalCat.{u} :=
  DispFunctor.ext (fun F => straightenObj_unstraightenObj F) fun _ =>
    ReprHom.hext (straightenObj_unstraightenObj _) (straightenObj_unstraightenObj _)
      (fun x x' hx => by
        obtain rfl := eq_of_heq hx
        exact HEq.rfl)
      (fun s s' hx hy hs => by
        obtain rfl := eq_of_heq hx
        obtain rfl := eq_of_heq hy
        obtain rfl := eq_of_heq hs
        exact HEq.rfl)

/-- **The total categories are isomorphic**: the functors of `straighteningEquivTotal` are inverse
to each other. -/
theorem straighteningEquivTotal_functor_comp_inverse :
    straighteningEquivTotal.{u}.functor ⋙ straighteningEquivTotal.inverse = 𝟭 _ :=
  congrArg DispFunctor.total unstraighten_comp_straighten

theorem straighteningEquivTotal_inverse_comp_functor :
    straighteningEquivTotal.{u}.inverse ⋙ straighteningEquivTotal.functor = 𝟭 _ :=
  rfl

/-! ## Cartesian functors -/

/-- **Unstraightening sends pullbacks to reindexings.** The two displayed categories agree on each
component by `rfl`, but not as a whole in the kernel. The rules for the laws of displayed categories
reduce the laws of `DisplayedCat.pull u (unstraightenObj G)` to `rfl`, while those of
`unstraightenObj (pullback u G)` are the laws of `G`, which hold only propositionally. -/
theorem unstraightenObj_pullback {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) :
    unstraightenObj (pullback u G) = DisplayedCat.pull u (unstraightenObj G) :=
  Displayed.ext_heq rfl HEq.rfl HEq.rfl HEq.rfl

/-- **`unstraighten` is a cartesian functor**: it sends the chosen pullbacks and lifts of
`LaxNormalCat` to those of `DisplayedCat`. On lifts, both are identities, compared pointwise so
that the kernel does not compare their domains as wholes. -/
def unstraightenCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) LaxNormalCat.{u} DisplayedCat.{u} where
  toPre := { toDispFunctor := unstraighten, obj_pull := unstraightenObj_pullback }
  map_clift _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-- **`straighten` is a cartesian functor**: it sends the chosen pullbacks and lifts of
`DisplayedCat` to those of `LaxNormalCat`, on the nose. -/
def straightenCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) DisplayedCat.{u} LaxNormalCat.{u} where
  toPre := { toDispFunctor := straighten, obj_pull := fun _ _ => rfl }
  map_clift _ _ := rfl

/-- **`unstraighten` preserves cartesian morphisms.** -/
def isCartesianUnstraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A}
    {G : LaxNormal B} {φ : LaxNormalCat.Hom u F G} (H : IsCartesian (D := LaxNormalCat) φ) :
    IsCartesian (D := DisplayedCat) (unstraighten.map φ) :=
  straighteningEquiv.isCartesianMap H

/-- **The straightening preserves cartesian morphisms.** -/
def isCartesianStraightenMap {A B : Cat.{u, u}} {u : A ⟶ B} {X : DisplayedCat.{u}.Ob A}
    {Y : DisplayedCat.{u}.Ob B} {w : DisplayedCat.Hom u X Y}
    (H : IsCartesian (D := DisplayedCat) w) :
    IsCartesian (D := LaxNormalCat) (straighten.map w) :=
  straighteningEquiv.symm.isCartesianMap H

end Displayed.Straightening
