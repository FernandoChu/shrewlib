import DoubleDisplayed.D2SFib.DProfStr
import DoubleDisplayed.D2SFib.D2SFibStr
import DoubleDisplayed.D2SFib.Straightening.Unstraighten

/-!
# Unstraightening of dependent profunctors, over `SplitOpfibStr`

The unstraightening `Unstraightening P` of a dependent profunctor `P : Bᵒᵖ.Total ⥤ Cat` is a split
D2SFib over `B` (`DoubleDisplayed/D2SFib/Straightening/Unstraighten.lean`). Here we extend it to
the morphisms of dependent profunctors over arbitrary opcartesian functors, which makes it natural
in `B`: a natural transformation `κ : P ⟶ H.dualOp.total ⋙ P'` gives the map of D2SFibs over `H`
with the components of `κ` on objects and morphisms (`unstraightenStrMap`), and the unstraightening
is a vertical functor `unstraightenStr : VertFunctor DProfStr D2SFibStr` over `SplitOpfibStr`.

As for the transformations between functors on the same category, the components of `κ` on
objects and morphisms have their own heads, `Str.tobj` and `Str.tmor`, and their naturality along
the chosen horizontal and vertical morphisms of `Bᵒᵖ.Total` is a set of rules. Along
`dualHoriz α x` it is the transport `hobj` of `P'` along `u α`, and along `dualVert β` the
transport `vobj` of `P'` along `H β`, since `H.dualOp.total` sends these chosen morphisms to the
chosen morphisms of `B'ᵒᵖ.Total`, by the rules of `H`. The components of a composite
`κ ≫ whiskerLeft H.dualOp.total κ'` are rules too, so that `tobj` and `tmor` are kept when it is
unfolded. With these rules, and the preservation of the opcartesian factorizations by `H`,
`unstraightenStrMap κ` is a functor and preserves the chosen lifts by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib Unstraightening

open scoped Displayed DoubleDisplayed

variable {A A' : Cat.{v₁, u₁}} {u : A ⟶ A'} {B : Displayed.{v₁, u₁, v₂, u₂} A}
  {B' : Displayed.{v₁, u₁, v₂, u₂} A'} [SplitOpfib B] [SplitOpfib B']
  {H : OpcartesianFunctor u.toFunctor B B'} {P : Bᵒᵖ.Total ⥤ Cat.{v₃, u₃}}
  {P' : B'ᵒᵖ.Total ⥤ Cat.{v₃, u₃}}

/-! ## The components of a morphism of dependent profunctors -/

namespace Str

/-- The component of `κ : P ⟶ H.dualOp.total ⋙ P'`, on objects. -/
def tobj (κ : P ⟶ H.dualOp.total ⋙ P') {x : Bᵒᵖ.Total} (c : P.obj x) :
    P'.obj (H.dualOp.total.obj x) :=
  (κ.app x).toFunctor.obj c

/-- The component of `κ : P ⟶ H.dualOp.total ⋙ P'`, on morphisms. -/
def tmor (κ : P ⟶ H.dualOp.total ⋙ P') {x : Bᵒᵖ.Total} {c c' : P.obj x} (θ : c ⟶ c') :
    tobj κ c ⟶ tobj κ c' :=
  (κ.app x).toFunctor.map θ

variable (κ : P ⟶ H.dualOp.total ⋙ P') {a a' : A}

theorem tapp_hmap (α : a ⟶ a') (x : B.Ob a) :
    hmap P α x ⋙ (κ.app (Bᵒᵖ.tot (B.push α x))).toFunctor =
      (κ.app (Bᵒᵖ.tot x)).toFunctor ⋙ hmap P' (u.toFunctor.map α) (H.toPre.obj x) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualHoriz α x))

theorem tapp_vmap {x y : B.Ob a} (β : x ⟶[𝟙 a] y) :
    vmap P β ⋙ (κ.app _).toFunctor = (κ.app _).toFunctor ⋙ vmap P' (H.toPre.map β) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualVert (B := B) β))

theorem tmor_hmor_heq (α : a ⟶ a') (x : B.Ob a) {c c' : P.obj (Bᵒᵖ.tot x)} (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) ≍ hmor P' (u.toFunctor.map α) (H.toPre.obj x) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_hmap κ α x) θ

theorem tmor_vmor_heq {x y : B.Ob a} (β : x ⟶[𝟙 a] y) {c c' : P.obj (Bᵒᵖ.tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P β θ) ≍ vmor P' (H.toPre.map β) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_vmap κ β) θ

@[rewrite_rule]
theorem tobj_hobj (α : a ⟶ a') (x : B.Ob a) (c : P.obj (Bᵒᵖ.tot x)) :
    tobj κ (hobj P α x c) = hobj P' (u.toFunctor.map α) (H.toPre.obj x) (tobj κ c) :=
  Functor.congr_obj (tapp_hmap κ α x) c

@[rewrite_rule]
theorem tobj_vobj {x y : B.Ob a} (β : x ⟶[𝟙 a] y) (c : P.obj (Bᵒᵖ.tot y)) :
    tobj κ (vobj P β c) = vobj P' (H.toPre.map β) (tobj κ c) :=
  Functor.congr_obj (tapp_vmap κ β) c

@[rewrite_rule]
theorem tmor_id {x : Bᵒᵖ.Total} (c : P.obj x) : tmor κ (𝟙 c) = 𝟙 _ :=
  (κ.app x).toFunctor.map_id c

@[rewrite_rule]
theorem tmor_comp {x : Bᵒᵖ.Total} {c c' c'' : P.obj x} (θ : c ⟶ c') (θ' : c' ⟶ c'') :
    tmor κ (θ ≫ θ') = tmor κ θ ≫ tmor κ θ' :=
  (κ.app x).toFunctor.map_comp θ θ'

@[rewrite_rule]
theorem tmor_hmor (α : a ⟶ a') (x : B.Ob a) {c c' : P.obj (Bᵒᵖ.tot x)} (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) = hmor P' (u.toFunctor.map α) (H.toPre.obj x) (tmor κ θ) :=
  eq_of_heq (tmor_hmor_heq κ α x θ)

@[rewrite_rule]
theorem tmor_vmor {x y : B.Ob a} (β : x ⟶[𝟙 a] y) {c c' : P.obj (Bᵒᵖ.tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P β θ) = vmor P' (H.toPre.map β) (tmor κ θ) :=
  eq_of_heq (tmor_vmor_heq κ β θ)

/-! The components of composites of morphisms of dependent profunctors, as rules, so that the
heads `tobj` and `tmor` are kept when a composite is unfolded. -/

variable {A'' : Cat.{v₁, u₁}} {u' : A' ⟶ A''} {B'' : Displayed.{v₁, u₁, v₂, u₂} A''}
  [SplitOpfib B'']
  {K : OpcartesianFunctor u'.toFunctor B' B''} {P'' : B''ᵒᵖ.Total ⥤ Cat.{v₃, u₃}}

@[rewrite_rule]
theorem tobj_compNat (κ' : P' ⟶ K.dualOp.total ⋙ P'') {x : Bᵒᵖ.Total} (c : P.obj x) :
    tobj (u := u ≫ u') (H := H.comp K) (P' := P'')
      (κ ≫ Functor.whiskerLeft H.dualOp.total κ') c = tobj κ' (tobj κ c) := rfl

@[rewrite_rule]
theorem tmor_compNat (κ' : P' ⟶ K.dualOp.total ⋙ P'') {x : Bᵒᵖ.Total} {c c' : P.obj x}
    (θ : c ⟶ c') :
    tmor (u := u ≫ u') (H := H.comp K) (P' := P'')
      (κ ≫ Functor.whiskerLeft H.dualOp.total κ') θ = tmor κ' (tmor κ θ) := rfl

end Str

/-! ## `unstraightenStr` -/

open Str in
/-- **The unstraightening of a morphism of dependent profunctors** `κ : P ⟶ H.dualOp.total ⋙ P'`
over `H`: the map of D2SFibs over `H` given by the components of `κ`. -/
def unstraightenStrMap (κ : P ⟶ H.dualOp.total ⋙ P') :
    D2SFibMap H (Unstraightening P) (Unstraightening P') where
  toObj :=
    { obj := fun c => tobj κ c
      map := fun θ => tmor κ θ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; rfl
  map_pushLift := by intros; rfl

/-- The unstraightening of a dependent profunctor is a split D2SFib. The instance
`Unstraightening.instSplitD2SFib` does not apply to it, since `DProfStr.Ob B` is not reducibly a
type of functors. -/
instance {A : Cat.{v₁, u₁}} {B : SplitOpfibStr.{v₁, u₁, v₂, u₂}.Ob A}
    (P : DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃}.Ob B) :
    SplitD2SFib (Unstraightening (B := SplitOpfibOb.toDisplayed B) P) :=
  Unstraightening.instSplitD2SFib P

/-- **The unstraightening over `SplitOpfibStr`**: dependent profunctors go to their
unstraightenings, and their morphisms over `H` to maps of D2SFibs over `H`. -/
def unstraightenStr :
    VertFunctor DProfStr.{v₁, u₁, v₂, u₂, v₃, u₃} D2SFibStr.{v₁, u₁, v₂, u₂, v₃, u₃} where
  obj P := unstraightenObj P
  map κ := unstraightenStrMap κ
  map_id _ := rfl
  map_comp _ _ := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)

end DoubleDisplayed.D2SFib.Straightening
