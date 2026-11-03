import DoubleDisplayed.D2SFib.Category
import Displayed.Opfibration.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# Unstraightening: the dependent 2-sided Grothendieck construction

Given `F : Bᵒᵖ.Total ⥤ Cat`, we build a doubly displayed category `Unstraightening F` over `B`
(the dependent 2-sided Grothendieck construction), and equip it with a `D2SFib` structure
(`unstraightenObj F`). Its action on morphisms, over arbitrary opcartesian functors, is in
`Str/Unstraighten.lean`.

The objects of `Unstraightening F` over `b : B.Ob a` are the objects of `F.obj ⟨a, b⟩`, and a
morphism over `g : B.Hom α b b'` from `c` to `c'` is a morphism
`hobj α c ⟶ vobj (B.opcartesianFactor g) c'` of `F.obj ⟨a', B.push α b⟩`. Here
`hobj`/`hmor` and `vobj`/`vmor` are the actions of `F` on objects and morphisms along the chosen
horizontal and vertical morphisms of `Bᵒᵖ.Total`.

The functoriality of `F` along these, and the interchange of vertical with horizontal morphisms,
are rewrite rules. They have their own heads `hobj`, `hmor`, `vobj` and `vmor`, rather than
`Functor.obj` and `Functor.map`, so that they are only tried where they can apply. (The functor
laws `F.map (𝟙 x) ↦ 𝟙 (F.obj x)` and `F.map (u ≫ v) ↦ F.map u ≫ F.map v` of `Rules.Functor`, which
this file sees through `Displayed/Displayed/Basic.lean`, do not do this. The morphisms of
`Bᵒᵖ.Total` compute, so for a variable `u`, `F.map u` is not definitionally equal to
`F.map (dualHoriz _ _) ≫ F.map (dualVert _)`, the splitting of `F.map (dualHoriz _ _ ≫ dualVert _)`.
They do fire along identities and composites of the chosen morphisms, which are rules in
`Displayed/Opfibration/DualOp.lean`, so `hmap_id`, `hmap_comp`, `vmap_id` and `vmap_comp` hold by
`rfl`.) As a result, composition in `Unstraightening F` is
`hmor α' θ ≫ vmor (B.pushMap α' (B.opcartesianFactor g)) θ'`, with no `eqToHom`, and its laws and
its `D2SFib` structure hold by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

section

namespace Unstraightening

variable (F : Bᵒᵖ.Total ⥤ Cat.{v₃, u₃})

/-! ### `F` along the chosen morphisms of `Bᵒᵖ.Total` -/

section Generators

variable {a a' a'' : A}

/-- `F` along the chosen horizontal morphism `dualHoriz α b`. -/
def hmap (α : a ⟶ a') (b : B.Ob a) :
    F.obj (Bᵒᵖ.tot b) ⥤ F.obj (Bᵒᵖ.tot (B.push α b)) :=
  (F.map (dualHoriz α b)).toFunctor

/-- `F` along the chosen vertical morphism `dualVert β`. -/
def vmap {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') : F.obj (Bᵒᵖ.tot b') ⥤ F.obj (Bᵒᵖ.tot b) :=
  (F.map (dualVert β)).toFunctor

/-- `hmap` on objects. -/
def hobj (α : a ⟶ a') (b : B.Ob a) (c : F.obj (Bᵒᵖ.tot b)) :
    F.obj (Bᵒᵖ.tot (B.push α b)) :=
  (hmap F α b).obj c

/-- `hmap` on morphisms. -/
def hmor (α : a ⟶ a') (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    hobj F α b c ⟶ hobj F α b c' :=
  (hmap F α b).map θ

/-- `vmap` on objects. -/
def vobj {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (Bᵒᵖ.tot b')) :
    F.obj (Bᵒᵖ.tot b) :=
  (vmap F β).obj c

/-- `vmap` on morphisms. -/
def vmor {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : F.obj (Bᵒᵖ.tot b')} (θ : c ⟶ c') :
    vobj F β c ⟶ vobj F β c' :=
  (vmap F β).map θ

theorem hmap_id (b : B.Ob a) : hmap F (𝟙 a) b = 𝟭 _ :=
  rfl

theorem hmap_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    hmap F (α ≫ α') b = hmap F α b ⋙ hmap F α' (B.push α b) :=
  rfl

theorem vmap_id (b : B.Ob a) : vmap F (B.id b) = 𝟭 _ :=
  rfl

theorem vmap_comp {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'') :
    vmap F (β ≫ᵈ γ) = vmap F γ ⋙ vmap F β :=
  rfl

theorem vmap_hmap (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    vmap F β ⋙ hmap F α b = hmap F α b' ⋙ vmap F (B.pushMap α β) :=
  (congrArg Cat.Hom.toFunctor (F.map_comp (dualVert β) (dualHoriz α b))).symm.trans
    (congrArg Cat.Hom.toFunctor (F.map_comp (dualHoriz α b') (dualVert (B.pushMap α β))))

/-! The actions on morphisms along identities, composites and the interchange are first stated as
`≍`, before the corresponding rules on objects are declared: once they are, `hobj F (𝟙 a) b c` is no
longer recognizably its own unfolding `(hmap F (𝟙 a) b).obj c`. The rules on objects then make the
two sides of each `≍` have the same type. -/

theorem hmor_idBase_heq (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    hmor F (𝟙 a) b θ ≍ θ := Functor.hcongr_hom (hmap_id F b) θ

theorem hmor_compBase_heq (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a)
    {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    hmor F (α ≫ α') b θ ≍ hmor F α' (B.push α b) (hmor F α b θ) :=
  Functor.hcongr_hom (hmap_comp F α α' b) θ

theorem vmor_idBase_heq (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    vmor F (B.id b) θ ≍ θ := Functor.hcongr_hom (vmap_id F b) θ

theorem vmor_compBase_heq {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : F.obj (Bᵒᵖ.tot b'')} (θ : c ⟶ c') :
    vmor F (β ≫ᵈ γ) θ ≍ vmor F β (vmor F γ θ) :=
  Functor.hcongr_hom (vmap_comp F β γ) θ

theorem hmor_vmor_heq (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (Bᵒᵖ.tot b')} (θ : c ⟶ c') :
    hmor F α b (vmor F β θ) ≍ vmor F (B.pushMap α β) (hmor F α b' θ) :=
  Functor.hcongr_hom (vmap_hmap F α β) θ

@[rewrite_rule]
theorem hobj_id (b : B.Ob a) (c : F.obj (Bᵒᵖ.tot b)) : hobj F (𝟙 a) b c = c :=
  Functor.congr_obj (hmap_id F b) c

@[rewrite_rule]
theorem hobj_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) (c : F.obj (Bᵒᵖ.tot b)) :
    hobj F (α ≫ α') b c = hobj F α' (B.push α b) (hobj F α b c) :=
  Functor.congr_obj (hmap_comp F α α' b) c

@[rewrite_rule]
theorem vobj_id (b : B.Ob a) (c : F.obj (Bᵒᵖ.tot b)) : vobj F (B.id b) c = c :=
  Functor.congr_obj (vmap_id F b) c

@[rewrite_rule]
theorem vobj_comp {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    (c : F.obj (Bᵒᵖ.tot b'')) : vobj F (β ≫ᵈ γ) c = vobj F β (vobj F γ c) :=
  Functor.congr_obj (vmap_comp F β γ) c

@[rewrite_rule]
theorem hobj_vobj (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (Bᵒᵖ.tot b')) :
    hobj F α b (vobj F β c) = vobj F (B.pushMap α β) (hobj F α b' c) :=
  Functor.congr_obj (vmap_hmap F α β) c

@[rewrite_rule]
theorem hmor_id (α : a ⟶ a') (b : B.Ob a) (c : F.obj (Bᵒᵖ.tot b)) :
    hmor F α b (𝟙 c) = 𝟙 _ := (hmap F α b).map_id c

@[rewrite_rule]
theorem hmor_comp (α : a ⟶ a') (b : B.Ob a) {c c' c'' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c')
    (θ' : c' ⟶ c'') : hmor F α b (θ ≫ θ') = hmor F α b θ ≫ hmor F α b θ' :=
  (hmap F α b).map_comp θ θ'

@[rewrite_rule]
theorem vmor_id {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (Bᵒᵖ.tot b')) :
    vmor F β (𝟙 c) = 𝟙 _ := (vmap F β).map_id c

@[rewrite_rule]
theorem vmor_comp {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' c'' : F.obj (Bᵒᵖ.tot b')}
    (θ : c ⟶ c') (θ' : c' ⟶ c'') : vmor F β (θ ≫ θ') = vmor F β θ ≫ vmor F β θ' :=
  (vmap F β).map_comp θ θ'

@[rewrite_rule]
theorem hmor_idBase (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    hmor F (𝟙 a) b θ = θ :=
  eq_of_heq (hmor_idBase_heq F b θ)

@[rewrite_rule]
theorem hmor_compBase (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)}
    (θ : c ⟶ c') : hmor F (α ≫ α') b θ = hmor F α' (B.push α b) (hmor F α b θ) :=
  eq_of_heq (hmor_compBase_heq F α α' b θ)

@[rewrite_rule]
theorem vmor_idBase (b : B.Ob a) {c c' : F.obj (Bᵒᵖ.tot b)} (θ : c ⟶ c') :
    vmor F (B.id b) θ = θ :=
  eq_of_heq (vmor_idBase_heq F b θ)

@[rewrite_rule]
theorem vmor_compBase {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : F.obj (Bᵒᵖ.tot b'')} (θ : c ⟶ c') :
    vmor F (β ≫ᵈ γ) θ = vmor F β (vmor F γ θ) :=
  eq_of_heq (vmor_compBase_heq F β γ θ)

@[rewrite_rule]
theorem hmor_vmor (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (Bᵒᵖ.tot b')} (θ : c ⟶ c') :
    hmor F α b (vmor F β θ) = vmor F (B.pushMap α β) (hmor F α b' θ) :=
  eq_of_heq (hmor_vmor_heq F α β θ)

/-- `F` on an arbitrary morphism of `Bᵒᵖ.Total`, which factors as a chosen horizontal morphism
followed by a vertical one. -/
theorem map_eq {x x' : Bᵒᵖ.Total} (u : x ⟶ x') :
    (F.map u).toFunctor = hmap F u.base x.2 ⋙ vmap (B := B) F u.fiber :=
  congrArg Cat.Hom.toFunctor
    (F.map_comp (dualHoriz (B := B) u.base x.2) (dualVert (B := B) u.fiber))

end Generators

/-! ### The doubly displayed category `Unstraightening F` -/

section Construction

variable {a a' a'' : A}

/-- Objects of `Unstraightening F` over `b : B.Ob a`. -/
abbrev Ob (b : B.Ob a) : Type u₃ := F.obj (Bᵒᵖ.tot b)

/-- Morphisms of `Unstraightening F` over `g : B.Hom α b b'`:
`hom_{C(a', B(α)b)}(C(α,id)c, C(id,β)c')`. -/
abbrev Hom {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : Ob F b) (c' : Ob F b') : Type v₃ :=
  hobj F α b c ⟶ vobj F (B.opcartesianFactor g) c'

/-- The identity of `Unstraightening F`. -/
def id' {b : B.Ob a} (c : Ob F b) : Hom F (B.id b) c c := 𝟙 c

/-- Composition in `Unstraightening F`: `γ ≔ C(α',id)θ ≫ C(id, B(α')β)θ'`. -/
def comp' {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}
    {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'') : Hom F (g ≫ᵈ g') c c'' :=
  hmor F α' (B.push α b) θ ≫ vmor F (B.pushMap α' (B.opcartesianFactor g)) θ'

theorem id_comp'' {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'} {c : Ob F b}
    {c' : Ob F b'} (θ : Hom F g c c') : comp' F (id' F c) θ = θ := rfl

theorem comp_id'' {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'} {c : Ob F b}
    {c' : Ob F b'} (θ : Hom F g c c') : comp' F θ (id' F c') = θ := rfl

theorem assoc'' {a₃ : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {α'' : a'' ⟶ a₃} {b : B.Ob a}
    {b' : B.Ob a'} {b'' : B.Ob a''} {b₃ : B.Ob a₃} {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''}
    {g'' : b'' ⟶[α''] b₃} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''} {c₃ : Ob F b₃}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'') (θ'' : Hom F g'' c'' c₃) :
    comp' F (comp' F θ θ') θ'' = comp' F θ (comp' F θ' θ'') := rfl

end Construction

end Unstraightening

open Unstraightening in
/-- **The unstraightening of `F`**, the dependent 2-sided Grothendieck construction:
the doubly displayed category over `B` associated with a functor `F : Bᵒᵖ.Total ⥤ Cat`. -/
def Unstraightening (F : Bᵒᵖ.Total ⥤ Cat.{v₃, u₃}) :
    DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B where
  Ob b := Unstraightening.Ob F b
  Hom g c c' := Unstraightening.Hom F g c c'
  id c := id' F c
  comp θ θ' := comp' F θ θ'
  id_comp θ := id_comp'' F θ
  comp_id θ := comp_id'' F θ
  assoc θ θ' θ'' := assoc'' F θ θ' θ''

namespace Unstraightening

variable (F : Bᵒᵖ.Total ⥤ Cat.{v₃, u₃})

/-- The `D2SFib` structure on the unstraightening: the chosen pullbacks and
pushforwards are the images under `F` of the chosen morphisms of `Bᵒᵖ.Total`, and the chosen
lifts are identities. -/
instance instD2SFib : D2SFib (Unstraightening F) where
  pull β c := vobj F β c
  pullLift _ _ := 𝟙 _
  isCartesianPullLift _ _ := ⟨fun _ _ χ => χ, fun _ _ _ => rfl, fun _ h => h⟩
  push := @fun _ _ α b c => hobj F α b c
  pushLift _ _ _ := 𝟙 _
  isOpcartesianPushLift _ _ _ := ⟨fun _ _ χ => χ, fun _ _ _ => rfl, fun _ h => h⟩

instance instPreSplitD2SFib : PreSplitD2SFib (Unstraightening F) where
  pull_id _ := rfl
  pull_comp _ _ _ := rfl
  push_id _ := rfl
  push_comp := by intros; rfl
  push_pull := by intros; rfl

instance instSplitD2SFib : SplitD2SFib (Unstraightening F) where
  pullLift_id _ := rfl
  pullLift_comp _ _ _ := rfl
  pushLift_id _ := rfl
  pushLift_comp := by intros; rfl
  pushLift_pullLift := by intros; rfl

section Maps

variable {a a' : A}

/-- The pushforward action of `Unstraightening F` on fiber morphisms is `hmor`. -/
@[rewrite_rule]
theorem pushMap_eq (α : a ⟶ a') {b : B.Ob a} {c c' : (Unstraightening F).Fiber b} (f : c ⟶ c') :
    pushMap (C := Unstraightening F) α f = hmor F α b f :=
  (DoubleDisplayed.IsOpcartesian.desc_uniq (isOpcartesianPushLift (C := Unstraightening F) α c) _
    rfl).symm

/-- The pullback action of `Unstraightening F` on fiber morphisms is `vmor`. -/
@[rewrite_rule]
theorem pullMap_eq {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : (Unstraightening F).Fiber b'}
    (f : c ⟶ c') :
    pullMap (C := Unstraightening F) β f = vmor F β f :=
  (pullDesc_uniq β c' (B.id b) _ _ rfl).symm

end Maps

end Unstraightening

/-- Bundled form: the object of `D2SFibCat B` carried by the unstraightening. -/
def unstraightenObj (F : Bᵒᵖ.Total ⥤ Cat.{v₃, u₃}) : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B :=
  ⟨Unstraightening F⟩

end

end DoubleDisplayed.D2SFib.Straightening
