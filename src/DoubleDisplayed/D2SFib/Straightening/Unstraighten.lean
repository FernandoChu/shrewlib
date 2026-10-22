import DoubleDisplayed.D2SFib.Category
import Displayed.Opfibration.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# Unstraightening: the dependent 2-sided Grothendieck construction

Given `F : ∫(Bᵈᵒ) ⥤ Cat`, we build a doubly displayed category `Unstraightening F` over `B` (the
dependent 2-sided Grothendieck construction), equip it with a `D2SFib` structure
(`unstraightenObj F`), and assemble the whole thing into the functor `unstraighten` (`Φ`) :
`(B.dualOp.Total ⥤ Cat) ⥤ D2SFibCat B`.

The objects of `Unstraightening F` over `b : B.Ob a` are the objects of `F.obj ⟨a, b⟩`, and a
morphism over `g : B.Hom α b b'` from `c` to `c'` is a morphism
`hobj α c ⟶ vobj (B.opcartesianFactor g) c'` of `F.obj ⟨a', B.push α b⟩`, that is,
`hom_{C(a', B(α)b)}(C(α,id)c, C(id,β)c')`. Here
`hobj`/`hmor` and `vobj`/`vmor` are the actions of `F` on objects and morphisms along the chosen
horizontal and vertical morphisms of `∫(Bᵈᵒ)`.

The functoriality of `F` along these, and the interchange of vertical with horizontal morphisms,
are rewrite rules. They have their own heads `hobj`, `hmor`, `vobj` and `vmor`, rather than
`Functor.obj` and `Functor.map`, so that they are only tried where they can apply. (A rule
`F.map (u ≫ v) = F.map u ≫ F.map v` for arbitrary morphisms of `∫(Bᵈᵒ)` would not do: these
compute, so `F.map u` and `F.map (dualHoriz _ _ ≫ dualVert _)` would stop being definitionally
equal.) The naturality of a transformation `κ` along these morphisms is a rule too. As a result,
composition in `Unstraightening F` is `hmor α' θ ≫ vmor (B.pushMap α' (B.opcartesianFactor g)) θ'`,
with no `eqToHom`, and its laws, its `D2SFib` structure and the functoriality of `Φ` hold by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

noncomputable section

namespace Unstraightening

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃})

/-! ### `F` along the chosen morphisms of `∫(Bᵈᵒ)` -/

section Generators

variable {a a' a'' : A}

/-- `F` along the chosen horizontal morphism `dualHoriz α b`. -/
def hmap (α : a ⟶ a') (b : B.Ob a) :
    F.obj (B.dualOp.tot b) ⥤ F.obj (B.dualOp.tot (B.push α b)) :=
  (F.map (dualHoriz α b)).toFunctor

/-- `F` along the chosen vertical morphism `dualVert β`. -/
def vmap {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') : F.obj (B.dualOp.tot b') ⥤ F.obj (B.dualOp.tot b) :=
  (F.map (dualVert β)).toFunctor

/-- `hmap` on objects. -/
def hobj (α : a ⟶ a') (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    F.obj (B.dualOp.tot (B.push α b)) :=
  (hmap F α b).obj c

/-- `hmap` on morphisms. -/
def hmor (α : a ⟶ a') (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    hobj F α b c ⟶ hobj F α b c' :=
  (hmap F α b).map θ

/-- `vmap` on objects. -/
def vobj {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (B.dualOp.tot b')) :
    F.obj (B.dualOp.tot b) :=
  (vmap F β).obj c

/-- `vmap` on morphisms. -/
def vmor {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : F.obj (B.dualOp.tot b')} (θ : c ⟶ c') :
    vobj F β c ⟶ vobj F β c' :=
  (vmap F β).map θ

theorem hmap_id (b : B.Ob a) : hmap F (𝟙 a) b = 𝟭 _ := by
  change (F.map (𝟙 (B.dualOp.tot b))).toFunctor = _
  rw [F.map_id]; rfl

theorem hmap_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    hmap F (α ≫ α') b = hmap F α b ⋙ hmap F α' (B.push α b) := by
  change (F.map (dualHoriz α b ≫ dualHoriz α' (B.push α b))).toFunctor = _
  rw [F.map_comp]; rfl

theorem vmap_id (b : B.Ob a) : vmap F (B.id b) = 𝟭 _ := by
  change (F.map (𝟙 (B.dualOp.tot b))).toFunctor = _
  rw [F.map_id]; rfl

theorem vmap_comp {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'') :
    vmap F (β ≫ᵈ γ) = vmap F γ ⋙ vmap F β := by
  change (F.map (dualVert γ ≫ dualVert β)).toFunctor = _
  rw [F.map_comp]; rfl

theorem vmap_hmap (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    vmap F β ⋙ hmap F α b = hmap F α b' ⋙ vmap F (B.pushMap α β) :=
  (congrArg Cat.Hom.toFunctor (F.map_comp (dualVert β) (dualHoriz α b))).symm.trans
    (congrArg Cat.Hom.toFunctor (F.map_comp (dualHoriz α b') (dualVert (B.pushMap α β))))

omit [SplitOpfib B] in
/-- Equal functors act heterogeneously equally on morphisms. -/
theorem _root_.CategoryTheory.Functor.map_heq_of_eq {C D : Type*} [Category C] [Category D]
    {G G' : C ⥤ D} (h : G = G') {X Y : C} (f : X ⟶ Y) : G.map f ≍ G'.map f := by
  subst h; rfl

/-! The actions on morphisms along identities, composites and the interchange are first stated as
`≍`, before the corresponding rules on objects are declared: once they are, `hobj F (𝟙 a) b c` is no
longer recognizably its own unfolding `(hmap F (𝟙 a) b).obj c`. The rules on objects then make the
two sides of each `≍` have the same type. -/

theorem hmor_idBase_heq (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    hmor F (𝟙 a) b θ ≍ θ := Functor.map_heq_of_eq (hmap_id F b) θ

theorem hmor_compBase_heq (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a)
    {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    hmor F (α ≫ α') b θ ≍ hmor F α' (B.push α b) (hmor F α b θ) :=
  Functor.map_heq_of_eq (hmap_comp F α α' b) θ

theorem vmor_idBase_heq (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    vmor F (B.id b) θ ≍ θ := Functor.map_heq_of_eq (vmap_id F b) θ

theorem vmor_compBase_heq {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : F.obj (B.dualOp.tot b'')} (θ : c ⟶ c') :
    vmor F (β ≫ᵈ γ) θ ≍ vmor F β (vmor F γ θ) :=
  Functor.map_heq_of_eq (vmap_comp F β γ) θ

theorem hmor_vmor_heq (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (B.dualOp.tot b')} (θ : c ⟶ c') :
    hmor F α b (vmor F β θ) ≍ vmor F (B.pushMap α β) (hmor F α b' θ) :=
  Functor.map_heq_of_eq (vmap_hmap F α β) θ

@[rewrite_rule]
theorem hobj_id (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) : hobj F (𝟙 a) b c = c :=
  Functor.congr_obj (hmap_id F b) c

@[rewrite_rule]
theorem hobj_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    hobj F (α ≫ α') b c = hobj F α' (B.push α b) (hobj F α b c) :=
  Functor.congr_obj (hmap_comp F α α' b) c

@[rewrite_rule]
theorem vobj_id (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) : vobj F (B.id b) c = c :=
  Functor.congr_obj (vmap_id F b) c

@[rewrite_rule]
theorem vobj_comp {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    (c : F.obj (B.dualOp.tot b'')) : vobj F (β ≫ᵈ γ) c = vobj F β (vobj F γ c) :=
  Functor.congr_obj (vmap_comp F β γ) c

@[rewrite_rule]
theorem hobj_vobj (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (B.dualOp.tot b')) :
    hobj F α b (vobj F β c) = vobj F (B.pushMap α β) (hobj F α b' c) :=
  Functor.congr_obj (vmap_hmap F α β) c

@[rewrite_rule]
theorem hmor_id (α : a ⟶ a') (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    hmor F α b (𝟙 c) = 𝟙 _ := (hmap F α b).map_id c

@[rewrite_rule]
theorem hmor_comp (α : a ⟶ a') (b : B.Ob a) {c c' c'' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c')
    (θ' : c' ⟶ c'') : hmor F α b (θ ≫ θ') = hmor F α b θ ≫ hmor F α b θ' :=
  (hmap F α b).map_comp θ θ'

@[rewrite_rule]
theorem vmor_id {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : F.obj (B.dualOp.tot b')) :
    vmor F β (𝟙 c) = 𝟙 _ := (vmap F β).map_id c

@[rewrite_rule]
theorem vmor_comp {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' c'' : F.obj (B.dualOp.tot b')}
    (θ : c ⟶ c') (θ' : c' ⟶ c'') : vmor F β (θ ≫ θ') = vmor F β θ ≫ vmor F β θ' :=
  (vmap F β).map_comp θ θ'

@[rewrite_rule]
theorem hmor_idBase (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    hmor F (𝟙 a) b θ = θ :=
  eq_of_heq (hmor_idBase_heq F b θ)

@[rewrite_rule]
theorem hmor_compBase (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)}
    (θ : c ⟶ c') : hmor F (α ≫ α') b θ = hmor F α' (B.push α b) (hmor F α b θ) :=
  eq_of_heq (hmor_compBase_heq F α α' b θ)

@[rewrite_rule]
theorem vmor_idBase (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    vmor F (B.id b) θ = θ :=
  eq_of_heq (vmor_idBase_heq F b θ)

@[rewrite_rule]
theorem vmor_compBase {b b' b'' : B.Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : F.obj (B.dualOp.tot b'')} (θ : c ⟶ c') :
    vmor F (β ≫ᵈ γ) θ = vmor F β (vmor F γ θ) :=
  eq_of_heq (vmor_compBase_heq F β γ θ)

@[rewrite_rule]
theorem hmor_vmor (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (B.dualOp.tot b')} (θ : c ⟶ c') :
    hmor F α b (vmor F β θ) = vmor F (B.pushMap α β) (hmor F α b' θ) :=
  eq_of_heq (hmor_vmor_heq F α β θ)

/-- `F` on an arbitrary morphism of `∫(Bᵈᵒ)`, which factors as a chosen horizontal morphism
followed by a vertical one. -/
theorem map_eq {x x' : B.dualOp.Total} (u : x ⟶ x') :
    (F.map u).toFunctor = hmap F u.base x.2 ⋙ vmap (B := B) F u.fiber :=
  congrArg Cat.Hom.toFunctor
    (F.map_comp (dualHoriz (B := B) u.base x.2) (dualVert (B := B) u.fiber))

end Generators

/-! ### The doubly displayed category `Unstraightening F` -/

section Construction

variable {a a' a'' : A}

/-- Objects of `Unstraightening F` over `b : B.Ob a`. -/
abbrev Ob (b : B.Ob a) : Type u₃ := F.obj (B.dualOp.tot b)

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
the doubly displayed category over `B` associated with a functor `F : ∫(Bᵈᵒ) ⥤ Cat`. -/
def Unstraightening (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) :
    DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B where
  Ob b := Unstraightening.Ob F b
  Hom g c c' := Unstraightening.Hom F g c c'
  id c := id' F c
  comp θ θ' := comp' F θ θ'
  id_comp θ := id_comp'' F θ
  comp_id θ := comp_id'' F θ
  assoc θ θ' θ'' := assoc'' F θ θ' θ''

namespace Unstraightening

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃})

/-- The `D2SFib` structure on the unstraightening: the chosen pullbacks and
pushforwards are the images under `F` of the chosen morphisms of `∫(Bᵈᵒ)`, and the chosen lifts are
identities. -/
instance instD2SFib : D2SFib (Unstraightening F) where
  pull β c := vobj F β c
  pullLift _ _ := 𝟙 _
  pullLift_cartesian := by intro _ _ _ _ _ _ _ _ χ; exact ⟨χ, rfl, fun _ h => h⟩
  push := @fun _ _ α b c => hobj F α b c
  pushLift _ _ _ := 𝟙 _
  pushLift_opcartesian := by intro _ _ _ _ _ _ _ _ _ _ χ; exact ⟨χ, rfl, fun _ h => h⟩

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
  (DoubleDisplayed.IsOpcartesian.desc_uniq (pushLift_opcartesian (C := Unstraightening F) α c) _
    rfl).symm

/-- The pullback action of `Unstraightening F` on fiber morphisms is `vmor`. -/
@[rewrite_rule]
theorem pullMap_eq {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') {c c' : (Unstraightening F).Fiber b'}
    (f : c ⟶ c') :
    pullMap (C := Unstraightening F) β f = vmor F β f :=
  (pullDesc_uniq β c' (B.id b) _ _ rfl).symm

end Maps

/-! ### `Φ` on morphisms -/

variable {F} {F' : B.dualOp.Total ⥤ Cat.{v₃, u₃}}

section Naturality

variable {a a' : A}

/-- The component of a natural transformation `κ : F ⟶ F'`, on objects. -/
def kobj (κ : F ⟶ F') {x : B.dualOp.Total} (c : F.obj x) : F'.obj x := (κ.app x).toFunctor.obj c

/-- The component of a natural transformation `κ : F ⟶ F'`, on morphisms. -/
def kmor (κ : F ⟶ F') {x : B.dualOp.Total} {c c' : F.obj x} (θ : c ⟶ c') :
    kobj κ c ⟶ kobj κ c' :=
  (κ.app x).toFunctor.map θ

@[rewrite_rule]
theorem kobj_id {x : B.dualOp.Total} (c : F.obj x) : kobj (𝟙 F) c = c := rfl

@[rewrite_rule]
theorem kmor_idNat {x : B.dualOp.Total} {c c' : F.obj x} (θ : c ⟶ c') : kmor (𝟙 F) θ = θ := rfl

@[rewrite_rule]
theorem kobj_comp {F'' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F') (κ' : F' ⟶ F'')
    {x : B.dualOp.Total} (c : F.obj x) : kobj (κ ≫ κ') c = kobj κ' (kobj κ c) := rfl

@[rewrite_rule]
theorem kmor_compNat {F'' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F') (κ' : F' ⟶ F'')
    {x : B.dualOp.Total} {c c' : F.obj x} (θ : c ⟶ c') :
    kmor (κ ≫ κ') θ = kmor κ' (kmor κ θ) := rfl

theorem kapp_hmap (κ : F ⟶ F') (α : a ⟶ a') (b : B.Ob a) :
    hmap F α b ⋙ (κ.app _).toFunctor = (κ.app _).toFunctor ⋙ hmap F' α b :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualHoriz α b))

theorem kapp_vmap (κ : F ⟶ F') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') :
    vmap F β ⋙ (κ.app _).toFunctor = (κ.app _).toFunctor ⋙ vmap F' β :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualVert β))

theorem kmor_hmor_heq (κ : F ⟶ F') (α : a ⟶ a') (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)}
    (θ : c ⟶ c') : kmor κ (hmor F α b θ) ≍ hmor F' α b (kmor κ θ) :=
  Functor.map_heq_of_eq (kapp_hmap κ α b) θ

theorem kmor_vmor_heq (κ : F ⟶ F') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (B.dualOp.tot b')} (θ : c ⟶ c') :
    kmor κ (vmor F β θ) ≍ vmor F' β (kmor κ θ) :=
  Functor.map_heq_of_eq (kapp_vmap κ β) θ

@[rewrite_rule]
theorem kobj_hobj (κ : F ⟶ F') (α : a ⟶ a') (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    kobj κ (hobj F α b c) = hobj F' α b (kobj κ c) :=
  Functor.congr_obj (kapp_hmap κ α b) c

@[rewrite_rule]
theorem kobj_vobj (κ : F ⟶ F') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    (c : F.obj (B.dualOp.tot b')) : kobj κ (vobj F β c) = vobj F' β (kobj κ c) :=
  Functor.congr_obj (kapp_vmap κ β) c

@[rewrite_rule]
theorem kmor_id (κ : F ⟶ F') {x : B.dualOp.Total} (c : F.obj x) : kmor κ (𝟙 c) = 𝟙 _ :=
  (κ.app x).toFunctor.map_id c

@[rewrite_rule]
theorem kmor_comp (κ : F ⟶ F') {x : B.dualOp.Total} {c c' c'' : F.obj x} (θ : c ⟶ c')
    (θ' : c' ⟶ c'') : kmor κ (θ ≫ θ') = kmor κ θ ≫ kmor κ θ' :=
  (κ.app x).toFunctor.map_comp θ θ'

@[rewrite_rule]
theorem kmor_hmor (κ : F ⟶ F') (α : a ⟶ a') (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)}
    (θ : c ⟶ c') : kmor κ (hmor F α b θ) = hmor F' α b (kmor κ θ) :=
  eq_of_heq (kmor_hmor_heq κ α b θ)

@[rewrite_rule]
theorem kmor_vmor (κ : F ⟶ F') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : F.obj (B.dualOp.tot b')} (θ : c ⟶ c') :
    kmor κ (vmor F β θ) = vmor F' β (kmor κ θ) :=
  eq_of_heq (kmor_vmor_heq κ β θ)

theorem kmor_comp' (κ : F ⟶ F') {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a}
    {b' : B.Ob a'} {b'' : B.Ob a''} {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : Ob F b}
    {c' : Ob F b'} {c'' : Ob F b''} (θ : Hom F g c c') (θ' : Hom F g' c' c'') :
    kmor κ (comp' F θ θ') = comp' F' (kmor κ θ) (kmor κ θ') := rfl

end Naturality

end Unstraightening

/-- Bundled form: the object of `D2SFibCat B` carried by the unstraightening. -/
def unstraightenObj (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B :=
  ⟨Unstraightening F⟩

/-- `Φ` on morphisms: a natural transformation `κ : F ⟶ F'` induces a morphism of D2SFibs, by the
components of `κ`. -/
def unstraightenMap {F F' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F') :
    unstraightenObj F ⟶ unstraightenObj F' where
  toObj :=
    { obj := fun c => Unstraightening.kobj κ c
      map := fun θ => Unstraightening.kmor κ θ
      map_id := fun _ => rfl
      map_comp := fun θ θ' => Unstraightening.kmor_comp' κ θ θ'
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; rfl
  map_pushLift := by intros; rfl

/-- **`Φ`**: the unstraightening as a functor into `D2SFib(A, B)`. -/
def unstraighten : (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ⥤ D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B where
  obj F := unstraightenObj F
  map κ := unstraightenMap κ
  map_id _ := rfl
  map_comp _ _ := rfl

end

end DoubleDisplayed.D2SFib.Straightening
