import DoubleDisplayed.D2SFib.Straightening.DProf
import DoubleDisplayed.D2SFib.D2SFibStr
import Displayed.Opfibration.Straightening.Str

/-!
# Unstraightening: the dependent 2-sided Grothendieck construction

Given a dependent profunctor `P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat` over `F : A ⥤ Cat`, we build a
doubly displayed category `Unstraightening P` over `∫ F` (the dependent 2-sided Grothendieck
construction), and equip it with a split `D2SFib` structure (`unstraightenObj P`). A morphism of
dependent profunctors over a strict transformation `τ` gives a map of D2SFibs over
`τ.unstraighten` (`unstraightenStrMap`), which makes the unstraightening a doubly displayed functor
`unstraighten : DProf ⟶ D2SFibStr` over `unstraightenStr : ICatStr ⟶ SplitOpfibStr`.

The objects of `Unstraightening P` over `b : F a` are the objects of `P ⟨a, b⟩`, and a morphism
over `g : (∫ F).Hom α b b'` from `c` to `c'` is a morphism
`hobj α c ⟶ vobj ((∫ F).opcartesianFactor g) c'` of `P ⟨a', F α b⟩`. Here `hobj`/`hmor` and
`vobj`/`vmor` are the actions of `P` on objects and morphisms along the chosen horizontal and
vertical morphisms `horiz` and `vert`.

The functoriality of `P` along these, and the interchange of vertical with horizontal morphisms,
are rewrite rules. They have their own heads `hobj`, `hmor`, `vobj` and `vmor`, rather than
`Functor.obj` and `Functor.map`, so that they are only tried where they can apply. (The functor
laws `P.map (𝟙 x) ↦ 𝟙 (P.obj x)` and `P.map (u ≫ v) ↦ P.map u ≫ P.map v` of `Rules.Functor`, which
this file sees through `Displayed/Displayed/Basic.lean`, do not do this. The morphisms of
`(∫ (F ⋙ opFunctor')).Total` compute, so for a variable `u`, `P.map u` is not definitionally equal
to `P.map (horiz _ _) ≫ P.map (vert _)`, the splitting of `P.map (horiz _ _ ≫ vert _)`. They do
fire along identities and composites of the chosen morphisms, which are rules in `DProf.lean`, so
`hmap_id`, `hmap_comp`, `vmap_id` and `vmap_comp` hold by `rfl`.) The rules along vertical
identities and composites are stated with the identities and composites of `F a`, to which those
of `∫ F` unfold, as for `vert`. As a result, composition in
`Unstraightening P` is `hmor α' θ ≫ vmor ((∫ F).pushMap α' ((∫ F).opcartesianFactor g)) θ'`, with
no `eqToHom`, and its laws and its `D2SFib` structure hold by `rfl`.

As for the transformations between functors on the same category, the components of a morphism
`κ : P ⟶ totalMap τ ⋙ P'` on objects and morphisms have their own heads, `Str.tobj` and `Str.tmor`,
and their naturality along the chosen morphisms is a set of rules. Along `horiz α x` it is the
transport `hobj` of `P'` along `u α`, and along `vert β` the transport `vobj` of `P'` along `τ β`,
since `totalMap τ` sends these chosen morphisms to chosen morphisms. The components of a composite
`κ ≫ whiskerLeft (totalMap τ) κ'` are rules too, so that `tobj` and `tmor` are kept when it is
unfolded. With these rules, `unstraightenStrMap κ` is a functor and preserves the chosen lifts by
`rfl`.
-/

universe v₃ u₃ v₂ u₂ v₁ u₁

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib DProf

open scoped Displayed DoubleDisplayed Displayed.Opfibration.Straightening

open Displayed.Opfibration.Straightening (ICatStr StrictTrans)



section

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v₂, u₂}}

namespace Unstraightening

variable (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃})

/-! ### `P` along the chosen morphisms of `(∫ (F ⋙ opFunctor')).Total` -/

section Generators

variable {a a' a'' : A}

/-- `P` along the chosen horizontal morphism `horiz α b`. -/
def hmap (α : a ⟶ a') (b : (∫ F).Ob a) :
    P.obj ((∫ (F ⋙ opFunctor')).tot b) ⥤ P.obj ((∫ (F ⋙ opFunctor')).tot ((∫ F).push α b)) :=
  (P.map (horiz α b)).toFunctor

/-- `P` along the chosen vertical morphism `vert β`. -/
def vmap {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') :
    P.obj ((∫ (F ⋙ opFunctor')).tot b') ⥤ P.obj ((∫ (F ⋙ opFunctor')).tot b) :=
  (P.map (vert β)).toFunctor

/-- `hmap` on objects. -/
def hobj (α : a ⟶ a') (b : (∫ F).Ob a) (c : P.obj ((∫ (F ⋙ opFunctor')).tot b)) :
    P.obj ((∫ (F ⋙ opFunctor')).tot ((∫ F).push α b)) :=
  (hmap P α b).obj c

/-- `hmap` on morphisms. -/
def hmor (α : a ⟶ a') (b : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    hobj P α b c ⟶ hobj P α b c' :=
  (hmap P α b).map θ

/-- `vmap` on objects. -/
def vobj {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (c : P.obj ((∫ (F ⋙ opFunctor')).tot b')) :
    P.obj ((∫ (F ⋙ opFunctor')).tot b) :=
  (vmap P β).obj c

/-- `vmap` on morphisms. -/
def vmor {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b')}
    (θ : c ⟶ c') : vobj P β c ⟶ vobj P β c' :=
  (vmap P β).map θ

theorem hmap_id (b : (∫ F).Ob a) : hmap P (𝟙 a) b = 𝟭 _ :=
  rfl

theorem hmap_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : (∫ F).Ob a) :
    hmap P (α ≫ α') b = hmap P α b ⋙ hmap P α' ((∫ F).push α b) :=
  rfl

theorem vmap_id (b : (∫ F).Ob a) : vmap P (@CategoryStruct.id (F.obj a) _ b) = 𝟭 _ :=
  rfl

theorem vmap_comp {b b' b'' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'') :
    vmap P (@CategoryStruct.comp (F.obj a) _ _ _ _ β γ) = vmap P γ ⋙ vmap P β :=
  rfl

theorem vmap_hmap (α : a ⟶ a') {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') :
    vmap P β ⋙ hmap P α b = hmap P α b' ⋙ vmap P ((∫ F).pushMap α β) :=
  (congrArg Cat.Hom.toFunctor (P.map_comp (vert β) (horiz α b))).symm.trans
    (congrArg Cat.Hom.toFunctor (P.map_comp (horiz α b') (vert ((∫ F).pushMap α β))))

/-! The actions on morphisms along identities, composites and the interchange are first stated as
`≍`, before the corresponding rules on objects are declared: once they are, `hobj P (𝟙 a) b c` is no
longer recognizably its own unfolding `(hmap P (𝟙 a) b).obj c`. The rules on objects then make the
two sides of each `≍` have the same type. -/

theorem hmor_idBase_heq (b : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    hmor P (𝟙 a) b θ ≍ θ := Functor.hcongr_hom (hmap_id P b) θ

theorem hmor_compBase_heq (α : a ⟶ a') (α' : a' ⟶ a'') (b : (∫ F).Ob a)
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    hmor P (α ≫ α') b θ ≍ hmor P α' ((∫ F).push α b) (hmor P α b θ) :=
  Functor.hcongr_hom (hmap_comp P α α' b) θ

theorem vmor_idBase_heq (b : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    vmor P (@CategoryStruct.id (F.obj a) _ b) θ ≍ θ := Functor.hcongr_hom (vmap_id P b) θ

theorem vmor_compBase_heq {b b' b'' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b'')} (θ : c ⟶ c') :
    vmor P (@CategoryStruct.comp (F.obj a) _ _ _ _ β γ) θ ≍ vmor P β (vmor P γ θ) :=
  Functor.hcongr_hom (vmap_comp P β γ) θ

theorem hmor_vmor_heq (α : a ⟶ a') {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b')} (θ : c ⟶ c') :
    hmor P α b (vmor P β θ) ≍ vmor P ((∫ F).pushMap α β) (hmor P α b' θ) :=
  Functor.hcongr_hom (vmap_hmap P α β) θ

@[rewrite_rule]
theorem hobj_id (b : (∫ F).Ob a) (c : P.obj ((∫ (F ⋙ opFunctor')).tot b)) : hobj P (𝟙 a) b c = c :=
  Functor.congr_obj (hmap_id P b) c

@[rewrite_rule]
theorem hobj_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : (∫ F).Ob a)
    (c : P.obj ((∫ (F ⋙ opFunctor')).tot b)) :
    hobj P (α ≫ α') b c = hobj P α' ((∫ F).push α b) (hobj P α b c) :=
  Functor.congr_obj (hmap_comp P α α' b) c

@[rewrite_rule]
theorem vobj_id (b : (∫ F).Ob a) (c : P.obj ((∫ (F ⋙ opFunctor')).tot b)) :
    vobj P (@CategoryStruct.id (F.obj a) _ b) c = c :=
  Functor.congr_obj (vmap_id P b) c

@[rewrite_rule]
theorem vobj_comp {b b' b'' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    (c : P.obj ((∫ (F ⋙ opFunctor')).tot b'')) :
    vobj P (@CategoryStruct.comp (F.obj a) _ _ _ _ β γ) c = vobj P β (vobj P γ c) :=
  Functor.congr_obj (vmap_comp P β γ) c

@[rewrite_rule]
theorem hobj_vobj (α : a ⟶ a') {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b')
    (c : P.obj ((∫ (F ⋙ opFunctor')).tot b')) :
    hobj P α b (vobj P β c) = vobj P ((∫ F).pushMap α β) (hobj P α b' c) :=
  Functor.congr_obj (vmap_hmap P α β) c

@[rewrite_rule]
theorem hmor_id (α : a ⟶ a') (b : (∫ F).Ob a) (c : P.obj ((∫ (F ⋙ opFunctor')).tot b)) :
    hmor P α b (𝟙 c) = 𝟙 _ := (hmap P α b).map_id c

@[rewrite_rule]
theorem hmor_comp (α : a ⟶ a') (b : (∫ F).Ob a) {c c' c'' : P.obj ((∫ (F ⋙ opFunctor')).tot b)}
    (θ : c ⟶ c') (θ' : c' ⟶ c'') : hmor P α b (θ ≫ θ') = hmor P α b θ ≫ hmor P α b θ' :=
  (hmap P α b).map_comp θ θ'

@[rewrite_rule]
theorem vmor_id {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (c : P.obj ((∫ (F ⋙ opFunctor')).tot b')) :
    vmor P β (𝟙 c) = 𝟙 _ := (vmap P β).map_id c

@[rewrite_rule]
theorem vmor_comp {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b')
    {c c' c'' : P.obj ((∫ (F ⋙ opFunctor')).tot b')} (θ : c ⟶ c') (θ' : c' ⟶ c'') :
    vmor P β (θ ≫ θ') = vmor P β θ ≫ vmor P β θ' :=
  (vmap P β).map_comp θ θ'

@[rewrite_rule]
theorem hmor_idBase (b : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    hmor P (𝟙 a) b θ = θ :=
  eq_of_heq (hmor_idBase_heq P b θ)

@[rewrite_rule]
theorem hmor_compBase (α : a ⟶ a') (α' : a' ⟶ a'') (b : (∫ F).Ob a)
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    hmor P (α ≫ α') b θ = hmor P α' ((∫ F).push α b) (hmor P α b θ) :=
  eq_of_heq (hmor_compBase_heq P α α' b θ)

@[rewrite_rule]
theorem vmor_idBase (b : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b)} (θ : c ⟶ c') :
    vmor P (@CategoryStruct.id (F.obj a) _ b) θ = θ :=
  eq_of_heq (vmor_idBase_heq P b θ)

@[rewrite_rule]
theorem vmor_compBase {b b' b'' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') (γ : b' ⟶[𝟙 a] b'')
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b'')} (θ : c ⟶ c') :
    vmor P (@CategoryStruct.comp (F.obj a) _ _ _ _ β γ) θ = vmor P β (vmor P γ θ) :=
  eq_of_heq (vmor_compBase_heq P β γ θ)

@[rewrite_rule]
theorem hmor_vmor (α : a ⟶ a') {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b')
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot b')} (θ : c ⟶ c') :
    hmor P α b (vmor P β θ) = vmor P ((∫ F).pushMap α β) (hmor P α b' θ) :=
  eq_of_heq (hmor_vmor_heq P α β θ)

/-- `P` on an arbitrary morphism of `(∫ (F ⋙ opFunctor')).Total`, which factors as a chosen
horizontal morphism followed by a vertical one. -/
theorem map_eq {x x' : (∫ (F ⋙ opFunctor')).Total} (u : x ⟶ x') :
    (P.map u).toFunctor = hmap P u.base x.2 ⋙ vmap (F := F) P u.fiber :=
  congrArg Cat.Hom.toFunctor
    (P.map_comp (horiz (F := F) u.base x.2) (vert (F := F) u.fiber))

end Generators

end Unstraightening

open Unstraightening in
/-- **The unstraightening of `P`**, the dependent 2-sided Grothendieck construction: the doubly
displayed category over `∫ F` associated with a dependent profunctor
`P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat`. Its objects over `b : F a` are those of `P ⟨a, b⟩`, its
morphisms over `g : (∫ F).Hom α b b'` are those of `P(a', F(α)b)` from `P(α,id)c` to `P(id,β)c'`,
for `β` the opcartesian factorization of `g`, and the composite of `θ` and `θ'` over `g` and `g'` is
`P(α',id)θ ≫ P(id, F(α')β)θ'`. -/
def Unstraightening (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) :
    DoubleDisplayed.{v₃, u₃} (∫ F) where
  Ob b := P.obj ((∫ (F ⋙ opFunctor')).tot b)
  Hom {_ _ α b _} g c c' := hobj P α b c ⟶ vobj P ((∫ F).opcartesianFactor g) c'
  id c := 𝟙 c
  comp {_ _ _ α α' b _ _ g _ _ _ _} θ θ' :=
    hmor P α' ((∫ F).push α b) θ ≫ vmor P ((∫ F).pushMap α' ((∫ F).opcartesianFactor g)) θ'

namespace Unstraightening

variable (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃})

/-- The `D2SFib` structure on the unstraightening: the chosen pullbacks and pushforwards are the
images under `P` of the chosen morphisms of `(∫ (F ⋙ opFunctor')).Total`, and the chosen lifts are
identities. -/
instance instD2SFib : D2SFib (Unstraightening P) where
  pull β c := vobj P β c
  pullLift _ _ := 𝟙 _
  isCartesianPullLift _ _ := ⟨fun _ _ χ => χ, fun _ _ _ => rfl, fun _ h => h⟩
  push := @fun _ _ α b c => hobj P α b c
  pushLift _ _ _ := 𝟙 _
  isOpcartesianPushLift _ _ _ := ⟨fun _ _ χ => χ, fun _ _ _ => rfl, fun _ h => h⟩

instance instPreSplitD2SFib : PreSplitD2SFib (Unstraightening P) := {}

instance instSplitD2SFib : SplitD2SFib (Unstraightening P) := {}

/-- The unstraightening of a dependent profunctor over an object of `ICatStr` is a split D2SFib.
The instance `instSplitD2SFib` does not apply to it, since `ICatStr.Ob A` is not reducibly
`A ⥤ Cat`. -/
instance instSplitD2SFibICatStr {A : Cat.{v₁, u₁}} {F : ICatStr.{v₂, u₂, v₁, u₁}.Ob A}
    (P : DProf.{v₃, u₃}.Ob F) :
    SplitD2SFib (Unstraightening (F := (F : A ⥤ Cat.{v₂, u₂})) P) :=
  instSplitD2SFib P

section Maps

variable {a a' : A}

/-- The pushforward action of `Unstraightening P` on fiber morphisms is `hmor`. -/
@[rewrite_rule]
theorem pushMap_eq (α : a ⟶ a') {b : (∫ F).Ob a} {c c' : (Unstraightening P).Fiber b} (f : c ⟶ c') :
    pushMap (C := Unstraightening P) α f = hmor P α b f :=
  (DoubleDisplayed.IsOpcartesian.desc_uniq (isOpcartesianPushLift (C := Unstraightening P) α c) _
    rfl).symm

/-- The pullback action of `Unstraightening P` on fiber morphisms is `vmor`. -/
@[rewrite_rule]
theorem pullMap_eq {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') {c c' : (Unstraightening P).Fiber b'}
    (f : c ⟶ c') :
    pullMap (C := Unstraightening P) β f = vmor P β f :=
  (pullDesc_uniq β c' ((∫ F).id b) _ _ rfl).symm

end Maps

end Unstraightening

/-- Bundled form: the object of `D2SFibCat (∫ F)` carried by the unstraightening. -/
def unstraightenObj (P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) :
    D2SFibCat.{v₃, u₃} (∫ F) :=
  ⟨Unstraightening P⟩

end

section Morphisms

open Unstraightening

variable {A A' : Cat.{v₁, u₁}} {u : A ⟶ A'} {F : A ⥤ Cat.{v₂, u₂}} {G : A' ⥤ Cat.{v₂, u₂}}
  {τ : StrictTrans F (u.toFunctor ⋙ G)} {P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}}
  {P' : (∫ (G ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}}

/-! ## The components of a morphism of dependent profunctors -/

namespace Str

/-- The component of `κ : P ⟶ totalMap τ ⋙ P'`, on objects. -/
def tobj (κ : P ⟶ totalMap τ ⋙ P') {x : (∫ (F ⋙ opFunctor')).Total} (c : P.obj x) :
    P'.obj ((totalMap τ).obj x) :=
  (κ.app x).toFunctor.obj c

/-- The component of `κ : P ⟶ totalMap τ ⋙ P'`, on morphisms. -/
def tmor (κ : P ⟶ totalMap τ ⋙ P') {x : (∫ (F ⋙ opFunctor')).Total} {c c' : P.obj x}
    (θ : c ⟶ c') : tobj κ c ⟶ tobj κ c' :=
  (κ.app x).toFunctor.map θ

variable (κ : P ⟶ totalMap τ ⋙ P') {a a' : A}

theorem tapp_hmap (α : a ⟶ a') (x : (∫ F).Ob a) :
    hmap P α x ⋙ (κ.app ((∫ (F ⋙ opFunctor')).tot ((∫ F).push α x))).toFunctor =
      (κ.app ((∫ (F ⋙ opFunctor')).tot x)).toFunctor ⋙
        hmap P' (u.toFunctor.map α) (τ.unstraighten.toPre.obj x) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (horiz α x))

theorem tapp_vmap {x y : (∫ F).Ob a} (β : x ⟶[𝟙 a] y) :
    vmap P β ⋙ (κ.app ((∫ (F ⋙ opFunctor')).tot x)).toFunctor =
      (κ.app ((∫ (F ⋙ opFunctor')).tot y)).toFunctor ⋙ vmap P' (τ.unstraighten.toPre.map β) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (vert (F := F) β))

theorem tmor_hmor_heq (α : a ⟶ a') (x : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot x)}
    (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) ≍ hmor P' (u.toFunctor.map α) (τ.unstraighten.toPre.obj x) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_hmap κ α x) θ

theorem tmor_vmor_heq {x y : (∫ F).Ob a} (β : x ⟶[𝟙 a] y)
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P β θ) ≍ vmor P' (τ.unstraighten.toPre.map β) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_vmap κ β) θ

@[rewrite_rule]
theorem tobj_hobj (α : a ⟶ a') (x : (∫ F).Ob a) (c : P.obj ((∫ (F ⋙ opFunctor')).tot x)) :
    tobj κ (hobj P α x c) = hobj P' (u.toFunctor.map α) (τ.unstraighten.toPre.obj x) (tobj κ c) :=
  Functor.congr_obj (tapp_hmap κ α x) c

@[rewrite_rule]
theorem tobj_vobj {x y : (∫ F).Ob a} (β : x ⟶[𝟙 a] y) (c : P.obj ((∫ (F ⋙ opFunctor')).tot y)) :
    tobj κ (vobj P β c) = vobj P' (τ.unstraighten.toPre.map β) (tobj κ c) :=
  Functor.congr_obj (tapp_vmap κ β) c

@[rewrite_rule]
theorem tmor_id {x : (∫ (F ⋙ opFunctor')).Total} (c : P.obj x) : tmor κ (𝟙 c) = 𝟙 _ :=
  (κ.app x).toFunctor.map_id c

@[rewrite_rule]
theorem tmor_comp {x : (∫ (F ⋙ opFunctor')).Total} {c c' c'' : P.obj x} (θ : c ⟶ c')
    (θ' : c' ⟶ c'') : tmor κ (θ ≫ θ') = tmor κ θ ≫ tmor κ θ' :=
  (κ.app x).toFunctor.map_comp θ θ'

@[rewrite_rule]
theorem tmor_hmor (α : a ⟶ a') (x : (∫ F).Ob a) {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot x)}
    (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) = hmor P' (u.toFunctor.map α) (τ.unstraighten.toPre.obj x) (tmor κ θ) :=
  eq_of_heq (tmor_hmor_heq κ α x θ)

@[rewrite_rule]
theorem tmor_vmor {x y : (∫ F).Ob a} (β : x ⟶[𝟙 a] y)
    {c c' : P.obj ((∫ (F ⋙ opFunctor')).tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P β θ) = vmor P' (τ.unstraighten.toPre.map β) (tmor κ θ) :=
  eq_of_heq (tmor_vmor_heq κ β θ)

/-! The components of composites of morphisms of dependent profunctors, as rules, so that the
heads `tobj` and `tmor` are kept when a composite is unfolded. -/

variable {A'' : Cat.{v₁, u₁}} {u' : A' ⟶ A''} {H : A'' ⥤ Cat.{v₂, u₂}}
  {σ : StrictTrans G (u'.toFunctor ⋙ H)} {P'' : (∫ (H ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}}

@[rewrite_rule]
theorem tobj_compNat (κ' : P' ⟶ totalMap σ ⋙ P'') {x : (∫ (F ⋙ opFunctor')).Total}
    (c : P.obj x) :
    tobj (u := u ≫ u') (τ := StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ))
      (P' := P'') (κ ≫ Functor.whiskerLeft (totalMap τ) κ') c = tobj κ' (tobj κ c) :=
  rfl

@[rewrite_rule]
theorem tmor_compNat (κ' : P' ⟶ totalMap σ ⋙ P'') {x : (∫ (F ⋙ opFunctor')).Total}
    {c c' : P.obj x} (θ : c ⟶ c') :
    tmor (u := u ≫ u') (τ := StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ))
      (P' := P'') (κ ≫ Functor.whiskerLeft (totalMap τ) κ') θ = tmor κ' (tmor κ θ) :=
  rfl

end Str

/-! ## `unstraighten` -/

open Str in
/-- **The unstraightening of a morphism of dependent profunctors** `κ : P ⟶ totalMap τ ⋙ P'` over
`τ`: the map of D2SFibs over `τ.unstraighten` given by the components of `κ`. -/
def unstraightenStrMap (κ : P ⟶ totalMap τ ⋙ P') :
    D2SFibMap τ.unstraighten (Unstraightening P) (Unstraightening P') where
  toObj :=
    { obj := fun c => tobj κ c
      map := fun θ => tmor κ θ }

/-- **The unstraightening of dependent profunctors**, a doubly displayed functor over the
unstraightening `ICatStr ⟶ SplitOpfibStr` of indexed categories: a dependent profunctor `P` over
`F` goes to its unstraightening, a split D2SFib over `∫ F`, and a morphism over `τ` to the map of
D2SFibs over `τ.unstraighten` given by its components. -/
def unstraighten :
    DDFunctor Displayed.Opfibration.Straightening.unstraightenStr DProf.{v₃, u₃, v₂, u₂, v₁, u₁}
      D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁} where
  obj P := unstraightenObj P
  map {_ _ _ _ _ τ _ _} κ := unstraightenStrMap (τ := τ) κ
  map_comp _ _ := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)

end Morphisms

end DoubleDisplayed.D2SFib.Straightening
