import CategoryTheory.Opposite.OpFunctor
import Displayed.Opfibration.Straightening.ICatStr
import DoubleDisplayed.Fibration

/-!
# Dependent profunctors

The category `DProf` of dependent profunctors, doubly displayed over `ICatStr`: it is the
Grothendieck construction of the contravariant functor sending `F : A ⥤ Cat` to the category of
functors `(∫ (F ⋙ opFunctor')).Total ⥤ Cat`, over the Grothendieck construction `ICatStr` of
`A ↦ (A ⥤ Cat)`.

A dependent profunctor over `F : A ⥤ Cat` is a functor `P : (∫ (F ⋙ opFunctor')).Total ⥤ Cat` out
of the total category of the unstraightening of the pointwise opposite of `F`, the Grothendieck
construction of `a ↦ (F a)ᵒᵖ`: its objects are the pairs `⟨a, x⟩` with `x : F a`, and its morphisms
`⟨a, x⟩ ⟶ ⟨a', x'⟩` the pairs of `α : a ⟶ a'` and `β : x' ⟶ F α x`. For `F` constant at `B`, it is
a profunctor from `A` to `B`, a functor `A × Bᵒᵖ ⥤ Cat`. This category is the context extension
`Γ ▹ Fᵒᵖ` of the category model, so that the types of the category model in that context are, as
they are, the dependent profunctors over `F`. It is also, by `rfl`, the total category
`(∫ F)ᵒᵖ.Total` of the dual opfibration of `∫ F`, but not reducibly so.

Every morphism of `(∫ (F ⋙ opFunctor')).Total` is a chosen horizontal morphism
`horiz α x : ⟨a, x⟩ ⟶ ⟨a', F α x⟩` followed by a chosen vertical morphism
`vert β : ⟨a, y⟩ ⟶ ⟨a, x⟩`, for `β : x ⟶ y` in `F a` (`eq_horiz_comp_vert`), and these satisfy the
equations of a split opfibration and its interchange by `rfl`. Those along identities and composites
are rules, so that the functor rules fire on the images of these morphisms, which compute to
`totalMk`s, never to identities or composites. They are stated with the operations of the split
opfibration `∫ F`, as the D2SFibs over it are (`(∫ F).push`, `(∫ F).pushMap`), except that the
vertical identities and composites are those of `F a`: the identities `(∫ F).id b` and composites
`β ≫ᵈ γ` of `∫ F` unfold to them, and so do the opcartesian factorizations of composites, so that
rules keyed on `≫ᵈ` would not fire on these.

A strict transformation `τ : StrictTrans F (u ⋙ G)` induces the functor
`totalMap τ : (∫ (F ⋙ opFunctor')).Total ⥤ (∫ (G ⋙ opFunctor')).Total`, `⟨a, x⟩ ↦ ⟨u a, τ x⟩`.
It sends the chosen morphisms to chosen morphisms, by `rfl`, and the identities and composites of
`ICatStr` to identities and composites of functors, as rules. A morphism of dependent profunctors
over `τ` from `P` to `P'` is a natural transformation `P ⟶ totalMap τ ⋙ P'`, and composition
whiskers the second transformation along the first `totalMap`. Over the identities of `ICatStr`,
the fiber of `DProf` over `F` thus has the natural transformations `P ⟶ P'` as morphisms.

`DProf` is a split fibration over `ICatStr` by precomposition: the pullback of `P'` along `τ` is
`totalMap τ ⋙ P'`, with the identity as chosen lift (`DProf.splitDDFib`).

`DProf` is reducible, like Mathlib's `Profunctor`, so that `DProf.Ob F` is a type of functors for
instance search: the morphisms and whiskerings of dependent profunctors are found without further
instances. (The D2SFib structure of the unstraightening of a dependent profunctor over an object of
`ICatStr` needs one, `Unstraightening.instSplitD2SFibICatStr`, since `ICatStr.Ob A` is not reducibly
`A ⥤ Cat`.) This is safe because the category that instance search finds on `DProf.Fiber F`, the
functor category, is the fiber category.
-/

universe v₃ u₃ v₂ u₂ v₁ u₁

namespace DoubleDisplayed

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

namespace DProf

/-! ## The chosen morphisms of `(∫ (F ⋙ opFunctor')).Total` -/

section Generators

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v₂, u₂}} {a a' a'' : A}

/-- The chosen horizontal morphism `⟨a, b⟩ ⟶ ⟨a', F α b⟩` over `α`. -/
def horiz (α : a ⟶ a') (b : (∫ F).Ob a) :
    (∫ (F ⋙ opFunctor')).tot b ⟶ (∫ (F ⋙ opFunctor')).tot ((∫ F).push α b) :=
  (∫ (F ⋙ opFunctor')).totalMk α (𝟙 ((∫ F).push α b))

/-- The chosen vertical morphism `⟨a, b'⟩ ⟶ ⟨a, b⟩` of a vertical morphism `β : b ⟶ b'` of `∫ F`;
it is contravariant. -/
def vert {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') :
    (∫ (F ⋙ opFunctor')).tot b' ⟶ (∫ (F ⋙ opFunctor')).tot b :=
  (∫ (F ⋙ opFunctor')).totalMk (𝟙 a) β

/-- The chosen horizontal morphism over an identity is the identity. -/
@[rewrite_rule]
theorem horiz_id (b : (∫ F).Ob a) : horiz (𝟙 a) b = 𝟙 ((∫ (F ⋙ opFunctor')).tot b) :=
  rfl

/-- The chosen horizontal morphism over a composite is the composite of the chosen horizontal
morphisms. -/
@[rewrite_rule]
theorem horiz_comp (α : a ⟶ a') (α' : a' ⟶ a'') (b : (∫ F).Ob a) :
    horiz (α ≫ α') b = horiz α b ≫ horiz α' ((∫ F).push α b) :=
  rfl

/-- The chosen vertical morphism of an identity is the identity. -/
@[rewrite_rule]
theorem vert_id (b : (∫ F).Ob a) :
    vert (@CategoryStruct.id (F.obj a) _ b) = 𝟙 ((∫ (F ⋙ opFunctor')).tot b) :=
  rfl

/-- `vert` is contravariant. -/
@[rewrite_rule]
theorem vert_comp {b₁ b₂ b₃ : (∫ F).Ob a} (β : b₁ ⟶[𝟙 a] b₂) (γ : b₂ ⟶[𝟙 a] b₃) :
    vert (@CategoryStruct.comp (F.obj a) _ _ _ _ β γ) = vert γ ≫ vert β :=
  rfl

/-- Interchange: pushing a vertical morphism past a chosen horizontal morphism transports it along
`(∫ F).pushMap`. -/
theorem vert_comp_horiz (α : a ⟶ a') {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') :
    vert β ≫ horiz α b = horiz α b' ≫ vert ((∫ F).pushMap α β) :=
  rfl

/-- Every morphism of `(∫ (F ⋙ opFunctor')).Total` is a chosen horizontal morphism followed by a
chosen vertical one. -/
theorem eq_horiz_comp_vert {x y : (∫ (F ⋙ opFunctor')).Total} (h : x ⟶ y) :
    h = horiz (F := F) h.base x.2 ≫ vert (F := F) h.fiber :=
  rfl

end Generators

/-! ## The functor induced by a strict transformation -/

section TotalMap

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₁} [Category.{v₁} B] {u : A ⥤ B}
  {F : A ⥤ Cat.{v₂, u₂}} {G : B ⥤ Cat.{v₂, u₂}} {a a' : A}

/-- **The functor induced by a strict transformation** `τ` over `u`,
`(∫ (F ⋙ opFunctor')).Total ⥤ (∫ (G ⋙ opFunctor')).Total`: `⟨a, x⟩ ↦ ⟨u a, τ x⟩`, and
`⟨α, β⟩ ↦ ⟨u α, τ β⟩`. The identities of `∫ (F ⋙ opFunctor')` are those of the opposite fibers,
on which the rule `StrictTrans.map_id` does not fire, so `map_id` is that rule. -/
def totalMap (τ : StrictTrans F (u ⋙ G)) :
    (∫ (F ⋙ opFunctor')).Total ⥤ (∫ (G ⋙ opFunctor')).Total where
  obj x := (∫ (G ⋙ opFunctor')).tot (τ.toObj.obj x.2)
  map h := (∫ (G ⋙ opFunctor')).totalMk (u.map h.base) (τ.map h.fiber)
  map_id x := congrArg ((∫ (G ⋙ opFunctor')).totalMk (𝟙 (u.obj x.1))) (τ.map_id x.2)
  map_comp _ _ := rfl

/-- `totalMap τ` sends the chosen horizontal morphisms to chosen horizontal morphisms. -/
theorem totalMap_map_horiz (τ : StrictTrans F (u ⋙ G)) (α : a ⟶ a') (b : (∫ F).Ob a) :
    (totalMap τ).map (horiz α b) = horiz (u.map α) ((StrictTrans.unstraighten τ).toPre.obj b) :=
  rfl

/-- `totalMap τ` sends the chosen vertical morphisms to chosen vertical morphisms. -/
theorem totalMap_map_vert (τ : StrictTrans F (u ⋙ G)) {b b' : (∫ F).Ob a} (β : b ⟶[𝟙 a] b') :
    (totalMap τ).map (vert β) = vert ((StrictTrans.unstraighten τ).toPre.map β) :=
  rfl

end TotalMap

/-! The functors that the identities and composites of `ICatStr` induce are the identities and
composites, as rules. -/

section ICatStr

variable {A A' A'' : Cat.{v₁, u₁}} {F : A ⥤ Cat.{v₂, u₂}} {G : A' ⥤ Cat.{v₂, u₂}}
  {H : A'' ⥤ Cat.{v₂, u₂}}

@[rewrite_rule]
theorem totalMap_id (F : A ⥤ Cat.{v₂, u₂}) :
    totalMap (u := (𝟙 A : A ⟶ A).toFunctor) (StrictTrans.id F) = 𝟭 _ :=
  rfl

-- The kernel does not identify the two functors, though it does identify their components.
@[rewrite_rule]
theorem totalMap_comp {u : A ⟶ A'} {u' : A' ⟶ A''} (τ : StrictTrans F (u.toFunctor ⋙ G))
    (σ : StrictTrans G (u'.toFunctor ⋙ H)) :
    totalMap (u := (u ≫ u').toFunctor) (StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ))
      = totalMap (u := u.toFunctor) τ ⋙ totalMap (u := u'.toFunctor) σ :=
  Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

end ICatStr

end DProf

-- The universes of the fibers only occur in the levels of `DProf` through the `max` of the levels
-- of its objects and morphisms.
set_option linter.checkUnivs false in
/-- **The category of dependent profunctors**, doubly displayed over `ICatStr`: over `F : A ⥤ Cat`,
the functors `(∫ (F ⋙ opFunctor')).Total ⥤ Cat`, and over a strict transformation `τ`, the natural
transformations `P ⟶ totalMap τ ⋙ P'`. -/
abbrev DProf : DoubleDisplayed ICatStr.{v₂, u₂, v₁, u₁} where
  Ob {A} (F : A ⥤ Cat.{v₂, u₂}) := (∫ (F ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}
  Hom {_ _ u F G} (τ : StrictTrans F (u.toFunctor ⋙ G)) P P' :=
    P ⟶ DProf.totalMap (u := u.toFunctor) τ ⋙ P'
  id P := 𝟙 P
  comp {_ _ _ u _ F G _ τ _ _ _ _} κ κ' :=
    κ ≫ Functor.whiskerLeft (DProf.totalMap (u := u.toFunctor) (F := F) (G := G) τ) κ'
  comp_id _ := NatTrans.ext (funext fun _ => rfl)
  assoc _ _ _ := NatTrans.ext (funext fun _ => rfl)

/-- The chosen pullback of a dependent profunctor along a strict transformation is the
precomposition with its `totalMap`, with the identity as chosen lift. -/
instance DProf.ddFib : DDFib DProf.{v₃, u₃, v₂, u₂, v₁, u₁} where
  pull {_ _ u _ G} τ (P' : (∫ ((G : _ ⥤ Cat.{v₂, u₂}) ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) :=
    DProf.totalMap (u := u.toFunctor) τ ⋙ P'
  clift {_ _ u _ G} τ (P' : (∫ ((G : _ ⥤ Cat.{v₂, u₂}) ⋙ opFunctor')).Total ⥤ Cat.{v₃, u₃}) :=
    𝟙 (DProf.totalMap (u := u.toFunctor) τ ⋙ P')
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => χ
      lift_fac := fun {_ _ _} _ {_} _ => NatTrans.ext (funext fun _ => rfl)
      lift_uniq := fun {_ _ _ _ _ _} _ h => (NatTrans.ext (funext fun _ => rfl)).trans h }

instance DProf.preSplitDDFib : PreSplitDDFib DProf.{v₃, u₃, v₂, u₂, v₁, u₁} := {}

/-- **`DProf` is a split fibration over `ICatStr`**, by precomposition. -/
instance DProf.splitDDFib : SplitDDFib DProf.{v₃, u₃, v₂, u₂, v₁, u₁} where
  clift_comp _ _ _ := NatTrans.ext (funext fun _ => rfl)

end DoubleDisplayed
