import Displayed.Opfibration.Straightening.Unstraighten
import Displayed.Opfibration.OpcartesianFunctor

/-!
# Indexed categories and strict natural transformations

For a category `A` and functors `F G : A ⥤ Cat`, a *strict natural transformation*
`StrictTrans F G` has components `F a ⥤ G a`, natural on the nose. It is stated by its actions on
objects (`StrictTransObj.obj`) and on morphisms (`StrictTrans.map`), which are dedicated heads for
the rules below, rather than by functors `F a ⥤ G a`: a rule keyed on `Functor.obj` would be tried
on every functor application. Its naturality is a pair of rules,
`τ (F f x) ↦ G f (τ x)` (`StrictTransObj.obj_push`) and `τ (F f φ) ↦ G f (τ φ)`
(`StrictTrans.map_push`), oriented so that the components are innermost, as for the opcartesian
functors of `Opfibration/OpcartesianFunctor.lean`. The rule on objects makes the one on morphisms a
plain equation, so the action on objects is a separate structure, a field of `StrictTrans`.

The category `ICat_str` of indexed categories and strict natural transformations is displayed over
`Cat` (`ICatStr`): an object over `A` is a functor `A ⥤ Cat`, and a morphism over `u : A ⟶ A'`
from `F` to `G` is a strict natural transformation `StrictTrans F (u ⋙ G)`. Its laws hold by
`rfl`. A strict transformation is a lax transformation whose 2-cells are identities
(`StrictTrans.toLaxTrans`), and this inclusion is a vertical functor
`ICatStr.forget : ICatStr ⟶ ICatLax`.

A strict transformation `τ` over `u` unstraightens to an opcartesian functor
`τ.unstraighten : ∫ F ⟶ ∫ G` over `u`. The unstraightening preserves identities and composites
of `ICatStr`, as rules.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

section StrictTrans

variable {A : Type u₁} [Category.{v₁} A]

/-- The action on objects of a strict natural transformation between `F G : A ⥤ Cat`, natural on
the nose. The naturality is a rewrite rule. -/
structure StrictTransObj (F G : A ⥤ Cat.{v, u}) where
  /-- The components on objects. -/
  obj : ∀ {a : A}, F.obj a → G.obj a
  /-- Naturality on objects. -/
  obj_push : ∀ {a a' : A} (f : a ⟶ a') (x : F.obj a),
    obj ((F.map f).toFunctor.obj x) = (G.map f).toFunctor.obj (obj x) := by intros; rfl

attribute [rewrite_rule] StrictTransObj.obj_push

/-- **A strict natural transformation** between `F G : A ⥤ Cat`: components `F a ⥤ G a`, given by
their actions on objects (`toObj`) and morphisms (`map`), with `G f ∘ τ_a = τ_{a'} ∘ F f` on the
nose. Its laws are rewrite rules. -/
structure StrictTrans (F G : A ⥤ Cat.{v, u}) where
  /-- The components on objects. -/
  toObj : StrictTransObj F G
  /-- The components on morphisms. -/
  map : ∀ {a : A} {x y : F.obj a}, (x ⟶ y) → (toObj.obj x ⟶ toObj.obj y)
  map_id : ∀ {a : A} (x : F.obj a), map (𝟙 x) = 𝟙 (toObj.obj x) := by intros; rfl
  map_comp : ∀ {a : A} {x y z : F.obj a} (φ : x ⟶ y) (ψ : y ⟶ z),
    map (φ ≫ ψ) = map φ ≫ map ψ := by intros; rfl
  /-- Naturality on morphisms. -/
  map_push : ∀ {a a' : A} (f : a ⟶ a') {x y : F.obj a} (φ : x ⟶ y),
    map ((F.map f).toFunctor.map φ) = (G.map f).toFunctor.map (map φ) := by intros; rfl

attribute [rewrite_rule] StrictTrans.map_id StrictTrans.map_comp StrictTrans.map_push

namespace StrictTrans

variable {F G H : A ⥤ Cat.{v, u}}

/-- Strict natural transformations are determined by their actions on objects and morphisms. -/
theorem ext {τ σ : StrictTrans F G} (hobj : ∀ {a : A} (x : F.obj a), τ.toObj.obj x = σ.toObj.obj x)
    (hmap : ∀ {a : A} {x y : F.obj a} (φ : x ⟶ y), τ.map φ ≍ σ.map φ) : τ = σ := by
  obtain ⟨⟨obj, _⟩, map, _, _, _⟩ := τ
  obtain ⟨⟨obj', _⟩, map', _, _, _⟩ := σ
  obtain rfl : @obj = @obj' := by
    funext a x
    exact hobj x
  obtain rfl : @map = @map' := by
    funext a x y φ
    exact eq_of_heq (hmap φ)
  rfl

/-- The component of `τ` at `a`, as a functor. -/
def app (τ : StrictTrans F G) (a : A) : F.obj a ⥤ G.obj a where
  obj x := τ.toObj.obj x
  map φ := τ.map φ
  map_id x := τ.map_id x
  map_comp φ ψ := τ.map_comp φ ψ

/-- The identity strict transformation. -/
protected def id (F : A ⥤ Cat.{v, u}) : StrictTrans F F where
  toObj := { obj := fun x => x }
  map φ := φ

/-- Vertical composition of strict transformations. -/
def vcomp (τ : StrictTrans F G) (σ : StrictTrans G H) : StrictTrans F H where
  toObj := { obj := fun x => σ.toObj.obj (τ.toObj.obj x) }
  map φ := σ.map (τ.map φ)

/-- Restriction of a strict transformation along a functor `u : B ⥤ A`. -/
def whiskerLeft {B : Type u₂} [Category.{v₂} B] (u : B ⥤ A) (τ : StrictTrans F G) :
    StrictTrans (u ⋙ F) (u ⋙ G) where
  toObj := { obj := fun x => τ.toObj.obj x, obj_push := fun f x => τ.toObj.obj_push (u.map f) x }
  map φ := τ.map φ
  map_push f _ _ φ := τ.map_push (u.map f) φ

end StrictTrans

end StrictTrans

/-! ## The displayed category of indexed categories -/

/-- **`ICat_str`**: the indexed categories and strict natural transformations, displayed over
`Cat`. An object over `A` is a functor `A ⥤ Cat`, and a morphism over `u : A ⟶ A'` from `F` to `G`
is a strict transformation `StrictTrans F (u ⋙ G)`. Composition restricts the second
transformation along the first base functor. -/
def ICatStr : Displayed.{u, u + 1} Cat.{u, u} where
  Ob A := A ⥤ Cat.{u, u}
  Hom u F G := StrictTrans F (u.toFunctor ⋙ G)
  id F := StrictTrans.id F
  comp {_ _ _ u _ _ _ _} τ σ := StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ)

/-- A strict transformation, as a lax transformation whose 2-cells are identities. -/
def StrictTrans.toLaxTrans {A : Type u₁} [Category.{v₁} A] {F G : A ⥤ Cat.{v, u}}
    (τ : StrictTrans F G) : LaxTrans F G where
  app a := τ.app a
  naturality _ _ := 𝟙 _
  naturality_naturality _ _ _ _ := rfl

/-- The vertical functor `ICatStr ⟶ ICatLax` seeing a strict transformation as a lax one. -/
def ICatStr.forget : VertFunctor ICatStr.{u} ICatLax.{u} where
  obj F := F
  map τ := StrictTrans.toLaxTrans τ
  map_comp _ _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-! ## Unstraightening strict transformations -/

namespace StrictTrans

variable {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B] {u : A ⥤ B} {F : A ⥤ Cat.{v, u}}
  {G : B ⥤ Cat.{v, u}}

/-- **The unstraightening of a strict transformation** `τ` over `u`: the opcartesian functor
`∫ F ⟶ ∫ G` over `u` given by `τ` on objects and on the morphisms `F f x ⟶ y` of `∫ F`. -/
def unstraighten (τ : StrictTrans F (u ⋙ G)) : OpcartesianFunctor u (∫ F) (∫ G) where
  toPre :=
    { obj := fun x => τ.toObj.obj x
      map := fun φ => τ.map φ }

end StrictTrans

namespace ICatStr

variable {A A' A'' : Cat.{u, u}} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}} {H : A'' ⥤ Cat.{u, u}}

/-- The unstraightening of an object of `ICatStr` is a split opfibration. The instance
`unstraightenSplitOpfib` does not apply to it, since `ICatStr.Ob A` is not reducibly `A ⥤ Cat`. -/
instance splitOpfib (F : ICatStr.Ob A) : SplitOpfib (∫ (F : A ⥤ Cat.{u, u})) :=
  unstraightenSplitOpfib F

/-! The unstraightening of the identities and composites of `ICatStr` are the identities and
composites of opcartesian functors, as rules. -/

@[rewrite_rule]
theorem unstraighten_id (F : A ⥤ Cat.{u, u}) :
    StrictTrans.unstraighten (u := (𝟙 A : A ⟶ A).toFunctor) (StrictTrans.id F) =
      OpcartesianFunctor.id (∫ F) := rfl

@[rewrite_rule]
theorem unstraighten_comp {u : A ⟶ A'} {u' : A' ⟶ A''} (τ : StrictTrans F (u.toFunctor ⋙ G))
    (σ : StrictTrans G (u'.toFunctor ⋙ H)) :
    StrictTrans.unstraighten (u := (u ≫ u').toFunctor)
        (StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ)) =
      OpcartesianFunctor.comp (StrictTrans.unstraighten (u := u.toFunctor) τ)
        (StrictTrans.unstraighten (u := u'.toFunctor) σ) := rfl

end ICatStr

end Displayed.Opfibration.Straightening
