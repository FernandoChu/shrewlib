import Displayed.Fibration.Basic
import Rules.Functor
import Mathlib.CategoryTheory.Category.Cat

/-!
# Indexed categories and lax natural transformations

For a category `A`, strict functors `F G : A ⥤ Cat` and *lax natural transformations* between them
(`LaxTrans F G`): functors `app a : F a ⥤ G a` and 2-cells `app a ⋙ G f ⟶ F f ⋙ app a'`, given by
their components `naturality f x : G f (app a x) ⟶ app a' (F f x)`, natural in `x` and compatible
with identities and composites. This is the direction of Mathlib's lax transformations
(`Bicategory.Lax.LaxTrans`) between functors into `Cat`, here stated on objects.

With the functor laws as rules, `G (𝟙 a) y` is `y` and `G (f ≫ g) y` is `G g (G f y)`, so the unit
and composition laws of the 2-cells, which are rules too, are plain equations.

The category of indexed categories and lax transformations is
displayed over `Cat` (`ICatLax`): an object over `A` is a functor `A ⥤ Cat`, and a morphism over
`u : A ⟶ B` from `F` to `G` is a lax transformation `LaxTrans F (u ⋙ G)`. Its laws hold by
`rfl`. Reindexing `ICatLax.pull u G = u ⋙ G` and the identity transformations make it a split
fibration over `Cat`, whose splitting laws hold by `rfl`.
-/

universe v u v₁ u₁ v₂ u₂

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

section LaxTrans

variable {A : Type u₁} [Category.{v₁} A]

/-- A lax natural transformation between strict functors `F G : A ⥤ Cat`: functors
`app a : F a ⥤ G a`, and natural 2-cells `app a ⋙ G f ⟶ F f ⋙ app a'` with components
`naturality f x`, which are the identity at `𝟙 a` and compose at `f ≫ g`. -/
structure LaxTrans (F G : A ⥤ Cat.{v, u}) where
  /-- The component functors. -/
  app : ∀ a, F.obj a ⥤ G.obj a
  /-- The components of the 2-cell `app a ⋙ G f ⟶ F f ⋙ app a'`. -/
  naturality : ∀ {a a' : A} (f : a ⟶ a') (x : F.obj a),
    (G.map f).toFunctor.obj ((app a).obj x) ⟶ (app a').obj ((F.map f).toFunctor.obj x)
  naturality_naturality : ∀ {a a' : A} (f : a ⟶ a') {x y : F.obj a} (φ : x ⟶ y),
    (G.map f).toFunctor.map ((app a).map φ) ≫ naturality f y =
      naturality f x ≫ (app a').map ((F.map f).toFunctor.map φ)
  naturality_id : ∀ {a : A} (x : F.obj a), naturality (𝟙 a) x = 𝟙 ((app a).obj x) := by intros; rfl
  naturality_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : F.obj a),
    naturality (f ≫ g) x =
      (G.map g).toFunctor.map (naturality f x) ≫ naturality g ((F.map f).toFunctor.obj x)
    := by intros; rfl

attribute [rewrite_rule] LaxTrans.naturality_id LaxTrans.naturality_comp

namespace LaxTrans

variable {F G H : A ⥤ Cat.{v, u}}

/-- Lax transformations are determined by their components and 2-cells. -/
theorem ext' {α β : LaxTrans F G}
    (happ_obj : ∀ (a : A) (x : F.obj a), (α.app a).obj x = (β.app a).obj x)
    (happ_map : ∀ (a : A) {x y : F.obj a} (φ : x ⟶ y), (α.app a).map φ ≍ (β.app a).map φ)
    (hnat : ∀ {a a' : A} (f : a ⟶ a') (x : F.obj a), α.naturality f x ≍ β.naturality f x) :
    α = β := by
  obtain ⟨app, nat, _, _, _⟩ := α
  obtain ⟨app', nat', _, _, _⟩ := β
  obtain rfl : app = app' :=
    funext fun a => Functor.hext (happ_obj a) fun _ _ φ => happ_map a φ
  obtain rfl : @nat = @nat' := by
    funext a a' f x
    exact eq_of_heq (hnat f x)
  rfl

/-- The identity lax transformation. -/
protected def id (F : A ⥤ Cat.{v, u}) : LaxTrans F F where
  app _ := 𝟭 _
  naturality _ _ := 𝟙 _
  naturality_naturality {_ _} _ {_ _} _ := rfl

/-- Vertical composition of lax transformations. -/
def vcomp (α : LaxTrans F G) (β : LaxTrans G H) : LaxTrans F H where
  app a := α.app a ⋙ β.app a
  naturality f x := β.naturality f ((α.app _).obj x) ≫ (β.app _).map (α.naturality f x)
  naturality_naturality {a a'} f {x y} φ :=
    (congrArg (· ≫ (β.app a').map (α.naturality f y))
      (β.naturality_naturality f ((α.app a).map φ))).trans
      (congrArg (fun t => β.naturality f ((α.app a).obj x) ≫ (β.app a').map t)
        (α.naturality_naturality f φ))
  naturality_comp {a _ a''} f g x :=
    congrArg (fun t => (H.map g).toFunctor.map (β.naturality f ((α.app a).obj x)) ≫
        t ≫ (β.app a'').map (α.naturality g ((F.map f).toFunctor.obj x)))
      (β.naturality_naturality g (α.naturality f x)).symm

/-- Restriction of a lax transformation along a functor `u : B ⥤ A`. -/
def whiskerLeft {B : Type u₂} [Category.{v₂} B] (u : B ⥤ A) (α : LaxTrans F G) :
    LaxTrans (u ⋙ F) (u ⋙ G) where
  app b := α.app (u.obj b)
  naturality f x := α.naturality (u.map f) x
  naturality_naturality {_ _} f {_ _} φ := α.naturality_naturality (u.map f) φ

end LaxTrans

end LaxTrans

/-! ## The displayed category of indexed categories -/

-- The universes of the fibers `Cat.{v, u}` only occur in the levels of `ICatLax` through the
-- `max` of the levels of its objects and morphisms.
set_option linter.checkUnivs false in
/-- The indexed categories and lax transformations, displayed over `Cat`: an object over `A` is a
functor `A ⥤ Cat`, and a morphism over `u : A ⟶ B` from `F` to `G` is a lax transformation
`LaxTrans F (u ⋙ G)`. Composition restricts the second transformation along the first base
functor. -/
def ICatLax : Displayed Cat.{v₁, u₁} where
  Ob A := A ⥤ Cat.{v, u}
  Hom u F G := LaxTrans F (u.toFunctor ⋙ G)
  id F := LaxTrans.id F
  comp {_ _ _ u _ _ _ _} α β := LaxTrans.vcomp α (LaxTrans.whiskerLeft u.toFunctor β)
  -- The two sides agree componentwise by `rfl`, but the kernel does not see it on the whole
  -- structure, so we go through `ext'`.
  assoc _ _ _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

namespace ICatLax

/-- Reindexing `pull u G = u ⋙ G` of `G : B ⥤ Cat` along `u : A ⟶ B`. -/
def pull {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (G : B ⥤ Cat.{v, u}) : A ⥤ Cat.{v, u} :=
  u.toFunctor ⋙ G

/-- The cartesian lift `pull u G ⟶[u] G`: the identity transformation. -/
def clift {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (G : B ⥤ Cat.{v, u}) :
    ICatLax.{v, u}.Hom u (pull u G) G :=
  LaxTrans.id (u.toFunctor ⋙ G)

/-- The chosen lift is cartesian: a transformation over `g ≫ u` is its own factorization. -/
def isCartesianClift {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (G : B ⥤ Cat.{v, u}) :
    IsCartesian (clift u G) where
  lift _ _ χ := χ
  lift_fac _ _ _ := rfl
  lift_uniq _ hψ := hψ

end ICatLax

/-- **`ICatLax` is a split fibration over `Cat`**, cloven by reindexing `ICatLax.pull u G = u ⋙ G`,
with the identity transformations as chosen lifts. -/
instance ICatLax.preSplitFib : PreSplitFib ICatLax.{v, u, v₁, u₁} where
  pull u G := ICatLax.pull u G
  clift u G := ICatLax.clift u G
  isCartesianClift u G := ICatLax.isCartesianClift u G

instance ICatLax.splitFib : SplitFib ICatLax.{v, u, v₁, u₁} := {}

end Displayed.Opfibration.Straightening
