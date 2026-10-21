import ComprehensionCategory.Basic
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

The category `ICat_lax = Cat ⋉⁻ [−, Cat]_lax` of indexed categories and lax transformations is
displayed over `Cat` (`ICat`): an object over `A` is a functor `A ⥤ Cat`, and a morphism over
`u : A ⟶ B` from `F` to `G` is a lax transformation `F ⇒ u ⋙ G`. Its laws hold by `rfl`.
Reindexing `u^* G = u ⋙ G` and the identity transformations make it a split fibration over `Cat`,
whose splitting laws hold by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v u

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
  naturality_id : ∀ {a : A} (x : F.obj a), naturality (𝟙 a) x = 𝟙 ((app a).obj x)
  naturality_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : F.obj a),
    naturality (f ≫ g) x =
      (G.map g).toFunctor.map (naturality f x) ≫ naturality g ((F.map f).toFunctor.obj x)

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
  naturality_id _ := rfl
  naturality_comp _ _ _ := rfl

/-- Vertical composition of lax transformations. -/
def vcomp (α : LaxTrans F G) (β : LaxTrans G H) : LaxTrans F H where
  app a := α.app a ⋙ β.app a
  naturality f x := β.naturality f ((α.app _).obj x) ≫ (β.app _).map (α.naturality f x)
  naturality_naturality {a a'} f {x y} φ :=
    (congrArg (· ≫ (β.app a').map (α.naturality f y))
      (β.naturality_naturality f ((α.app a).map φ))).trans
      (congrArg (fun t => β.naturality f ((α.app a).obj x) ≫ (β.app a').map t)
        (α.naturality_naturality f φ))
  naturality_id _ := rfl
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
  naturality_id _ := rfl
  naturality_comp _ _ _ := rfl

end LaxTrans

end LaxTrans

/-! ## The displayed category of indexed categories -/

/-- `ICat_lax`, displayed over `Cat`: an object over `A` is a functor `A ⥤ Cat`, and a morphism
over `u : A ⟶ B` from `F` to `G` is a lax transformation `F ⇒ u ⋙ G`. Composition restricts the
second transformation along the first base functor. -/
def ICat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := A ⥤ Cat.{u, u}
  Hom u F G := LaxTrans F (u.toFunctor ⋙ G)
  id F := LaxTrans.id F
  comp {_ _ _ u _ _ _ _} α β := LaxTrans.vcomp α (LaxTrans.whiskerLeft u.toFunctor β)
  id_comp _ := rfl
  comp_id _ := rfl
  -- The two sides agree componentwise by `rfl`, but the kernel does not see it on the whole
  -- structure, so we go through `ext'`.
  assoc _ _ _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

namespace ICat

/-- Reindexing `u^* G = u ⋙ G` of `G : B ⥤ Cat` along `u : A ⟶ B`. -/
def pull {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : A ⥤ Cat.{u, u} :=
  u.toFunctor ⋙ G

/-- The cartesian lift `u^* G ⟶[u] G`: the identity transformation. -/
def clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) : ICat.Hom u (pull u G) G :=
  LaxTrans.id (u.toFunctor ⋙ G)

theorem isCartesian_clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Cat.{u, u}) :
    IsCartesian (clift u G) := by
  intro _ _ _ χ
  refine ⟨χ, rfl, fun ψ hψ => ?_⟩
  subst hψ
  rfl

end ICat

/-- **`ICat` is a split fibration over `Cat`**, cloven by reindexing `u^* G = u ⋙ G`, with the
identity transformations as chosen lifts. -/
instance ICat.preSplitFib : PreSplitFib ICat.{u} where
  pull u G := ICat.pull u G
  clift u G := ICat.clift u G
  clift_cartesian u G := ICat.isCartesian_clift u G
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

instance ICat.splitFib : SplitFib ICat.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

end Displayed.Opfibration.Straightening
