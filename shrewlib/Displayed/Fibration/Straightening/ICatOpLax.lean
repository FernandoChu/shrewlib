import Displayed.Fibration.Basic
import Rules.Opposite
import Tactic.KernelTactic
import Mathlib.CategoryTheory.Category.Cat

/-!
# Contravariant indexed categories and lax natural transformations

For a category `A`, strict functors `F G : Aᵒᵖ ⥤ Cat` and *lax natural transformations* between
them (`LaxTrans F G`): functors `app a : F (op a) ⥤ G (op a)` and 2-cells
`F f ⋙ app a ⟶ app a' ⋙ G f` for `f : a ⟶ a'`, where `F f` stands for `F.map f.op`, given by
their components `naturality f y : app a (F f y) ⟶ G f (app a' y)`, natural in `y` and
compatible with identities and composites. This is the dual of
`Opfibration/Straightening/ICatLax.lean`.

With the functor laws as rules, including those on opposites (`Rules.Opposite`), `G (𝟙 a) y` is
`y` and `G (f ≫ g) y` is `G f (G g y)`, so the unit and composition laws of the 2-cells, which are
rules too, are plain equations.

The category of contravariant indexed categories and lax transformations is displayed over `Cat`
(`ICatOpLax`): an object over `A` is a functor `Aᵒᵖ ⥤ Cat`, and a morphism over `u : A ⟶ B` from `F`
to `G` is a lax transformation `LaxTrans F (reindex u G)`, where `reindex u G` is `u.op ⋙ G` written
out. Its laws hold by `rfl`. Reindexing `ICatOpLax.pull u G = reindex u G` and the identity
transformations make it a split fibration over `Cat`, whose splitting laws hold by `rfl`.

Some of these definitional equalities are checked in the kernel (`kernel_exact`, `kernel_rfl'`):
the elaborator is slow on them, as it tries the rules on opposites at every `Functor.map`.
-/

universe v₁ u₁ v₂ u₂ v u

namespace Displayed.Fibration.Straightening

open CategoryTheory Opposite Displayed

open scoped Displayed

section LaxTrans

variable {A : Type u₁} [Category.{v₁} A]

/-- The reindexing `reindex u G` of `G : Bᵒᵖ ⥤ Cat` along `u : A ⥤ B`, sending `a` to
`G (op (u a))` and `f` to `G.map (u.map f).op`. It is `u.op ⋙ G`, written out: through
`Functor.op`, the rules on opposites and on functors do not terminate. -/
def reindex {B : Type u₂} [Category.{v₂} B] (u : A ⥤ B) (G : Bᵒᵖ ⥤ Cat.{v, u}) :
    Aᵒᵖ ⥤ Cat.{v, u} where
  obj a := G.obj (op (u.obj a.unop))
  map f := G.map (u.map f.unop).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A lax natural transformation between strict functors `F G : Aᵒᵖ ⥤ Cat`: functors
`app a : F (op a) ⥤ G (op a)`, and natural 2-cells `F f ⋙ app a ⟶ app a' ⋙ G f` with components
`naturality f y`, which are the identity at `𝟙 a` and compose at `f ≫ g`. -/
structure LaxTrans (F G : Aᵒᵖ ⥤ Cat.{v, u}) where
  /-- The component functors. -/
  app : ∀ a : A, F.obj (op a) ⥤ G.obj (op a)
  /-- The components of the 2-cell `F f ⋙ app a ⟶ app a' ⋙ G f`. -/
  naturality : ∀ {a a' : A} (f : a ⟶ a') (y : F.obj (op a')),
    (app a).obj ((F.map f.op).toFunctor.obj y) ⟶ (G.map f.op).toFunctor.obj ((app a').obj y)
  naturality_naturality : ∀ {a a' : A} (f : a ⟶ a') {x y : F.obj (op a')} (φ : x ⟶ y),
    (app a).map ((F.map f.op).toFunctor.map φ) ≫ naturality f y =
      naturality f x ≫ (G.map f.op).toFunctor.map ((app a').map φ)
  naturality_id : ∀ {a : A} (y : F.obj (op a)), naturality (𝟙 a) y = 𝟙 ((app a).obj y)
    := by intros; rfl
  naturality_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : F.obj (op a'')),
    naturality (f ≫ g) y =
      naturality f ((F.map g.op).toFunctor.obj y) ≫ (G.map f.op).toFunctor.map (naturality g y)
    := by intros; rfl

attribute [rewrite_rule] LaxTrans.naturality_id LaxTrans.naturality_comp

namespace LaxTrans

variable {F G H : Aᵒᵖ ⥤ Cat.{v, u}}

/-- Lax transformations are determined by their components and 2-cells. -/
theorem ext' {α β : LaxTrans F G}
    (happ_obj : ∀ (a : A) (x : F.obj (op a)), (α.app a).obj x = (β.app a).obj x)
    (happ_map : ∀ (a : A) {x y : F.obj (op a)} (φ : x ⟶ y), (α.app a).map φ ≍ (β.app a).map φ)
    (hnat : ∀ {a a' : A} (f : a ⟶ a') (y : F.obj (op a')), α.naturality f y ≍ β.naturality f y) :
    α = β := by
  obtain ⟨app, nat, _, _, _⟩ := α
  obtain ⟨app', nat', _, _, _⟩ := β
  obtain rfl : app = app' :=
    funext fun a => Functor.hext (happ_obj a) fun _ _ φ => happ_map a φ
  obtain rfl : @nat = @nat' := by
    funext a a' f y
    exact eq_of_heq (hnat f y)
  rfl

/-- The identity lax transformation. -/
protected def id (F : Aᵒᵖ ⥤ Cat.{v, u}) : LaxTrans F F where
  app _ := 𝟭 _
  naturality _ _ := 𝟙 _
  naturality_naturality {_ _} _ {_ _} _ := rfl

/-- Vertical composition of lax transformations. -/
def vcomp (α : LaxTrans F G) (β : LaxTrans G H) : LaxTrans F H where
  app a := α.app a ⋙ β.app a
  naturality f y := (β.app _).map (α.naturality f y) ≫ β.naturality f ((α.app _).obj y)
  naturality_naturality {a a'} f {x y} φ := by
    kernel_exact (congrArg (fun t => (β.app a).map t ≫ β.naturality f ((α.app a').obj y))
      (α.naturality_naturality f φ)).trans
      (congrArg ((β.app a).map (α.naturality f x) ≫ ·)
        (β.naturality_naturality f ((α.app a').map φ)))
  naturality_comp {a _ _} f g y := by
    kernel_exact congrArg (fun t => (β.app a).map (α.naturality f ((F.map g.op).toFunctor.obj y)) ≫
        t ≫ (H.map f.op).toFunctor.map (β.naturality g ((α.app _).obj y)))
      (β.naturality_naturality f (α.naturality g y))

/-- Restriction of a lax transformation along a functor `u : B ⥤ A`. -/
def whiskerLeft {B : Type u₂} [Category.{v₂} B] (u : B ⥤ A) (α : LaxTrans F G) :
    LaxTrans (reindex u F) (reindex u G) where
  app b := α.app (u.obj b)
  naturality f y := α.naturality (u.map f) y
  naturality_naturality {_ _} f {_ _} φ := α.naturality_naturality (u.map f) φ

end LaxTrans

end LaxTrans

/-! ## The displayed category of contravariant indexed categories -/

/-- The contravariant indexed categories and lax transformations, displayed over `Cat`: an object
over `A` is a functor `Aᵒᵖ ⥤ Cat`, and a morphism over `u : A ⟶ B` from `F` to `G` is a lax
transformation `LaxTrans F (reindex u G)`. Composition restricts the second transformation along the
first base functor. -/
def ICatOpLax : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := Aᵒᵖ ⥤ Cat.{u, u}
  Hom u F G := LaxTrans F (reindex u.toFunctor G)
  id F := LaxTrans.id F
  comp {_ _ _ u _ _ _ _} α β := LaxTrans.vcomp α (LaxTrans.whiskerLeft u.toFunctor β)
  -- The two sides agree componentwise by `rfl`, but the kernel does not see it on the whole
  -- structure, so we go through `ext'`, with the components compared in the kernel.
  assoc _ _ _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl)
    (fun _ _ => by kernel_rfl')

namespace ICatOpLax

/-- Reindexing `pull u G = reindex u G` of `G : Bᵒᵖ ⥤ Cat` along `u : A ⟶ B`. -/
def pull {A B : Cat.{u, u}} (u : A ⟶ B) (G : Bᵒᵖ ⥤ Cat.{u, u}) : Aᵒᵖ ⥤ Cat.{u, u} :=
  reindex u.toFunctor G

/-- The cartesian lift `pull u G ⟶[u] G`: the identity transformation. -/
def clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : Bᵒᵖ ⥤ Cat.{u, u}) : ICatOpLax.Hom u (pull u G) G :=
  LaxTrans.id (reindex u.toFunctor G)

/-- The chosen lift is cartesian: a transformation over `g ≫ u` is its own factorization. -/
def isCartesianClift {A B : Cat.{u, u}} (u : A ⟶ B) (G : Bᵒᵖ ⥤ Cat.{u, u}) :
    IsCartesian (clift u G) where
  lift _ _ χ := χ
  lift_fac _ _ _ := rfl
  lift_uniq _ hψ := hψ

end ICatOpLax

/-- **`ICatOpLax` is a split fibration over `Cat`**, cloven by reindexing
`ICatOpLax.pull u G = reindex u G`, with the identity transformations as chosen lifts. -/
instance ICatOpLax.preSplitFib : PreSplitFib ICatOpLax.{u} where
  pull u G := ICatOpLax.pull u G
  clift u G := ICatOpLax.clift u G
  isCartesianClift u G := ICatOpLax.isCartesianClift u G

instance ICatOpLax.splitFib : SplitFib ICatOpLax.{u} := {}

end Displayed.Fibration.Straightening
