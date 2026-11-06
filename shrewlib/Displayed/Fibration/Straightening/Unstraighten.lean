import Displayed.Fibration.Straightening.ICatOpLax
import Displayed.Fibration.SplitFibLax
import Tactic.KernelTactic

/-!
# Unstraightening contravariant functors into `Cat`

The unstraightening of `F : Aᵒᵖ ⥤ Cat` is the displayed category `∫⁻ F` (`unstraightenObj F`) over
`A` whose objects over `a` are the objects of `F (op a)`, and whose morphisms `x ⟶[f] y` over
`f : a ⟶ a'` are the morphisms `x ⟶ F f y` of `F (op a)`, where `F f` stands for `F.map f.op`. Its
identities are identities and the composite of `φ` over `f` and `ψ` over `g` is `φ ≫ F f ψ`: with
the functor laws as rules, including those on opposites, `F (𝟙 a) y` is `y` and `F (f ≫ g) z` is
`F f (F g z)`, so these are well typed, and the laws hold by `rfl`.

* `∫⁻ F` is a split fibration (`unstraightenSplitFib`): the chosen pullback of `y` along `f` is
  `F f y`, with the identity as chosen lift, and a morphism over `g ≫ f` is its own factorization.
  The laws hold by `rfl`.
* A lax transformation `α : LaxTrans F (reindex u G)` over `u : A ⥤ B` gives the displayed functor
  over `u` sending `φ : x ⟶ F f y` to `α φ ≫ α.naturality f y` (`unstraightenMap`).
* `unstraighten : VertFunctor ICatOpLax SplitFibLax`, whose functor laws hold by `rfl`.

It is an equivalence over `Cat`, with inverse the straightening (`Equivalence.lean`), hence fully
faithful (`unstraightenFullyFaithful`).

This is the dual of `Opfibration/Straightening/Unstraighten.lean`.
-/

universe v₁ u₁ v₂ u₂ v u

namespace Displayed.Fibration.Straightening

open CategoryTheory Opposite Displayed

open scoped Displayed

section UnstraightenObj

variable {A : Type u₁} [Category.{v₁} A]

/-- **The unstraightening of `F : Aᵒᵖ ⥤ Cat`**: objects over `a` are the objects of `F (op a)`,
and morphisms `x ⟶[f] y` are the morphisms `x ⟶ F f y`. -/
def unstraightenObj (F : Aᵒᵖ ⥤ Cat.{v, u}) : Displayed.{v₁, u₁, v, u} A where
  Ob a := F.obj (op a)
  Hom f x y := x ⟶ (F.map f.op).toFunctor.obj y
  id x := 𝟙 x
  -- The ascription is needed for the rules to identify the codomain with `F (f ≫ g) z`.
  comp {_ _ _ f g x _ z} φ ψ :=
    (φ ≫ (F.map f.op).toFunctor.map ψ :
      x ⟶ (F.map f.op).toFunctor.obj ((F.map g.op).toFunctor.obj z))

/-- `∫⁻ F` is the unstraightening `unstraightenObj F` of `F : Aᵒᵖ ⥤ Cat`. -/
scoped notation:max "∫⁻ " F:max => unstraightenObj F

/-- The chosen lift `𝟙 : F f y ⟶[f] y` is cartesian: a morphism over `g ≫ f` is its own
factorization. -/
def isCartesianUnstraightenClift (F : Aᵒᵖ ⥤ Cat.{v, u}) {a a' : A} (f : a ⟶ a')
    (y : F.obj (op a')) :
    IsCartesian (D := ∫⁻ F) (x := (F.map f.op).toFunctor.obj y)
      (𝟙 ((F.map f.op).toFunctor.obj y)) where
  lift _ _ χ := χ
  lift_fac _ _ _ := rfl
  lift_uniq _ h := h

instance unstraightenPreSplitFib (F : Aᵒᵖ ⥤ Cat.{v, u}) : PreSplitFib (∫⁻ F) where
  pull f y := (F.map f.op).toFunctor.obj y
  clift f y := 𝟙 ((F.map f.op).toFunctor.obj y)
  isCartesianClift f y := isCartesianUnstraightenClift F f y

/-- **The unstraightening of `F` is a split fibration**, pulling back along `F`. -/
instance unstraightenSplitFib (F : Aᵒᵖ ⥤ Cat.{v, u}) : SplitFib (∫⁻ F) := {}

/-- Transport in `∫⁻ F` along `f` is `F f`, as a rule, so that the straightening of `∫⁻ F` is `F`
on the nose. -/
@[rewrite_rule]
theorem unstraightenPullMap (F : Aᵒᵖ ⥤ Cat.{v, u}) {a a' : A} (f : a ⟶ a')
    {x y : (∫⁻ F).Fiber a'} (β : x ⟶ y) :
    (∫⁻ F).pullMap f β = (F.map f.op).toFunctor.map (β : x ⟶ y) := by
  refine (pullMap_eq_lift _ f β).trans ?_
  kernel_rfl'

end UnstraightenObj

/-! ## The unstraightening functor -/

/-- The unstraightening of a lax transformation `α : LaxTrans F (reindex u G)`: the displayed
functor over `u` sending `φ : x ⟶ F f y` to `α φ ≫ α.naturality f y`. -/
def unstraightenMap {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {u : A ⥤ B}
    {F : Aᵒᵖ ⥤ Cat.{v, u}} {G : Bᵒᵖ ⥤ Cat.{v, u}} (α : LaxTrans F (reindex u G)) :
    DispFunctor u (∫⁻ F) (∫⁻ G) where
  obj {a} x := ((α.app a).obj x : G.obj (op (u.obj a)))
  map {a a' f x y} φ := ((α.app a).map φ ≫ α.naturality f y :
    (α.app a).obj x ⟶ (G.map (u.map f).op).toFunctor.obj ((α.app a').obj y))
  map_comp {a _ _ f g x _ _} φ ψ := by
    kernel_exact congrArg (fun t => (α.app a).map φ ≫ t ≫
        (G.map (u.map f).op).toFunctor.map (α.naturality g _))
      (α.naturality_naturality f ψ)

/-- **The unstraightening**, into the split fibrations: `F` goes to `∫⁻ F`, and a lax
transformation over `u` to the induced displayed functor. -/
def unstraighten : VertFunctor ICatOpLax.{u} SplitFibLax.{u} where
  obj F := { toDisplayed := ∫⁻ F, splitFib := unstraightenSplitFib F }
  map {_ _ u _ _} α := unstraightenMap (u := u.toFunctor) α
  map_comp _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Displayed.Fibration.Straightening
