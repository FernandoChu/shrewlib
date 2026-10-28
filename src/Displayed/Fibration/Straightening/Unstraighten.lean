import Displayed.Fibration.Straightening.ICat
import Displayed.Fibration.SplitFibCat
import Displayed.Displayed.Equivalence
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
* `unstraighten : VertFunctor ICat SplitFibCat`, whose functor laws hold by `rfl`.
* It is fully faithful (`unstraightenFullyFaithful`), with an explicit inverse on morphisms
  (`unstraightenPreimage`): a displayed functor `H` over `u` is the image of the lax
  transformation with components `H` on the vertical morphisms and 2-cells `H` on the chosen lifts.

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
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

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
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **The unstraightening of `F` is a split fibration**, pulling back along `F`. -/
instance unstraightenSplitFib (F : Aᵒᵖ ⥤ Cat.{v, u}) : SplitFib (∫⁻ F) where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

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
  map_id _ := rfl
  map_comp {a _ _ f g x _ _} φ ψ := by
    kernel_exact congrArg (fun t => (α.app a).map φ ≫ t ≫
        (G.map (u.map f).op).toFunctor.map (α.naturality g _))
      (α.naturality_naturality f ψ)

/-- **The unstraightening**, into the split fibrations: `F` goes to `∫⁻ F`, and a lax
transformation over `u` to the induced displayed functor. -/
def unstraighten : VertFunctor ICat.{u} SplitFibCat.{u} where
  obj F := { toDisplayed := ∫⁻ F, splitFib := unstraightenSplitFib F }
  map {_ _ u _ _} α := unstraightenMap (u := u.toFunctor) α
  map_id _ := rfl
  map_comp _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-! ## The inverse on morphisms -/

section Preimage

variable {A B : Cat.{u, u}} {u : A ⟶ B} {F : Aᵒᵖ ⥤ Cat.{u, u}} {G : Bᵒᵖ ⥤ Cat.{u, u}}

/-- A displayed functor `H` from `∫⁻ F` to `∫⁻ G` preserves the identities of the fibres. Stated in
`G (op (u a))`, so that the kernel accepts it as the law of the component functor of
`unstraightenPreimage H`. -/
theorem unstraightenPreimage_app_map_id
    (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) (a : A) (x : F.obj (op a)) :
    (H.map (f := 𝟙 a) (𝟙 x) : (H.obj x : G.obj (op (u.toFunctor.obj a))) ⟶ H.obj x) =
      𝟙 (H.obj x) :=
  H.map_id x

/-- A displayed functor `H` from `∫⁻ F` to `∫⁻ G` preserves the composites of the fibres. -/
theorem unstraightenPreimage_app_map_comp
    (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) (a : A)
    {x y z : F.obj (op a)} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (H.map (f := 𝟙 a) (φ ≫ ψ) : (H.obj x : G.obj (op (u.toFunctor.obj a))) ⟶ H.obj z) =
      (H.map (f := 𝟙 a) φ : (H.obj x : G.obj (op (u.toFunctor.obj a))) ⟶ H.obj y) ≫
        H.map (f := 𝟙 a) ψ :=
  H.map_comp (f := 𝟙 a) (g := 𝟙 a) φ ψ

/-- The 2-cells of `unstraightenPreimage H` are natural. -/
theorem unstraightenPreimage_naturality_naturality
    (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) {a a' : A} (f : a ⟶ a')
    {x y : F.obj (op a')} (φ : x ⟶ y) :
    (H.map (f := 𝟙 a) ((F.map f.op).toFunctor.map φ) :
        (H.obj ((F.map f.op).toFunctor.obj x) : G.obj (op (u.toFunctor.obj a))) ⟶
          H.obj ((F.map f.op).toFunctor.obj y)) ≫
      (H.map (f := f) (𝟙 ((F.map f.op).toFunctor.obj y)) :
        H.obj ((F.map f.op).toFunctor.obj y) ⟶
          (G.map (u.toFunctor.map f).op).toFunctor.obj (H.obj y)) =
    (H.map (f := f) (𝟙 ((F.map f.op).toFunctor.obj x)) :
        H.obj ((F.map f.op).toFunctor.obj x) ⟶
          (G.map (u.toFunctor.map f).op).toFunctor.obj (H.obj x)) ≫
      (G.map (u.toFunctor.map f).op).toFunctor.map
        (H.map (f := 𝟙 a') φ : (H.obj x : G.obj (op (u.toFunctor.obj a'))) ⟶ H.obj y) :=
  (H.map_comp (f := 𝟙 a) (g := f) ((F.map f.op).toFunctor.map φ)
      (𝟙 ((F.map f.op).toFunctor.obj y))).symm.trans
    (H.map_comp (f := f) (g := 𝟙 a') (𝟙 ((F.map f.op).toFunctor.obj x)) φ)

/-- The 2-cells of `unstraightenPreimage H` compose. -/
theorem unstraightenPreimage_naturality_comp
    (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) {a a' a'' : A}
    (f : a ⟶ a') (g : a' ⟶ a'') (y : F.obj (op a'')) :
    (H.map (f := f ≫ g) (𝟙 ((F.map (f ≫ g).op).toFunctor.obj y)) :
        H.obj ((F.map (f ≫ g).op).toFunctor.obj y) ⟶
          (G.map (u.toFunctor.map (f ≫ g)).op).toFunctor.obj (H.obj y)) =
      (H.map (f := f) (𝟙 ((F.map f.op).toFunctor.obj ((F.map g.op).toFunctor.obj y))) :
        H.obj ((F.map f.op).toFunctor.obj ((F.map g.op).toFunctor.obj y)) ⟶
          (G.map (u.toFunctor.map f).op).toFunctor.obj
            (H.obj ((F.map g.op).toFunctor.obj y))) ≫
      (G.map (u.toFunctor.map f).op).toFunctor.map
        (H.map (f := g) (𝟙 ((F.map g.op).toFunctor.obj y)) :
          H.obj ((F.map g.op).toFunctor.obj y) ⟶
            (G.map (u.toFunctor.map g).op).toFunctor.obj (H.obj y)) :=
  H.map_comp (f := f) (g := g) (𝟙 ((F.map f.op).toFunctor.obj ((F.map g.op).toFunctor.obj y)))
    (𝟙 ((F.map g.op).toFunctor.obj y))

/-- The inverse of the unstraightening on morphisms: the lax transformation of a displayed
functor `H` over `u`, with components `H` on the vertical morphisms and 2-cells `H` on the chosen
lifts. -/
def unstraightenPreimage (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) :
    ICat.Hom u F G where
  app a :=
    { obj x := H.obj x
      map {x y} φ := (H.map (f := 𝟙 a) (x := x) (y := y) φ : H.obj x ⟶ H.obj y)
      map_id x := unstraightenPreimage_app_map_id H a x
      map_comp φ ψ := unstraightenPreimage_app_map_comp H a φ ψ }
  naturality f y := H.map (f := f) (y := y) (𝟙 ((F.map f.op).toFunctor.obj y))
  naturality_naturality f _ _ φ := unstraightenPreimage_naturality_naturality H f φ
  naturality_id {a} y := unstraightenPreimage_app_map_id H a y
  naturality_comp f g y := unstraightenPreimage_naturality_comp H f g y

theorem unstraightenMap_preimage
    (H : DispFunctor u.toFunctor (∫⁻ F) (∫⁻ G)) :
    unstraightenMap (unstraightenPreimage H) = H :=
  DispFunctor.ext (fun _ => rfl) fun {a _} f _ y φ =>
    heq_of_eq (H.map_comp (f := 𝟙 a) (g := f) (z := y) φ (𝟙 ((F.map f.op).toFunctor.obj y))).symm

theorem unstraightenPreimage_map (α : ICat.Hom u F G) :
    unstraightenPreimage (unstraightenMap α) = α :=
  LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-- **The unstraightening is fully faithful**: displayed functors from `∫⁻ F` to `∫⁻ G` over `u`
are the same as lax transformations `LaxTrans F (reindex u G)`. -/
def unstraightenFullyFaithful : unstraighten.{u}.FullyFaithful where
  preimage H := unstraightenPreimage H
  map_preimage H := unstraightenMap_preimage H
  preimage_map α := unstraightenPreimage_map α

end Preimage

end Displayed.Fibration.Straightening
