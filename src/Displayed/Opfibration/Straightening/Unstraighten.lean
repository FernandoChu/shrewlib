import Displayed.Opfibration.Straightening.ICat
import Displayed.Opfibration.SplitOpfibCat
import Displayed.Displayed.Equivalence

/-!
# Unstraightening functors into `Cat`

The unstraightening of `F : A ⥤ Cat` is the displayed category `∫F` over `A` whose objects over
`a` are the objects of `F a`, and whose morphisms `x ⟶[f] y` over `f : a ⟶ a'` are the morphisms
`F f x ⟶ y` of `F a'` (`unstraightenObj`). Its identities are identities and the composite of
`φ` over `f` and `ψ` over `g` is `F g φ ≫ ψ`: with the functor laws as rules, `F (𝟙 a) x` is `x`
and `F (f ≫ g) x` is `F g (F f x)`, so these are well typed, and the laws hold by `rfl`.

* `∫F` is a split opfibration (`unstraightenSplitOpfib`): the chosen pushforward of `x` along `f`
  is `F f x`, with the identity as chosen lift, and a morphism over `f ≫ g` is its own
  factorization. The laws hold by `rfl`.
* A lax transformation `α : F ⇒ u ⋙ G` over `u : A ⥤ B` gives the displayed functor over `u`
  sending `φ : F f x ⟶ y` to `α_f x ≫ α φ` (`unstraightenMap`).
* `unstraighten : VertFunctor ICat SplitOpfibCat`, whose functor laws hold by `rfl`.
* It is fully faithful (`unstraightenFullyFaithful`), with an explicit inverse on morphisms
  (`unstraightenPreimage`): a displayed functor `H` over `u` is the image of the lax
  transformation with components `H` on the vertical morphisms and 2-cells `H` on the chosen lifts.
-/

universe v₁ u₁ v₂ u₂ v u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

section UnstraightenObj

variable {A : Type u₁} [Category.{v₁} A]

/-- **The unstraightening of `F : A ⥤ Cat`**: objects over `a` are the objects of `F a`, and
morphisms `x ⟶[f] y` are the morphisms `F f x ⟶ y`. -/
def unstraightenObj (F : A ⥤ Cat.{v, u}) : Displayed.{v₁, u₁, v, u} A where
  Ob a := F.obj a
  Hom f x y := (F.map f).toFunctor.obj x ⟶ y
  id x := 𝟙 x
  -- The ascription is needed for the rules to identify the codomain with `F (f ≫ g) x ⟶ z`.
  comp {_ _ _ f g x _ z} φ ψ :=
    ((F.map g).toFunctor.map φ ≫ ψ : (F.map g).toFunctor.obj ((F.map f).toFunctor.obj x) ⟶ z)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The chosen lift `𝟙 : x ⟶[f] F f x` is opcartesian: a morphism over `f ≫ g` is its own
factorization. -/
def isOpcartesianUnstraightenOlift (F : A ⥤ Cat.{v, u}) {a a' : A} (f : a ⟶ a') (x : F.obj a) :
    IsOpcartesian (D := unstraightenObj F) (y := (F.map f).toFunctor.obj x)
      (𝟙 ((F.map f).toFunctor.obj x)) where
  desc _ _ χ := χ
  desc_fac _ _ _ := rfl
  desc_uniq _ h := h

instance unstraightenPreSplitOpfib (F : A ⥤ Cat.{v, u}) : PreSplitOpfib (unstraightenObj F) where
  push f x := (F.map f).toFunctor.obj x
  olift f x := 𝟙 ((F.map f).toFunctor.obj x)
  isOpcartesianOlift f x := isOpcartesianUnstraightenOlift F f x
  push_id _ := rfl
  push_comp _ _ _ := rfl

/-- **The unstraightening of `F` is a split opfibration**, pushing forward along `F`. -/
instance unstraightenSplitOpfib (F : A ⥤ Cat.{v, u}) : SplitOpfib (unstraightenObj F) where
  olift_id _ := rfl
  olift_comp _ _ _ := rfl

end UnstraightenObj

/-! ## The unstraightening functor -/

/-- The unstraightening of a lax transformation `α : F ⇒ u ⋙ G`: the displayed functor over `u`
sending `φ : F f x ⟶ y` to `α_f x ≫ α φ`. -/
def unstraightenMap {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {u : A ⥤ B}
    {F : A ⥤ Cat.{v, u}} {G : B ⥤ Cat.{v, u}} (α : LaxTrans F (u ⋙ G)) :
    DispFunctor u (unstraightenObj F) (unstraightenObj G) where
  obj {a} x := ((α.app a).obj x : G.obj (u.obj a))
  map {a a' f x y} φ := (α.naturality f x ≫ (α.app a').map φ :
    (G.map (u.map f)).toFunctor.obj ((α.app a).obj x) ⟶ (α.app a').obj y)
  map_id _ := rfl
  map_comp {_ _ a'' f g x _ _} φ ψ :=
    congrArg (fun t => (G.map (u.map g)).toFunctor.map (α.naturality f x) ≫ t ≫
        (α.app a'').map ψ)
      (α.naturality_naturality g φ).symm

/-- **The unstraightening**, into the split opfibrations: `F` goes to `∫F`, and a lax
transformation over `u` to the induced displayed functor. -/
def unstraighten : VertFunctor ICat.{u} SplitOpfibCat.{u} where
  obj F := { toDisplayed := unstraightenObj F, splitOpfib := unstraightenSplitOpfib F }
  map {_ _ u _ _} α := unstraightenMap (u := u.toFunctor) α
  map_id _ := rfl
  map_comp _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-! ## The inverse on morphisms -/

section Preimage

variable {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}} {G : B ⥤ Cat.{u, u}}

/-- A displayed functor `H : ∫F ⟶ ∫G` preserves the identities of the fibres. Stated in `G (u a)`,
so that the kernel accepts it as the law of the component functor of `unstraightenPreimage H`. -/
theorem unstraightenPreimage_app_map_id
    (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) (a : A) (x : F.obj a) :
    (H.map (f := 𝟙 a) (𝟙 x) : (H.obj x : G.obj (u.toFunctor.obj a)) ⟶ H.obj x) = 𝟙 (H.obj x) :=
  H.map_id x

/-- A displayed functor `H : ∫F ⟶ ∫G` preserves the composites of the fibres. -/
theorem unstraightenPreimage_app_map_comp
    (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) (a : A)
    {x y z : F.obj a} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (H.map (f := 𝟙 a) (φ ≫ ψ) : (H.obj x : G.obj (u.toFunctor.obj a)) ⟶ H.obj z) =
      (H.map (f := 𝟙 a) φ : (H.obj x : G.obj (u.toFunctor.obj a)) ⟶ H.obj y) ≫
        H.map (f := 𝟙 a) ψ :=
  H.map_comp (f := 𝟙 a) (g := 𝟙 a) φ ψ

/-- The 2-cells of `unstraightenPreimage H` are natural. -/
theorem unstraightenPreimage_naturality_naturality
    (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) {a a' : A} (f : a ⟶ a')
    {x y : F.obj a} (φ : x ⟶ y) :
    (G.map (u.toFunctor.map f)).toFunctor.map
        (H.map (f := 𝟙 a) φ : (H.obj x : G.obj (u.toFunctor.obj a)) ⟶ H.obj y) ≫
      (H.map (f := f) (𝟙 ((F.map f).toFunctor.obj y)) :
        (G.map (u.toFunctor.map f)).toFunctor.obj (H.obj y) ⟶ H.obj ((F.map f).toFunctor.obj y)) =
    (H.map (f := f) (𝟙 ((F.map f).toFunctor.obj x)) :
        (G.map (u.toFunctor.map f)).toFunctor.obj (H.obj x) ⟶ H.obj ((F.map f).toFunctor.obj x)) ≫
      (H.map (f := 𝟙 a') ((F.map f).toFunctor.map φ) :
        (H.obj ((F.map f).toFunctor.obj x) : G.obj (u.toFunctor.obj a')) ⟶
          H.obj ((F.map f).toFunctor.obj y)) :=
  (H.map_comp (f := 𝟙 a) (g := f) φ (𝟙 ((F.map f).toFunctor.obj y))).symm.trans
    (H.map_comp (f := f) (g := 𝟙 a') (𝟙 ((F.map f).toFunctor.obj x)) ((F.map f).toFunctor.map φ))

/-- The 2-cells of `unstraightenPreimage H` compose. -/
theorem unstraightenPreimage_naturality_comp
    (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) {a a' a'' : A}
    (f : a ⟶ a') (g : a' ⟶ a'') (x : F.obj a) :
    (H.map (f := f ≫ g) (𝟙 ((F.map (f ≫ g)).toFunctor.obj x)) :
        (G.map (u.toFunctor.map (f ≫ g))).toFunctor.obj (H.obj x) ⟶
          H.obj ((F.map (f ≫ g)).toFunctor.obj x)) =
      (G.map (u.toFunctor.map g)).toFunctor.map
        (H.map (f := f) (𝟙 ((F.map f).toFunctor.obj x)) :
          (G.map (u.toFunctor.map f)).toFunctor.obj (H.obj x) ⟶
            H.obj ((F.map f).toFunctor.obj x)) ≫
      (H.map (f := g) (𝟙 ((F.map g).toFunctor.obj ((F.map f).toFunctor.obj x))) :
        (G.map (u.toFunctor.map g)).toFunctor.obj (H.obj ((F.map f).toFunctor.obj x)) ⟶
          H.obj ((F.map g).toFunctor.obj ((F.map f).toFunctor.obj x))) :=
  H.map_comp (f := f) (g := g) (𝟙 ((F.map f).toFunctor.obj x))
    (𝟙 ((F.map g).toFunctor.obj ((F.map f).toFunctor.obj x)))

/-- The inverse of the unstraightening on morphisms: the lax transformation of a displayed
functor `H` over `u`, with components `H` on the vertical morphisms and 2-cells `H` on the chosen
lifts. -/
def unstraightenPreimage (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) :
    ICat.Hom u F G where
  app a :=
    { obj x := H.obj x
      map {x y} φ := (H.map (f := 𝟙 a) (x := x) (y := y) φ : H.obj x ⟶ H.obj y)
      map_id x := unstraightenPreimage_app_map_id H a x
      map_comp φ ψ := unstraightenPreimage_app_map_comp H a φ ψ }
  naturality f x := H.map (f := f) (x := x) (𝟙 ((F.map f).toFunctor.obj x))
  naturality_naturality f _ _ φ := unstraightenPreimage_naturality_naturality H f φ
  naturality_id {a} x := unstraightenPreimage_app_map_id H a x
  naturality_comp f g x := unstraightenPreimage_naturality_comp H f g x

theorem unstraightenMap_preimage
    (H : DispFunctor u.toFunctor (unstraightenObj F) (unstraightenObj G)) :
    unstraightenMap (unstraightenPreimage H) = H :=
  DispFunctor.ext (fun _ => rfl) fun {_ a'} f x _ φ =>
    heq_of_eq (H.map_comp (f := f) (g := 𝟙 a') (x := x) (𝟙 ((F.map f).toFunctor.obj x)) φ).symm

theorem unstraightenPreimage_map (α : ICat.Hom u F G) :
    unstraightenPreimage (unstraightenMap α) = α :=
  LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)

/-- **The unstraightening is fully faithful**: displayed functors `∫F ⟶ ∫G` over `u` are the same
as lax transformations `F ⇒ u ⋙ G`. -/
def unstraightenFullyFaithful : unstraighten.{u}.FullyFaithful where
  preimage H := unstraightenPreimage H
  map_preimage H := unstraightenMap_preimage H
  preimage_map α := unstraightenPreimage_map α

end Preimage

end Displayed.Opfibration.Straightening
