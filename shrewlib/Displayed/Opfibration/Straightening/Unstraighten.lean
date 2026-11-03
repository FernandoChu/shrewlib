import Displayed.Opfibration.Straightening.ICatLax
import Displayed.Opfibration.SplitOpfibLax
import Tactic.KernelTactic

/-!
# Unstraightening functors into `Cat`

The unstraightening of `F : A ⥤ Cat` is the displayed category `∫ F` (`unstraightenObj F`) over `A`
whose objects over `a` are the objects of `F a`, and whose morphisms `x ⟶[f] y` over `f : a ⟶ a'`
are the morphisms `F f x ⟶ y` of `F a'`. Its identities are identities and the composite of `φ` over
`f` and `ψ` over `g` is `F g φ ≫ ψ`: with the functor laws as rules, `F (𝟙 a) x` is `x` and
`F (f ≫ g) x` is `F g (F f x)`, so these are well typed, and the laws hold by `rfl`.

* `∫ F` is a split opfibration (`unstraightenSplitOpfib`): the chosen pushforward of `x` along
  `f` is `F f x`, with the identity as chosen lift, and a morphism over `f ≫ g` is its own
  factorization. The laws hold by `rfl`.
* A lax transformation `α : LaxTrans F (u ⋙ G)` over `u : A ⥤ B` gives the displayed functor
  over `u` sending `φ : F f x ⟶ y` to `α.naturality f x ≫ α φ` (`unstraightenMap`).
* `unstraighten : VertFunctor ICatLax SplitOpfibLax`, whose functor laws hold by `rfl`.

It is an equivalence over `Cat`, with inverse the straightening (`Equivalence.lean`), hence fully
faithful (`unstraightenFullyFaithful`).
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

/-- `∫ F` is the unstraightening `unstraightenObj F` of `F : A ⥤ Cat`. -/
scoped notation:max "∫ " F:max => unstraightenObj F

/-- The chosen lift `𝟙 : x ⟶[f] F f x` is opcartesian: a morphism over `f ≫ g` is its own
factorization. -/
def isOpcartesianUnstraightenOlift (F : A ⥤ Cat.{v, u}) {a a' : A} (f : a ⟶ a') (x : F.obj a) :
    IsOpcartesian (D := ∫ F) (y := (F.map f).toFunctor.obj x)
      (𝟙 ((F.map f).toFunctor.obj x)) where
  desc _ _ χ := χ
  desc_fac _ _ _ := rfl
  desc_uniq _ h := h

instance unstraightenPreSplitOpfib (F : A ⥤ Cat.{v, u}) : PreSplitOpfib (∫ F) where
  push f x := (F.map f).toFunctor.obj x
  olift f x := 𝟙 ((F.map f).toFunctor.obj x)
  isOpcartesianOlift f x := isOpcartesianUnstraightenOlift F f x
  push_id _ := rfl
  push_comp _ _ _ := rfl

/-- **The unstraightening of `F` is a split opfibration**, pushing forward along `F`. -/
instance unstraightenSplitOpfib (F : A ⥤ Cat.{v, u}) : SplitOpfib (∫ F) where
  olift_id _ := rfl
  olift_comp _ _ _ := rfl

/-- The unstraightening of an object of `ICatLax` is a split opfibration. The instance
`unstraightenSplitOpfib` does not apply to it, since `ICatLax.Ob A` is not reducibly `A ⥤ Cat`. -/
instance ICatLax.splitOpfib {A : Cat.{u, u}} (F : ICatLax.Ob A) :
    SplitOpfib (∫ (F : A ⥤ Cat.{u, u})) :=
  unstraightenSplitOpfib F

/-- Transport in `∫ F` along `f` is `F f`, as a rule, so that the straightening of
`∫ F` is `F` on the nose. -/
@[rewrite_rule]
theorem unstraightenPushMap (F : A ⥤ Cat.{v, u}) {a a' : A} (f : a ⟶ a')
    {x y : (∫ F).Fiber a} (β : x ⟶ y) :
    (∫ F).pushMap f β = (F.map f).toFunctor.map (β : x ⟶ y) := by
  refine (pushMap_eq_desc _ f β).trans ?_
  kernel_rfl'

end UnstraightenObj

/-! ## The unstraightening functor -/

/-- The unstraightening of a lax transformation `α : LaxTrans F (u ⋙ G)`: the displayed functor
over `u` sending `φ : F f x ⟶ y` to `α.naturality f x ≫ α φ`. -/
def unstraightenMap {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {u : A ⥤ B}
    {F : A ⥤ Cat.{v, u}} {G : B ⥤ Cat.{v, u}} (α : LaxTrans F (u ⋙ G)) :
    DispFunctor u (∫ F) (∫ G) where
  obj {a} x := ((α.app a).obj x : G.obj (u.obj a))
  map {a a' f x y} φ := (α.naturality f x ≫ (α.app a').map φ :
    (G.map (u.map f)).toFunctor.obj ((α.app a).obj x) ⟶ (α.app a').obj y)
  map_id _ := rfl
  map_comp {_ _ a'' f g x _ _} φ ψ :=
    congrArg (fun t => (G.map (u.map g)).toFunctor.map (α.naturality f x) ≫ t ≫
        (α.app a'').map ψ)
      (α.naturality_naturality g φ).symm

/-- **The unstraightening**, into the split opfibrations: `F` goes to `∫ F`, and a lax
transformation over `u` to the induced displayed functor. -/
def unstraighten : VertFunctor ICatLax.{u} SplitOpfibLax.{u} where
  obj F := { toDisplayed := ∫ F, splitOpfib := unstraightenSplitOpfib F }
  map {_ _ u _ _} α := unstraightenMap (u := u.toFunctor) α
  map_id _ := rfl
  map_comp _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Displayed.Opfibration.Straightening
