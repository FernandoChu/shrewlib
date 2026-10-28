import Displayed.Displayed.Functor
import Displayed.Fibration.Basic
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# The codomain displayed category

The arrow category of `C`, displayed over `C` by the codomain: an object over `a` is a morphism
`p : X ⟶ a`, and a morphism over `f : a ⟶ a'` from `p : X ⟶ a` to `q : Y ⟶ a'` is a morphism
`h : X ⟶ Y` with `h ≫ q = p ≫ f`. The laws hold by `rfl`, since the category laws of `C` are rules
and the equation is a proposition. For `C = Cat` it is the arrow
category of `Cat` used in `Displayed/Displayed/Straightening`.

We show that the cartesian morphisms are the pullback squares: the square of a cartesian morphism
is a limit (`isLimitOfIsCartesian`), and a morphism whose square is a limit is cartesian
(`isCartesianOfIsLimit`). Both are data, and the second takes the limit data rather than Mathlib's
`IsPullback`, a `Prop`, from which the lifts could only be chosen. So if `C` has chosen pullbacks
(Mathlib's `ChosenPullbacks C`, whose limit cones are computable), `cod C` is a fibration
(`cod.fib`).

A functor `F : C ⥤ C'` acts on the codomain displayed categories (`codMap F`), by `F.map`.
-/

universe v u v₂ u₂

open CategoryTheory Limits

namespace Displayed

open scoped Displayed

variable (C : Type u) [Category.{v} C]

/-- An object of the codomain displayed category over `a`: a morphism into `a`. -/
@[ext]
structure CodOb (a : C) where
  /-- The domain. -/
  dom : C
  /-- The morphism into `a`. -/
  hom : dom ⟶ a

variable {C}

/-- A morphism of the codomain displayed category over `f : a ⟶ a'`: a commutative square. -/
def CodHom {a a' : C} (f : a ⟶ a') (x : CodOb C a) (y : CodOb C a') : Type v :=
  { h : x.dom ⟶ y.dom // h ≫ y.hom = x.hom ≫ f }

theorem CodHom.ext {a a' : C} {f : a ⟶ a'} {x : CodOb C a} {y : CodOb C a'} {φ ψ : CodHom f x y}
    (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

variable (C)

/-- The codomain displayed category: the arrow category of `C`, displayed over `C` by the
codomain. -/
def cod : Displayed.{v, u, v, max u v} C where
  Ob := CodOb C
  Hom := CodHom
  id x := ⟨𝟙 x.dom, rfl⟩
  comp {_ _ _ f g x y z} φ ψ := ⟨φ.1 ≫ ψ.1, by
    obtain ⟨φ, hφ⟩ := φ
    obtain ⟨ψ, hψ⟩ := ψ
    change φ ≫ ψ ≫ z.hom = x.hom ≫ f ≫ g
    rw [hψ, ← Category.assoc, hφ, Category.assoc]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {C}

namespace cod

@[simp] theorem id_val {a : C} (x : (cod C).Ob a) : (𝟙ᵈ x : x ⟶[𝟙 a] x).1 = 𝟙 x.dom := rfl

@[simp] theorem comp_val {a a' a'' : C} {f : a ⟶ a'} {g : a' ⟶ a''} {x : (cod C).Ob a}
    {y : (cod C).Ob a'} {z : (cod C).Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    (φ ≫ᵈ ψ).1 = φ.1 ≫ ψ.1 := rfl

/-- The commutative square of a morphism of `cod C`. -/
theorem w {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} (φ : x ⟶[f] y) :
    φ.1 ≫ y.hom = x.hom ≫ f :=
  φ.2

/-- The pullback cone of a morphism `φ` of `cod C`: its square. -/
abbrev cone {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} (φ : x ⟶[f] y) :
    PullbackCone y.hom f :=
  PullbackCone.mk φ.1 x.hom φ.2

/-- **The square of a cartesian morphism of `cod C` is a pullback**: a cone `(k, l)` is a morphism
over `l` from the identity of its apex, whose factorization through `φ` is the lift. -/
def isLimitOfIsCartesian {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'}
    {φ : x ⟶[f] y} (H : IsCartesian φ) : IsLimit (cone φ) :=
  let χ (s : PullbackCone y.hom f) : (⟨s.pt, 𝟙 s.pt⟩ : (cod C).Ob s.pt) ⟶[s.snd ≫ f] y :=
    ⟨s.fst, s.condition⟩
  PullbackCone.IsLimit.mk φ.2 (fun s => (H.lift s.snd (χ s)).1)
    (fun s => congrArg Subtype.val (H.lift_fac s.snd (χ s)))
    (fun s => (H.lift s.snd (χ s)).2)
    (fun s m hm₁ hm₂ => congrArg Subtype.val (H.lift_uniq (χ := χ s) ⟨m, hm₂⟩ (CodHom.ext hm₁)))

/-- The square of a cartesian morphism of `cod C` is a pullback. -/
theorem isPullback_of_isCartesian {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a}
    {y : (cod C).Ob a'} {φ : x ⟶[f] y} (H : IsCartesian φ) : IsPullback φ.1 x.hom y.hom f :=
  ⟨⟨φ.2⟩, ⟨isLimitOfIsCartesian H⟩⟩

/-- **A morphism of `cod C` whose square is a pullback is cartesian**: the factorization of `χ`
is the lift of `(χ, z ⟶ a₀ ⟶ a)`. -/
def isCartesianOfIsLimit {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'}
    {φ : x ⟶[f] y} (P : IsLimit (cone φ)) : IsCartesian φ where
  lift g z χ := ⟨PullbackCone.IsLimit.lift P χ.1 (z.hom ≫ g) χ.2,
    PullbackCone.IsLimit.lift_snd P _ _ _⟩
  lift_fac _ _ _ := CodHom.ext (PullbackCone.IsLimit.lift_fst P _ _ _)
  lift_uniq {_ _ z χ} ψ hψ := CodHom.ext (PullbackCone.IsLimit.hom_ext P
    ((congrArg Subtype.val hψ).trans (PullbackCone.IsLimit.lift_fst P _ _ _).symm)
    (ψ.2.trans (PullbackCone.IsLimit.lift_snd P χ.1 (z.hom ≫ _) χ.2).symm))

/-- If `C` has chosen pullbacks, the codomain displayed category is a fibration, with the chosen
pullback of `q : Y ⟶ a'` along `f : a ⟶ a'` the projection `pullbackObj q f ⟶ a`. -/
@[instance_reducible]
instance fib [ChosenPullbacks C] : Fib (cod C) where
  pull f y := ⟨ChosenPullbacksAlong.pullbackObj y.hom f, ChosenPullbacksAlong.snd y.hom f⟩
  clift f y := ⟨ChosenPullbacksAlong.fst y.hom f, ChosenPullbacksAlong.condition⟩
  isCartesianClift f y := isCartesianOfIsLimit (ChosenPullbacksAlong.isLimitPullbackCone y.hom f)

end cod

/-! ## Functoriality -/

variable {C' : Type u₂} [Category.{v₂} C']

/-- The action of a functor `F : C ⥤ C'` on the codomain displayed categories, sending `p : X ⟶ a`
to `F.map p`, and a square to its image. -/
def codMap (F : C ⥤ C') : DispFunctor F (cod C) (cod C') where
  obj x := ⟨F.obj x.dom, F.map x.hom⟩
  map φ := ⟨F.map φ.1, (congrArg F.map (cod.w φ) :)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed
