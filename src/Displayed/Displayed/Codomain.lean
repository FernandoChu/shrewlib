import Displayed.Fibration.Basic
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# The codomain displayed category

The arrow category of `C`, displayed over `C` by the codomain: an object over `a` is a morphism
`p : X ⟶ a`, and a morphism over `f : a ⟶ a'` from `p : X ⟶ a` to `q : Y ⟶ a'` is a morphism
`h : X ⟶ Y` with `h ≫ q = p ≫ f`. The laws hold by `rfl`, since the category laws of `C` are rules
and the equation is a proposition. For `C = Cat` it is the arrow
category `Cat^→` of `Displayed/Displayed/Straightening`.

We show that the cartesian morphisms are the pullback squares (`isCartesian_iff_isPullback`), so
that if `C` has chosen pullbacks (Mathlib's `ChosenPullbacks C`, which are data rather than a
`Prop`, so no choice is involved), `cod C` is a fibration (`cod.fib`).
-/

universe v u

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

/-- **The cartesian morphisms of `cod C` are the pullback squares.** -/
theorem isCartesian_iff_isPullback {a a' : C} {f : a ⟶ a'} {x : (cod C).Ob a}
    {y : (cod C).Ob a'} (φ : x ⟶[f] y) : IsCartesian φ ↔ IsPullback φ.1 x.hom y.hom f := by
  constructor
  · intro H
    -- A cone `(k, l)` is a morphism over `l` from the identity of its apex.
    let χ (s : PullbackCone y.hom f) : (⟨s.pt, 𝟙 s.pt⟩ : (cod C).Ob s.pt) ⟶[s.snd ≫ f] y :=
      ⟨s.fst, s.condition⟩
    refine ⟨⟨φ.2⟩, ⟨PullbackCone.IsLimit.mk φ.2 (fun s => (H.lift s.snd (χ s)).1)
      (fun s => congrArg Subtype.val (H.lift_fac s.snd (χ s)))
      (fun s => (H.lift s.snd (χ s)).2) (fun s m hm₁ hm₂ => ?_)⟩⟩
    exact congrArg Subtype.val (H.lift_uniq (χ := χ s) ⟨m, hm₂⟩ (CodHom.ext hm₁))
  · intro P a₀ g z χ
    have w : χ.1 ≫ y.hom = (z.hom ≫ g) ≫ f := χ.2
    refine ⟨⟨P.lift χ.1 (z.hom ≫ g) w, P.lift_snd _ _ w⟩, CodHom.ext (P.lift_fst _ _ w),
      fun ψ hψ => CodHom.ext ?_⟩
    exact P.hom_ext ((congrArg Subtype.val hψ).trans (P.lift_fst _ _ w).symm)
      (ψ.2.trans (P.lift_snd _ _ w).symm)

/-- If `C` has chosen pullbacks, the codomain displayed category is a fibration, with the chosen
pullback of `q : Y ⟶ a'` along `f : a ⟶ a'` the projection `pullbackObj q f ⟶ a`. -/
@[instance_reducible]
instance fib [ChosenPullbacks C] : Fib (cod C) where
  pull f y := ⟨ChosenPullbacksAlong.pullbackObj y.hom f, ChosenPullbacksAlong.snd y.hom f⟩
  clift f y := ⟨ChosenPullbacksAlong.fst y.hom f, ChosenPullbacksAlong.condition⟩
  clift_cartesian f y :=
    (isCartesian_iff_isPullback _).2 (ChosenPullbacksAlong.isPullback y.hom f)

end cod

end Displayed
