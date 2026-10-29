import Displayed.Displayed.Codomain
import Displayed.Fibration.Basic
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# The codomain fibration

The cartesian morphisms of the codomain displayed category `cod C` are the pullback squares: the
square of a cartesian morphism is a limit (`isLimitOfIsCartesian`), and a morphism whose square is
a limit is cartesian (`isCartesianOfIsLimit`). Both are data, and the second takes the limit data
rather than Mathlib's `IsPullback`, a `Prop`, from which the lifts could only be chosen. So if `C`
has chosen pullbacks (Mathlib's `ChosenPullbacks C`, whose limit cones are computable), `cod C` is
a fibration (`cod.fib`).
-/

universe v u

open CategoryTheory Limits

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

namespace cod

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

end Displayed
