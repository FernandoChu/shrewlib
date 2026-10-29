import Displayed.Displayed.Sigma
import Displayed.Fibration.Basic

/-!
# Fibrations compose

For a fibration `D` over `A` and a fibration `E` over `D.Total`, the composite `D.sigmaDisp E` is a
fibration over `A` (`sigmaFib`): the chosen pullback of `⟨y, c⟩` along `f` is
`⟨pull f y, pull (f, clift f y) c⟩`, with the pair of chosen lifts as chosen lift. A morphism
`⟨χ₁, χ₂⟩` over `g ≫ f` factors as the factorization `ψ₁` of `χ₁` and the factorization of `χ₂`,
which lies over `(g, ψ₁) ≫ (f, clift f y)`, that is over `(g ≫ f, χ₁)` up to the factorization law
of `ψ₁`: it is the only cast.

If `D` and `E` are split, so is the composite (`sigmaSplitFib`), with laws holding by `rfl`: the
splitting laws of the chosen lifts `(f, clift f y)` of `D.Total` are made rules
(`totalClift_id`, `totalClift_comp`), so that the rules for `E` apply to them.

This is the dual of `Opfibration/Sigma.lean`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
  {E : Displayed.{max v₁ v₂, max u₁ u₂, v₃, u₃} D.Total}

section Fib

variable [Fib D] [Fib E] {a a' : A}

/-- The pair of chosen lifts `⟨clift f y, clift (f, clift f y) c⟩` is cartesian. -/
def isCartesianSigmaClift (f : a ⟶ a') (Y : (D.sigmaDisp E).Ob a') :
    IsCartesian (D := D.sigmaDisp E)
      (x := (⟨D.pull f Y.1, E.pull (D.totalClift f Y.1) Y.2⟩ : (D.sigmaDisp E).Ob a))
      ⟨D.clift f Y.1, E.clift (D.totalClift f Y.1) Y.2⟩ where
  lift g Z χ :=
    ⟨(D.isCartesianClift f Y.1).lift g χ.1,
      (E.isCartesianClift (D.totalClift f Y.1) Y.2).lift _
        (cast (congrArg (fun φ => E.Hom (D.totalMk (g ≫ f) φ) Z.2 Y.2)
          ((D.isCartesianClift f Y.1).lift_fac g χ.1).symm) χ.2)⟩
  lift_fac g _ χ := Sigma.ext ((D.isCartesianClift f Y.1).lift_fac g χ.1)
    ((heq_of_eq ((E.isCartesianClift (D.totalClift f Y.1) Y.2).lift_fac _ _)).trans
      (cast_heq _ _))
  lift_uniq {_ g _ χ} ψ hψ := by
    obtain ⟨ψ₁, ψ₂⟩ := ψ
    obtain ⟨χ₁, χ₂⟩ := χ
    obtain ⟨h₁, h₂⟩ := Sigma.mk.inj hψ
    obtain rfl := (D.isCartesianClift f Y.1).lift_uniq ψ₁ h₁
    exact congrArg (Sigma.mk _) ((E.isCartesianClift (D.totalClift f Y.1) Y.2).lift_uniq ψ₂
      (eq_of_heq (h₂.trans (cast_heq _ _).symm)))

/-- **Fibrations compose.** -/
@[instance_reducible]
instance sigmaFib : Fib (D.sigmaDisp E) where
  pull f Y := ⟨D.pull f Y.1, E.pull (D.totalClift f Y.1) Y.2⟩
  clift f Y := ⟨D.clift f Y.1, E.clift (D.totalClift f Y.1) Y.2⟩
  isCartesianClift f Y := isCartesianSigmaClift f Y

end Fib

/-- The composite of a split fibration and a pre-split one is pre-split. The pullback along
`f ≫ g` in `E` is along `clift (f ≫ g) y`, so `D` needs to be split. -/
@[instance_reducible]
instance sigmaPreSplitFib [SplitFib D] [PreSplitFib E] : PreSplitFib (D.sigmaDisp E) where
  toFib := sigmaFib
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **Split fibrations compose.** -/
instance sigmaSplitFib [SplitFib D] [SplitFib E] : SplitFib (D.sigmaDisp E) where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

end Displayed
