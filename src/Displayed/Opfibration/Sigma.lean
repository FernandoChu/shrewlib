import Displayed.Displayed.Sigma
import Displayed.Opfibration.Basic

/-!
# Opfibrations compose

For an opfibration `D` over `A` and an opfibration `E` over `D.Total`, the composite
`D.sigmaDisp E` is an opfibration over `A` (`sigmaOpfib`): the chosen pushforward of `⟨x, b⟩`
along `f` is `⟨push f x, push (f, olift f x) b⟩`, with the pair of chosen lifts as chosen lift. A
morphism `⟨χ₁, χ₂⟩` over `f ≫ g` factors as the factorization `ψ₁` of `χ₁` and the factorization of
`χ₂`, which lies over `(f, olift f x) ≫ (g, ψ₁)`, that is over `(f ≫ g, χ₁)` up to the
factorization law of `ψ₁`: it is the only cast.

If `D` and `E` are split, so is the composite (`sigmaSplitOpfib`), with laws holding by `rfl`:
the splitting laws of the chosen lifts `(f, olift f x)` of `D.Total` are made rules
(`totalOlift_id`, `totalOlift_comp`), so that the rules for `E` apply to them.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
  {E : Displayed.{max v₁ v₂, max u₁ u₂, v₃, u₃} D.Total}

section Opfib

variable [Opfib D] [Opfib E] {a a' : A}

/-- The pair of chosen lifts `⟨olift f x, olift (f, olift f x) b⟩` is opcartesian. -/
def isOpcartesianSigmaOlift (f : a ⟶ a') (X : (D.sigmaDisp E).Ob a) :
    IsOpcartesian (D := D.sigmaDisp E)
      (y := (⟨D.push f X.1, E.push (D.totalOlift f X.1) X.2⟩ : (D.sigmaDisp E).Ob a'))
      ⟨D.olift f X.1, E.olift (D.totalOlift f X.1) X.2⟩ where
  desc g _ χ :=
    ⟨(D.isOpcartesianOlift f X.1).desc g χ.1,
      (E.isOpcartesianOlift (D.totalOlift f X.1) X.2).desc _
        (cast (congrArg (fun φ => E.Hom (D.totalMk (f ≫ g) φ) X.2 _)
          ((D.isOpcartesianOlift f X.1).desc_fac g χ.1).symm) χ.2)⟩
  desc_fac g _ χ := Sigma.ext ((D.isOpcartesianOlift f X.1).desc_fac g χ.1)
    ((heq_of_eq ((E.isOpcartesianOlift (D.totalOlift f X.1) X.2).desc_fac _ _)).trans
      (cast_heq _ _))
  desc_uniq {_ g _ χ} ψ hψ := by
    obtain ⟨ψ₁, ψ₂⟩ := ψ
    obtain ⟨χ₁, χ₂⟩ := χ
    obtain ⟨h₁, h₂⟩ := Sigma.mk.inj hψ
    obtain rfl := (D.isOpcartesianOlift f X.1).desc_uniq ψ₁ h₁
    exact congrArg (Sigma.mk _) ((E.isOpcartesianOlift (D.totalOlift f X.1) X.2).desc_uniq ψ₂
      (eq_of_heq (h₂.trans (cast_heq _ _).symm)))

/-- **Opfibrations compose.** -/
@[instance_reducible]
instance sigmaOpfib : Opfib (D.sigmaDisp E) where
  push f X := ⟨D.push f X.1, E.push (D.totalOlift f X.1) X.2⟩
  olift f X := ⟨D.olift f X.1, E.olift (D.totalOlift f X.1) X.2⟩
  isOpcartesianOlift f X := isOpcartesianSigmaOlift f X

end Opfib

/-- The composite of a split opfibration and a pre-split one is pre-split. The pushforward along
`f ≫ g` in `E` is along `olift (f ≫ g) x`, so `D` needs to be split. -/
@[instance_reducible]
instance sigmaPreSplitOpfib [SplitOpfib D] [PreSplitOpfib E] :
    PreSplitOpfib (D.sigmaDisp E) where
  toOpfib := sigmaOpfib
  push_id _ := rfl
  push_comp _ _ _ := rfl

/-- **Split opfibrations compose.** -/
instance sigmaSplitOpfib [SplitOpfib D] [SplitOpfib E] : SplitOpfib (D.sigmaDisp E) where
  olift_id _ := rfl
  olift_comp _ _ _ := rfl

end Displayed
