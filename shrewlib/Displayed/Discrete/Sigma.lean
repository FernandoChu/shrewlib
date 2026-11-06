import Displayed.Discrete.Basic
import Displayed.Opfibration.Sigma

/-!
# Discrete opfibrations compose

For `D` displayed over `A` and `E` displayed over `D.Total`, both with discrete fibres, the
composite `D.sigmaDisp E` has discrete fibres (`isDiscrete_sigmaDisp`): a vertical morphism
`⟨φ, ψ⟩ : ⟨x, b⟩ ⟶ ⟨x', b'⟩` has `φ : x ⟶[𝟙 a] x'` vertical, so `x = x'` and `φ` is the identity,
and then `ψ` lies over the identity of `⟨a, x⟩`, so `b = b'`. With the composite of split
opfibrations (`sigmaSplitOpfib`), discrete opfibrations compose (`DiscOpfibOb.sigma`).
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- **The fibres of the composite of displayed categories with discrete fibres are discrete.** -/
theorem isDiscrete_sigmaDisp {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₂, u₂} A}
    {E : Displayed.{v₃, u₃} D.Total} [∀ a, IsDiscrete (D.Fiber a)]
    [∀ p, IsDiscrete (E.Fiber p)] (a : A) : IsDiscrete ((D.sigmaDisp E).Fiber a) where
  subsingleton := by
    rintro ⟨x, b⟩ ⟨x', b'⟩
    refine ⟨fun ⟨φ, ψ⟩ ⟨φ', ψ'⟩ => ?_⟩
    obtain rfl : x = x' := IsDiscrete.eq_of_hom (C := D.Fiber a) φ
    obtain rfl : φ = 𝟙ᵈ x := Subsingleton.elim (α := @Quiver.Hom (D.Fiber a) _ x x) _ _
    obtain rfl : φ' = 𝟙ᵈ x := Subsingleton.elim (α := @Quiver.Hom (D.Fiber a) _ x x) _ _
    exact congrArg (Sigma.mk _)
      (Subsingleton.elim (α := @Quiver.Hom (E.Fiber (D.tot x)) _ b b') _ _)
  eq_of_hom := by
    rintro ⟨x, b⟩ ⟨x', b'⟩ ⟨φ, ψ⟩
    obtain rfl : x = x' := IsDiscrete.eq_of_hom (C := D.Fiber a) φ
    obtain rfl : φ = 𝟙ᵈ x := Subsingleton.elim (α := @Quiver.Hom (D.Fiber a) _ x x) _ _
    obtain rfl : b = b' := IsDiscrete.eq_of_hom (C := E.Fiber (D.tot x)) ψ
    rfl

/-- **Discrete opfibrations compose**: the composite of a discrete opfibration `X` over `A` and a
discrete opfibration over its total category. -/
def DiscOpfibOb.sigma {A : Cat.{v₁, u₁}} (X : DiscOpfibOb.{v₂, u₂} A)
    (Y : DiscOpfibOb.{v₂, u₂} (Cat.of X.toDisplayed.Total)) : DiscOpfibOb.{v₂, u₂} A where
  toDisplayed := X.toDisplayed.sigmaDisp Y.toDisplayed
  splitOpfib := @sigmaSplitOpfib _ _ _ _ X.splitOpfib Y.splitOpfib
  isDiscrete := @isDiscrete_sigmaDisp _ _ _ _ X.isDiscrete Y.isDiscrete

end Displayed
