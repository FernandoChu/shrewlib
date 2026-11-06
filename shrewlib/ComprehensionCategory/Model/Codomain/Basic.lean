import ComprehensionCategory.Map

/-!
# The codomain comprehension category

A category `C` with chosen pullbacks is a full comprehension category over itself: the
codomain fibration `cod C` (`Displayed/Displayed/Codomain`), with the identity as comprehension
functor. A type in context `Γ` is a morphism `p : X ⟶ Γ`, `Γ ▹ p` is `X`, and substitution is
pullback.

The comprehension functor of any comprehension category `D` over `C` is a strict map to it, over
the identity (`comprMap`).
-/

universe v u v₂ u₂

open CategoryTheory Limits Displayed

namespace ComprehensionCategory.CodomainModel

variable {C : Type u} [Category.{v} C]

/-- A category with chosen pullbacks is a comprehension category over itself, with the codomain
fibration and the identity comprehension functor. -/
@[instance_reducible]
instance comprehension [ChosenPullbacks C] : Comprehension (cod C) where
  compr := VertFunctor.id (cod C)
  isCartesianComprMap H := H

/-- The codomain comprehension category is full. -/
@[instance_reducible]
instance fullComprehension [ChosenPullbacks C] : FullComprehension (cod C) where
  comprFullyFaithful :=
    { preimage := fun ψ => ψ }

/-- **The comprehension functor is a strict map** from `D` to the codomain comprehension category,
over the identity: the comprehension functor of `cod C` is the identity. -/
def comprMap [ChosenPullbacks C] (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] :
    StrictComprehensionMap (𝟭 C) D (cod C) where
  toPre.obj A := D.compr.obj A
  toPre.map φ := D.compr.map φ
  toPre.isCartesianMap H := D.isCartesianComprMap H
  toPre.compr_obj _ := rfl

end ComprehensionCategory.CodomainModel
