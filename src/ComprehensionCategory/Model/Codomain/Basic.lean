import ComprehensionCategory.Basic

/-!
# The codomain comprehension category

A category `C` with chosen pullbacks is a full comprehension category over itself: the
codomain fibration `cod C` (`Displayed/Displayed/Codomain`), with the identity as comprehension
functor. A type in context `Γ` is a morphism `p : X ⟶ Γ`, `Γ ▹ p` is `X`, and substitution is
pullback.
-/

universe v u

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
    { preimage := fun ψ => ψ
      map_preimage := fun _ => rfl
      preimage_map := fun _ => rfl }

end ComprehensionCategory.CodomainModel
