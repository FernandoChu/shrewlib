import ComprehensionCategory.Map

/-!
# The codomain comprehension category

A category `C` with chosen pullbacks is a full comprehension category over itself: the
codomain fibration `cod C` (`Displayed/Displayed/Codomain`), with the identity as comprehension
functor. A type in context `Γ` is a morphism `p : X ⟶ Γ`, `Γ ▹ p` is `X`, and substitution is
pullback.

The comprehension functor of any comprehension category `D` over `C` is a pseudo map to it, over
the identity, with identity comparisons (`comprMap`). It is not strict: it need not send the
chosen lifts of `D` to the chosen pullbacks of `C`.
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

/-- **The comprehension functor is a pseudo map** from `D` to the codomain comprehension category,
over the identity, with identity comparisons: the comprehension functor of `cod C` is the identity.
It is not a strict map, which preserves the chosen lifts: the pullback square of `𝐪(σ, A)` need not
be the chosen pullback of `C`. -/
def comprMap [ChosenPullbacks C] (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] :
    PseudoComprehensionMap (𝟭 C) D (cod C) where
  obj A := D.compr.obj A
  map φ := D.compr.map φ
  isCartesianMap H := D.isCartesianComprMap H
  cmp _ := 𝟙 _
  cmp_proj _ := Category.id_comp _
  cmp_natural _ := (Category.comp_id _).trans (Category.id_comp _).symm
  cmpInv _ := 𝟙 _
  cmp_cmpInv _ := Category.comp_id _
  cmpInv_cmp _ := Category.comp_id _

end ComprehensionCategory.CodomainModel
