import ComprehensionCategory.Model.Discrete.Basic
import ComprehensionCategory.Model.Cat.TypeFormers.Sigma
import Displayed.Discrete.Sigma
import Displayed.Discrete.Straightening.Unstraighten

/-!
# Σ-types in the discrete model

The Σ-types of the discrete model are those of the category model. For `A : Γ ⥤ Cat` and
`B : Γ ⋉ A ⥤ Cat` into discrete categories, the Σ-type `Σ[A] B` of the category model sends `γ` to
the fibre over `γ` of the composite of the unstraightenings of `A` and `B`, whose fibres are
discrete (`isDiscrete_unstraighten`), so its fibres are discrete too (`isDiscrete_sigmaDisp`): it
takes values in discrete categories (`isDiscrete_sigma`). The pairing is that of the category
model, and so are all the laws.

So **forgetting the discreteness preserves Σ-types strictly**
(`forgetComprehensionMap_preservesSigma`), with both clauses by `rfl`: the Σ-type of the discrete
model is that of the category model with a proof of discreteness, and the pairing is the same
morphism.

With the functors into sets as types, this fails (`Basic`): their Σ-type is the set of objects of
the same fibre, and the embedding into the category model sends it to the discrete category on
that set, whose morphisms are proofs of equalities of pairs, while those of the fibre are pairs of
proofs, an equivalent but different type. Here the types keep their category structure, so the
fibre is never compared to the discrete category on its objects.
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening

open scoped Displayed

variable {Γ : Cat.{u, u}} (A : IDisc.{u}.Ty Γ) (B : IDisc.{u}.Ty (Γ ▹ A))

/-- **The Σ-types of the category model of functors into discrete categories take values in
discrete categories**: `(Σ[A] B) γ` is the fibre over `γ` of the composite of the unstraightenings
of `A` and `B`, whose fibres are discrete. -/
theorem isDiscrete_sigma (γ : Γ) :
    IsDiscrete ((ICat.{u}.sigma A.toFunctor B.toFunctor).obj γ) :=
  @isDiscrete_sigmaDisp _ _ (∫ A.toFunctor) (∫ B.toFunctor)
    (@isDiscrete_unstraighten _ A.toFunctor A.isDiscrete)
    (@isDiscrete_unstraighten _ B.toFunctor B.isDiscrete) γ

/-- The Σ-type of the discrete model: that of the category model. -/
def sigma : IDisc.{u}.Ty Γ where
  toFunctor := ICat.{u}.sigma A.toFunctor B.toFunctor
  isDiscrete := isDiscrete_sigma A B

/-- The Σ-types of the discrete model, stable under substitution since those of the category model
are. -/
instance preSigma : PreSigma IDisc.{u} where
  sigma A B := DiscreteModel.sigma A B
  pull_sigma _ _ _ := rfl

/-- **The discrete model has Σ-types**, with the pairings of the category model. -/
instance hasSigma : HasSigma IDisc.{u} where
  pair A B := HasSigma.pair (D := ICat.{u}) A.toFunctor B.toFunctor
  unpair A B := HasSigma.unpair (D := ICat.{u}) A.toFunctor B.toFunctor
  pair_unpair A B := HasSigma.pair_unpair (D := ICat.{u}) A.toFunctor B.toFunctor
  unpair_pair A B := HasSigma.unpair_pair (D := ICat.{u}) A.toFunctor B.toFunctor
  pair_proj A B := HasSigma.pair_proj (D := ICat.{u}) A.toFunctor B.toFunctor
  pair_q σ A B := HasSigma.pair_q (D := ICat.{u}) σ A.toFunctor B.toFunctor

/-- **Forgetting the discreteness preserves Σ-types strictly**: the Σ-types and the pairings of the
discrete model are those of the category model. -/
theorem forgetComprehensionMap_preservesSigma : forgetComprehensionMap.{u}.PreservesSigma where
  obj_sigma _ _ := rfl
  map_pair _ _ := HEq.rfl

end ComprehensionCategory.DiscreteModel
