import ComprehensionCategory.Model.OverCat.Displayed.Basic
import ComprehensionCategory.TypeFormers.Sigma
import Displayed.Displayed.Sigma
import Tactic.KernelTactic

/-!
# Σ-types in the displayed category model

For `F : LaxNormal Γ` and `G : LaxNormal (Γ ▹ F)`, the unstraightenings `unstraightenObj F` over `Γ`
and `unstraightenObj G` over `Γ ▹ F = (unstraightenObj F).Total` compose to a displayed category
`sigmaOb F G` over `Γ` (`Displayed.sigmaDisp`). The Σ-type `sigma F G` is its straightening.

This is simpler than in the category model, since unstraightening undoes straightening on the nose
(`unstraightenObj_straightenObj`): the context `Γ ▹ sigma F G` is the total category of
`sigmaOb F G` itself. So the pairing `Γ ▹ F ▹ G ≅ Γ ▹ sigma F G` is the reassociation of the pairs
(`Displayed.sigmaUnassoc`, with inverse `Displayed.sigmaAssoc`), with no counit to compose with, and
its laws hold by `rfl`.

The Σ-types are stable under substitution since the straightening of a reindexing is the reindexing
of the straightening, and the reindexing of `sigmaOb F G` along `σ` agrees with
`sigmaOb F⦃σ⦄ G⦃𝐪(σ, F)⦄` on each component. This is checked in the kernel (`kernel_rfl'`): the
elaborator, unifying the two lax normal functors as a whole, times out.
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

open scoped Displayed

variable {Γ : Cat.{u, u}} (F : IProf.{u, u, u}.Ty Γ) (G : IProf.{u, u, u}.Ty (Γ ▹ F))

/-- The composite of the unstraightenings of `F` and `G`, displayed over `Γ`. -/
def sigmaOb : Displayed.{u, u} Γ :=
  (unstraightenObj F).sigmaDisp (unstraightenObj G)

/-- The Σ-type `sigma F G : LaxNormal Γ`, the straightening of `sigmaOb F G`. -/
def sigma : IProf.{u, u, u}.Ty Γ :=
  straightenObj (sigmaOb F G)

/-- `Γ ▹ F ▹ G ⟶ Γ ▹ sigma F G`: reassociate the pairs. -/
def pairHom : Γ ▹ F ▹ G ⟶ Γ ▹ sigma F G :=
  ((unstraightenObj F).sigmaUnassoc (unstraightenObj G)).toCatHom

/-- `Γ ▹ sigma F G ⟶ Γ ▹ F ▹ G`: reassociate the pairs back. -/
def unpairHom : Γ ▹ sigma F G ⟶ Γ ▹ F ▹ G :=
  ((unstraightenObj F).sigmaAssoc (unstraightenObj G)).toCatHom

/-- **The Σ-types are stable under substitution**, checked in the kernel. -/
theorem pull_sigma' {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) :
    (sigma F G)⦃σ⦄ = sigma F⦃σ⦄ G⦃𝐪(σ, F)⦄ := by
  kernel_rfl'

/-- The Σ-types of the displayed category model, stable under substitution. -/
instance preSigma : PreSigma IProf.{u, u, u} where
  sigma F G := DisplayedModel.sigma F G
  pull_sigma σ F G := pull_sigma' F G σ

/-- **The displayed category model has Σ-types**, whose pairing reassociates the pairs. -/
instance hasSigma : HasSigma IProf.{u, u, u} where
  pair F G := pairHom F G
  unpair F G := unpairHom F G
  pair_unpair _ _ := rfl
  unpair_pair _ _ := rfl
  pair_proj _ _ := rfl
  pair_q _ _ _ := rfl

omit F G in
/-- The pairing of the straightenings of displayed categories `D₁` over `Γ` and `D₂` over its total
category is the reassociation of the pairs of `D₁` and `D₂`. This holds by `rfl`, but is stated for
variables `D₁` and `D₂`: for given displayed categories, the kernel may fail to identify the
codomain `Γ ▹ sigma F G` of the pairing with the total category of the composite. -/
theorem pairHom_straightenObj (D₁ : Displayed.{u, u} Γ) (D₂ : Displayed.{u, u} (Cat.of D₁.Total)) :
    pairHom (straightenObj D₁) (straightenObj D₂) ≍ (D₁.sigmaUnassoc D₂).toCatHom :=
  HEq.rfl

end ComprehensionCategory.DisplayedModel
