import ComprehensionCategory.Model.OverCat.CatOp.Basic
import ComprehensionCategory.TypeFormers.Sigma
import Displayed.Fibration.Sigma
import Displayed.Fibration.Straightening.Equivalence
import Tactic.KernelTactic

/-!
# Σ-types in the contravariant category model

For `A : Γᵒᵖ ⥤ Cat` and `B : (Γ ⋉⁻ A)ᵒᵖ ⥤ Cat`, the unstraightenings `∫⁻ A` over `Γ` and `∫⁻ B` over
`Γ ⋉⁻ A = (∫⁻ A).Total` are split fibrations, and so is their composite `sigmaOb A B`, that is
`(∫⁻ A).sigmaDisp (∫⁻ B)`, over `Γ` (`Displayed.sigmaSplitFib`). The Σ-type `sigma A B` is its
straightening, which sends `γ` to the fibre of `sigmaOb A B` over `γ`.

The pairing is the composite of two isomorphisms over `Γ`:

```
  Γ ⋉⁻ A ⋉⁻ B ≅ (sigmaOb A B).toDisplayed.Total ≅ Γ ⋉⁻ sigma A B
```

the reassociation of the pairs (`Displayed.sigmaUnassoc`), and the total functor of the inverse of
the counit of straightening–unstraightening (`counitInv`). Its inverse is the counit followed by
the reassociation, and both lie over `Γ` by `rfl`.

The Σ-types are stable under substitution since the reindexing of `sigmaOb A B` along `σ` and
`sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄` agree fieldwise: their fibres are the same, and so are their transports,
which unfold to the same factorizations (`pullMap_eq_lift`). These definitional equalities are
checked in the kernel (`kernel_rfl'`).

This is the dual of `OverCat/Cat/TypeFormers/Sigma.lean`.
-/

universe u

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Opposite Displayed Displayed.Fibration.Straightening

variable {Γ : Cat.{u, u}} (A : Γᵒᵖ ⥤ Cat.{u, u}) (B : (Γ ⋉⁻ A)ᵒᵖ ⥤ Cat.{u, u})

/-- The composite of the unstraightenings of `A` and `B`, a split fibration over `Γ`. -/
def sigmaOb : SplitFibOb Γ := ⟨(∫⁻ A).sigmaDisp (∫⁻ B)⟩

/-- The Σ-type `sigma A B : Γᵒᵖ ⥤ Cat`, the straightening of `sigmaOb A B`. -/
def sigma : Γᵒᵖ ⥤ Cat.{u, u} := straightenObj (sigmaOb A B)

/-- `Γ ⋉⁻ A ⋉⁻ B ⟶ Γ ⋉⁻ sigma A B`: reassociate, then the inverse of the counit. -/
def pairHom : Cat.of (Γ ⋉⁻ A ⋉⁻ B) ⟶ Cat.of (Γ ⋉⁻ CatOpModel.sigma A B) :=
  ((∫⁻ A).sigmaUnassoc (∫⁻ B) ⋙ (counitInv (sigmaOb A B)).total).toCatHom

/-- `Γ ⋉⁻ sigma A B ⟶ Γ ⋉⁻ A ⋉⁻ B`: the counit, then reassociate. -/
def unpairHom : Cat.of (Γ ⋉⁻ CatOpModel.sigma A B) ⟶ Cat.of (Γ ⋉⁻ A ⋉⁻ B) :=
  ((counitHom (sigmaOb A B)).total ⋙ (∫⁻ A).sigmaAssoc (∫⁻ B)).toCatHom

section Pull

variable {Δ Γ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatOpLax.{u, u}.Ty Γ)
    (B : ICatOpLax.{u, u}.Ty (Γ ▹ A))

/-- Transport in `sigmaOb A B` along `σ f` is transport in `sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄` along `f`:
both unfold to the same factorization. -/
theorem pullMap_sigmaOb_pull {δ δ' : Δ} (f : δ ⟶ δ')
    {X Y : (sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed.Fiber δ'} (β : X ⟶ Y) :
    (sigmaOb A B).toDisplayed.pullMap (σ.toFunctor.map f) β ≍
      (sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed.pullMap f β :=
  heq_of_eq_of_heq
    (pullMap_eq_lift (sigmaOb A B).toDisplayed (σ.toFunctor.map f) (x := X) (y := Y) β)
    (heq_of_heq_of_eq (by kernel_rfl')
      (pullMap_eq_lift (sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed f β).symm)

/-- The pullback functors of `sigmaOb A B` along `σ f` and of `sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄` along
`f` agree. The cast along the equality of their types, checked in the kernel, keeps the elaborator
from unifying the two fibres. -/
theorem pullFunctor_sigmaOb_pull {δ δ' : Δ} (f : δ ⟶ δ') :
    cast (by kernel_rfl' : ((sigmaOb A B).toDisplayed.Fiber (σ.toFunctor.obj δ') ⥤
        (sigmaOb A B).toDisplayed.Fiber (σ.toFunctor.obj δ)) =
      ((sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed.Fiber δ' ⥤
        (sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed.Fiber δ))
      ((sigmaOb A B).toDisplayed.pullFunctor (σ.toFunctor.map f)) =
    (sigmaOb A⦃σ⦄ B⦃𝐪(σ, A)⦄).toDisplayed.pullFunctor f :=
  Functor.hext (fun _ => by kernel_rfl') fun _ _ β => by
    kernel_exact pullMap_sigmaOb_pull σ A B f β

end Pull

/-- The Σ-types of the contravariant category model, stable under substitution. -/
instance preSigma : PreSigma ICatOpLax.{u, u, u, u} where
  sigma A B := CatOpModel.sigma A B
  pull_sigma σ A B := Functor.hext (fun _ => by kernel_rfl') fun _ _ f => by
    kernel_exact heq_of_eq (congrArg Functor.toCatHom (pullFunctor_sigmaOb_pull σ A B f.unop))

/-- **The contravariant category model has Σ-types.** -/
instance hasSigma : HasSigma ICatOpLax.{u, u, u, u} where
  pair A B := pairHom A B
  unpair A B := unpairHom A B
  pair_unpair _ _ := rfl
  unpair_pair _ B := by
    kernel_exact congrArg (fun H => (DispFunctor.total H).toCatHom)
      (counitIso (sigmaOb _ B)).hom_inv_id
  pair_proj _ _ := rfl
  pair_q _ _ _ := Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

end ComprehensionCategory.CatOpModel
