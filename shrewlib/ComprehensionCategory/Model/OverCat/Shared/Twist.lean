import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Displayed.Basic
import DoubleDisplayed.D2SFib.Straightening.Unstraighten
import DoubleDisplayed.Total
import Tactic.KernelTactic

/-!
# Twisted types

A type `C` of the category model in context `Γ ▹ Bᵒᵖ`, which depends contravariantly on a variable
of `B`, has a *twist* `Tw(C)`, a type of the displayed category model in context `Γ ▹ B`, which
depends on it covariantly:

```
       Γ ⊢ B type        Γ ▹ b : Bᵒᵖ ⊢ C type
  ------------------------------------------- Twist
             Γ ▹ b : B ⊢ Tw(C) type
```

The context `Γ ▹ Bᵒᵖ` is the total category `(∫ (B ⋙ opFunctor')).Total`, with objects `(γ, b)`,
and morphisms `(γ, b) ⟶ (γ', b')` the pairs of `f : γ ⟶ γ'` and a morphism `b' ⟶ B f b` of `B γ'`.
So `C` is, as it is, a dependent profunctor over `B`: a functor
`(∫ (B ⋙ opFunctor')).Total ⥤ Cat`, an object of `DProf` over `B`.

The unstraightening `Unstraightening C` is a split D2SFib over `∫ B`
(`DoubleDisplayed/D2SFib/Straightening/Unstraighten.lean`), a category doubly displayed over
`∫ B`, which is a category displayed over the total category of `∫ B`, the context `Γ ▹ B`
(`DoubleDisplayed.overTotal`). The twist is the type of the displayed model of this displayed
category (`twistDisp`), its straightening.

Concretely, the objects of `twistDisp C` over `(γ, b)` are the objects of `C (γ, b)`, and its
morphisms over `(f, β) : (γ, b) ⟶ (γ', b')`, with `β : B f b ⟶ b'`, from `c` to `c'` are the
morphisms `C(f, 𝟙) c ⟶ C(𝟙, β) c'` of `C (γ', B f b)`. Its total category is the context extension
`Γ ▹ b : B ▹ Tw(C)` of the displayed model, by `rfl`.

The twist of a type that does not depend on `b` is that type, weakened:

```
       Γ ⊢ B type        Γ ⊢ C type
  ----------------------------------- Twist-Weak
    Γ ▹ b : B ⊢ Tw_b(C) ≡ C type_d
```

Here a type `C` of the category model is seen as a type of the displayed model (`catToDisp C`),
the straightening of its unstraightening `∫ C`. The twist of the weakening `C⦃𝐩 Bᵒᵖ⦄` is the
weakening of `catToDisp C` along `𝐩 B` (`twist_weak`): over `(f, β)`, the morphisms
`C(f, 𝟙) c ⟶ C(𝟙, β) c'` of the twist are the morphisms `C f c ⟶ c'` of `∫ C` over `f`, since
`C(𝟙, β)` is `C 𝟙`, the identity. The two displayed categories agree on their hom-types,
identities and composites by `rfl`, checked in the kernel (`twistDisp_weak`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The displayed category of the twist of `C`: the unstraightening of `C`, a dependent profunctor
over `B`, displayed over the total category `Γ ▹ B` of `∫ B`. -/
def twistDisp {B : ICatLax.{u, u}.Ty Γ} (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ)) :
    Displayed.{u, u} (Γ ▹ B : Cat.{u, u}) :=
  (DoubleDisplayed.D2SFib.Straightening.Unstraightening (F := B) C).overTotal

/-- **The twist of a type `C` in context `Γ ▹ Bᵒᵖ`** (Twist): the type of the displayed model of
`twistDisp C`, in context `Γ ▹ B`. -/
def twist {B : ICatLax.{u, u}.Ty Γ} (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ)) :
    Straightening.LaxNormalCat.{u, u, u}.Ty (Γ ▹ B) :=
  Straightening.straightenObj (twistDisp C)

/-- The context extension of the displayed model by the twist of `C` is the total category of
`twistDisp C`. -/
theorem ext_twist {B : ICatLax.{u, u}.Ty Γ} (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ)) :
    (Γ ▹ B) ▹ twist C = Cat.of (twistDisp C).Total :=
  rfl

/-- A type `C` of the category model as a type of the displayed model: the straightening of its
unstraightening `∫ C`. -/
def catToDisp (C : ICatLax.{u, u}.Ty Γ) : Straightening.LaxNormalCat.{u, u, u}.Ty Γ :=
  Straightening.straightenObj (∫ C)

/-- The displayed category of the twist of a weakened type `C⦃𝐩 Bᵒᵖ⦄` is the reindexing of `∫ C`
along `𝐩 B`. -/
theorem twistDisp_weak (B C : ICatLax.{u, u}.Ty Γ) :
    twistDisp (C⦃𝐩 (Bᵒᵖ)⦄) = DisplayedCat.pull (𝐩 B) (∫ C) :=
  Displayed.ext_heq rfl (by kernel_rfl') (by kernel_rfl') (by kernel_rfl')

/-- **Twist-Weak**: the twist of a type `C` weakened to `Γ ▹ Bᵒᵖ` is `C`, as a type of the
displayed model, weakened to `Γ ▹ B`. -/
theorem twist_weak (B C : ICatLax.{u, u}.Ty Γ) : twist (C⦃𝐩 (Bᵒᵖ)⦄) = (catToDisp C)⦃𝐩 B⦄ :=
  congrArg Straightening.straightenObj (twistDisp_weak B C)

end ComprehensionCategory.OverCat
