import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Displayed.Basic
import DoubleDisplayed.D2SFib.Straightening.Unstraighten
import DoubleDisplayed.Total

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

The context `Γ ▹ Bᵒᵖ` is the total category `(∫ B)ᵒᵖ.Total` of the dual of the unstraightening of
`B`, on objects and morphisms, so such a type `C` is a dependent profunctor over `B`: a functor
`P : (∫ B)ᵒᵖ.Total ⥤ Cat`. The twist is defined on these (`twist P`). (The two categories have
different identities and composites, as terms, those of `opCategory'` for `Γ ▹ Bᵒᵖ`; that they
agree is not something the kernel checks well, so the dependent profunctors are given on
`(∫ B)ᵒᵖ.Total` directly.) The unstraightening `Unstraightening P` is a split D2SFib over `∫ B`
(`DoubleDisplayed/D2SFib/Straightening/Unstraighten.lean`), a category doubly displayed over
`∫ B`, which is a category displayed over the total category of `∫ B`, the context `Γ ▹ B`
(`DoubleDisplayed.uncurry`). The twist is the type of the displayed model of this displayed category
(`twistDisp`), its straightening.

Concretely, the objects of `twistDisp P` over `(γ, b)` are the objects of `P (γ, b)`, and its
morphisms over `(f, β) : (γ, b) ⟶ (γ', b')`, with `β : B f b ⟶ b'`, from `c` to `c'` are the
morphisms `P(f, 𝟙) c ⟶ P(𝟙, β) c'` of `P (γ', B f b)`. Its total category is the context extension
`Γ ▹ b : B ▹ Tw(P)` of the displayed model, by `rfl`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The displayed category of the twist of a dependent profunctor `P` over `B`: its
unstraightening, displayed over the total category `Γ ▹ B` of `∫ B`. -/
def twistDisp {B : ICatLax.{u}.Ty Γ} (P : (∫ (B : Γ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u}) :
    Displayed.{u, u, u, u} ((Γ ▹ B : Cat.{u, u}) : Type u) :=
  (DoubleDisplayed.D2SFib.Straightening.Unstraightening P).uncurry

/-- **The twist of a dependent profunctor `P` over `B`** (Twist): the type of the displayed model of
`twistDisp P`. -/
def twist {B : ICatLax.{u}.Ty Γ} (P : (∫ (B : Γ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u}) :
    Straightening.LaxNormalCat.{u}.Ty (Γ ▹ B) :=
  Straightening.straightenObj (twistDisp P)

/-- The context extension of the displayed model by the twist of `P` is the total category of
`twistDisp P`. -/
theorem ext_twist {B : ICatLax.{u}.Ty Γ} (P : (∫ (B : Γ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u}) :
    (Γ ▹ B) ▹ twist P = Cat.of (twistDisp P).Total :=
  rfl

end ComprehensionCategory.OverCat
