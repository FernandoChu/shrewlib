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

The context `Γ ▹ Bᵒᵖ` has the same objects and morphisms as the total category `(∫ B)ᵒᵖ.Total` of
the dual of the unstraightening of `B`: pairs `(γ, b)`, and pairs of `f : γ ⟶ γ'` and a morphism
`b' ⟶ B f b` of `B γ'`. So `C` is a dependent profunctor over `B`, a functor
`(∫ B)ᵒᵖ.Total ⥤ Cat` with the values of `C` (`asDProf`). The two categories have different
identities and composites as terms, those of `opCategory'` for `Γ ▹ Bᵒᵖ`, and the kernel does not
identify the two structures, though it does identify their components: the functor laws of
`asDProf C` are those of `C`, through extensionality of the morphisms of `Γ ▹ Bᵒᵖ`.

The unstraightening `Unstraightening (asDProf C)` is a split D2SFib over `∫ B`
(`DoubleDisplayed/D2SFib/Straightening/Unstraighten.lean`), a category doubly displayed over
`∫ B`, which is a category displayed over the total category of `∫ B`, the context `Γ ▹ B`
(`DoubleDisplayed.uncurry`). The twist is the type of the displayed model of this displayed category
(`twistDisp`), its straightening.

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

/-- **A type `C` in context `Γ ▹ Bᵒᵖ` as a dependent profunctor over `B`**: the functor
`(∫ B)ᵒᵖ.Total ⥤ Cat` with the values of `C`. Its laws are those of `C`, as the identities and
composites of the two categories agree componentwise. -/
def asDProf {B : ICatLax.{u}.Ty Γ} (C : ICatLax.{u}.Ty (Γ ▹ Bᵒᵖ)) :
    (∫ (B : Γ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u} where
  obj x := C.obj x
  map F := C.map ⟨F.base, F.fiber⟩
  map_id x := (congrArg C.map (Total.Hom.ext' rfl (by kernel_rfl'))).trans (C.map_id x)
  map_comp F G := (congrArg C.map (Total.Hom.ext' rfl (by kernel_rfl'))).trans
    (C.map_comp (X := _) (Y := _) (Z := _) ⟨F.base, F.fiber⟩ ⟨G.base, G.fiber⟩)

/-- The displayed category of the twist of `C`: the unstraightening of `C`, as a dependent
profunctor over `B`, displayed over the total category `Γ ▹ B` of `∫ B`. -/
def twistDisp {B : ICatLax.{u}.Ty Γ} (C : ICatLax.{u}.Ty (Γ ▹ Bᵒᵖ)) :
    Displayed.{u, u, u, u} ((Γ ▹ B : Cat.{u, u}) : Type u) :=
  (DoubleDisplayed.D2SFib.Straightening.Unstraightening (asDProf C)).uncurry

/-- **The twist of a type `C` in context `Γ ▹ Bᵒᵖ`** (Twist): the type of the displayed model of
`twistDisp C`, in context `Γ ▹ B`. -/
def twist {B : ICatLax.{u}.Ty Γ} (C : ICatLax.{u}.Ty (Γ ▹ Bᵒᵖ)) :
    Straightening.LaxNormalCat.{u}.Ty (Γ ▹ B) :=
  Straightening.straightenObj (twistDisp C)

/-- The context extension of the displayed model by the twist of `C` is the total category of
`twistDisp C`. -/
theorem ext_twist {B : ICatLax.{u}.Ty Γ} (C : ICatLax.{u}.Ty (Γ ▹ Bᵒᵖ)) :
    (Γ ▹ B) ▹ twist C = Cat.of (twistDisp C).Total :=
  rfl

/-- A type `C` of the category model as a type of the displayed model: the straightening of its
unstraightening `∫ C`. -/
def catToDisp (C : ICatLax.{u}.Ty Γ) : Straightening.LaxNormalCat.{u}.Ty Γ :=
  Straightening.straightenObj (∫ (C : Γ ⥤ Cat.{u, u}))

/-- The displayed category of the twist of a weakened type `C⦃𝐩 Bᵒᵖ⦄` is the reindexing of `∫ C`
along `𝐩 B`. -/
theorem twistDisp_weak (B C : ICatLax.{u}.Ty Γ) :
    twistDisp (C⦃𝐩 (Bᵒᵖ)⦄) = DisplayedCat.pull (𝐩 B) (∫ (C : Γ ⥤ Cat.{u, u})) :=
  Displayed.ext_heq rfl (by kernel_rfl') (by kernel_rfl') (by kernel_rfl')

/-- **Twist-Weak**: the twist of a type `C` weakened to `Γ ▹ Bᵒᵖ` is `C`, as a type of the
displayed model, weakened to `Γ ▹ B`. -/
theorem twist_weak (B C : ICatLax.{u}.Ty Γ) : twist (C⦃𝐩 (Bᵒᵖ)⦄) = (catToDisp C)⦃𝐩 B⦄ :=
  congrArg Straightening.straightenObj (twistDisp_weak B C)

end ComprehensionCategory.OverCat
