import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Universe
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The universe of discrete types

The category model at level `v + 1`, with contexts in `Cat.{v + 1, v + 1}`, has a Coquand-style
universe `UDisc Γ` of the discrete types of level `v`, the functors `Γ ⥤ Cat.{v, v}` into discrete
categories (`IDiscOb.{v, v} Γ`, the types of `SmallIDisc`, `Discrete/Small`): it is a type of the
category model, whose terms `Tm(Γ, UDisc Γ)` are exactly these functors, by inverse maps `ElDisc`
and `codeDisc`, all stable under substitution. This is a universe in the sense of
`ComprehensionCategory/TypeFormers/Universe`, along the lift of the discrete types of level `v` into
the category model, a strict map of comprehension categories (`liftDiscComprehensionMap`):
`HasUniverse liftDiscComprehensionMap`.

As for the universe `U Γ` of all the types of level `v` (`Cat/TypeFormers/Universe`), `UDisc Γ` is
a constant type: at `smallDiscCat`, the full subcategory of `Cat.{v, v}` on the discrete categories,
made a category of `Cat.{v + 1, v + 1}` by `AsSmall`. It is not itself discrete: its morphisms are
the functors between discrete categories. Its terms are the functors `Γ ⥤ smallDiscCat`
(`Tm.constEquiv`), and `ElDisc` and `codeDisc` compose this with `AsSmall.down` followed by the
inclusion of the full subcategory, and with the lift into the full subcategory followed by
`AsSmall.up`. `ElDisc (codeDisc A) = A` holds componentwise by `rfl`, and
`codeDisc (ElDisc t) = t` since `t` is the term of its values. The universe is closed by `rfl`
(`pull_UDisc`), and `ElDisc` and `codeDisc` commute with substitution (`ElDisc_pull`,
`codeDisc_pull`).

A term `t` of the universe decodes to the type `lift (ElDisc t)` of the category model
(`Displayed.decode`), and the discrete types of level `v` are types of the discrete model too, by
`liftDisc` (`Discrete/Small`).
-/

universe v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel DiscreteModel

open scoped Displayed

/-- Being discrete, a property of small categories. -/
def isDiscreteCat : ObjectProperty Cat.{v, v} :=
  fun C => IsDiscrete C

/-- The category of small discrete categories, the full subcategory of `Cat.{v, v}` on the discrete
categories, made a category of `Cat.{v + 1, v + 1}` by `AsSmall`. -/
def smallDiscCat : Cat.{v + 1, v + 1} :=
  Cat.of (AsSmall.{v + 1} isDiscreteCat.{v}.FullSubcategory)

/-- **The universe of discrete types** in context `Γ`: the constant type at the category of small
discrete categories. -/
def UDisc (Γ : Cat.{v + 1, v + 1}) : ICatLax.{v + 1, v + 1}.Ty Γ :=
  constTy Γ smallDiscCat

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- The discrete type of level `v` decoded from a term `t` of the universe: its values. -/
def ElDisc (t : Tm(Γ, UDisc Γ)) : IDiscOb.{v, v} Γ where
  toFunctor := Tm.toConst t ⋙ AsSmall.down ⋙ isDiscreteCat.ι
  isDiscrete γ := (ULift.down ((Tm.toConst t).obj γ)).property

/-- The code of a discrete type `A` of level `v`, a term of the universe: the term of its values. -/
def codeDisc (A : IDiscOb.{v, v} Γ) : Tm(Γ, UDisc Γ) :=
  Tm.ofConst (isDiscreteCat.lift A.toFunctor A.isDiscrete ⋙ AsSmall.up)

/-- `ElDisc` undoes `codeDisc`. -/
theorem ElDisc_codeDisc (A : IDiscOb.{v, v} Γ) : ElDisc (codeDisc A) = A :=
  IDiscOb.ext (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl)

/-- `codeDisc` undoes `ElDisc`: a term is the term of its values. -/
theorem codeDisc_ElDisc (t : Tm(Γ, UDisc Γ)) : codeDisc (ElDisc t) = t :=
  (congrArg Tm.ofConst (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl :
    isDiscreteCat.lift (ElDisc t).toFunctor (ElDisc t).isDiscrete ⋙ AsSmall.up =
      Tm.toConst t)).trans (Tm.ofConst_toConst t)

/-- **The universe of discrete types is closed**: it is stable under substitution. -/
theorem pull_UDisc (σ : Δ ⟶ Γ) : (UDisc Γ)⦃σ⦄ = UDisc Δ :=
  rfl

/-- `ElDisc` commutes with substitution. -/
theorem ElDisc_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, UDisc Γ)) :
    ElDisc (Γ := Δ) t⦃σ⦄ = SmallIDisc.pull σ (ElDisc t) :=
  IDiscOb.ext ((congrArg (· ⋙ AsSmall.down ⋙ isDiscreteCat.ι) (Tm.toConst_pull σ t)).trans
    (Functor.assoc _ _ _))

/-- `codeDisc` commutes with substitution. -/
theorem codeDisc_pull (σ : Δ ⟶ Γ) (A : IDiscOb.{v, v} Γ) :
    (codeDisc A)⦃σ⦄ = codeDisc (SmallIDisc.pull σ A) :=
  (Tm.ofConst_pull σ _).trans (congrArg Tm.ofConst
    (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl))

/-- The universe of the discrete types of level `v`, along their lift into the category model. -/
instance preUniverseDisc : PreUniverse liftDiscComprehensionMap.{v} where
  univ Γ := UDisc Γ
  pull_univ σ := pull_UDisc σ

/-- **The category model has a Coquand-style universe of the discrete types of level `v`**, along
their lift into the category model. -/
instance hasUniverseDisc : HasUniverse liftDiscComprehensionMap.{v} where
  El t := ElDisc t
  code A := codeDisc A
  El_code A := ElDisc_codeDisc A
  code_El t := codeDisc_ElDisc t
  El_pull σ t := ElDisc_pull σ t

end ComprehensionCategory.OverCat
