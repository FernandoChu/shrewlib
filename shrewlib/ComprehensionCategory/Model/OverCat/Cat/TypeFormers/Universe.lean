import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.Model.OverCat.Maps.SmallToCat
import ComprehensionCategory.TypeFormers.Universe

/-!
# The universe in the category model

The category model at level `v + 1`, with contexts in `Cat.{v + 1, v + 1}`, has a Coquand-style
universe `U Γ` of the types of level `v`, the functors `Γ ⥤ Cat.{v, v}` (`SmallICat`, `Cat/Small`):
its terms `Tm(Γ, U Γ)` are exactly these functors, by inverse maps `El` and `code`, all stable under
substitution. This is a universe in the sense of `ComprehensionCategory/TypeFormers/Universe`,
along the lift of the types of level `v` into the category model, a strict map of comprehension
categories (`liftComprehensionMap`): `HasUniverse liftComprehensionMap`.

`U Γ` is the constant type at `smallCat`, the category `Cat.{v, v}` of small categories made a
category of `Cat.{v + 1, v + 1}` by `AsSmall`, which wraps its objects and morphisms in `ULift`. So
its terms are the functors `Γ ⥤ smallCat` (`Tm.constEquiv`), and `El` and `code` compose this with
the equivalence `AsSmall.down`, `AsSmall.up` between `smallCat` and `Cat.{v, v}`: a term `t` gives
the small category `El t γ` of its value at `γ`. `El (code A) = A` holds componentwise by `rfl`, and
`code (El t) = t` since `t` is the term of its values, by its equation as a section. The universe
is closed by `rfl` (`pull_U`), and `El` and `code` commute with substitution (`El_pull`,
`code_pull`).

A term `t` of the universe decodes to the type `lift (El t)` of the category model, which replaces
each category by the equivalent category `AsSmall` of `Cat.{v + 1, v + 1}`
(`Displayed.decode`).
-/

universe v

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- The category `Cat.{v, v}` of small categories, made a category of `Cat.{v + 1, v + 1}` by
`AsSmall`. -/
def smallCat : Cat.{v + 1, v + 1} :=
  Cat.of (AsSmall.{v + 1} Cat.{v, v})

/-- **The universe** in context `Γ`: the constant type at the category of small categories. -/
def U (Γ : Cat.{v + 1, v + 1}) : ICatLax.{v + 1}.Ty Γ :=
  constTy Γ smallCat

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- The type of level `v` decoded from a term `t` of the universe: its values. -/
def El (t : Tm(Γ, U Γ)) : Γ ⥤ Cat.{v, v} :=
  Tm.toConst t ⋙ AsSmall.down

/-- The code of a type `A` of level `v`, a term of the universe: the term of its values. -/
def code (A : Γ ⥤ Cat.{v, v}) : Tm(Γ, U Γ) :=
  Tm.ofConst (A ⋙ AsSmall.up)

/-- `El` undoes `code`. -/
theorem El_code (A : Γ ⥤ Cat.{v, v}) : El (code A) = A :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- `code` undoes `El`: a term is the term of its values. -/
theorem code_El (t : Tm(Γ, U Γ)) : code (El t) = t :=
  (congrArg Tm.ofConst (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl :
    (Tm.toConst t ⋙ AsSmall.down) ⋙ AsSmall.up = Tm.toConst t)).trans (Tm.ofConst_toConst t)

/-- **The universe is closed**: it is stable under substitution. -/
theorem pull_U (σ : Δ ⟶ Γ) : (U Γ)⦃σ⦄ = U Δ :=
  rfl

/-- `El` commutes with substitution. -/
theorem El_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, U Γ)) : El (Γ := Δ) t⦃σ⦄ = σ.toFunctor ⋙ El t :=
  (congrArg (· ⋙ AsSmall.down) (Tm.toConst_pull σ t)).trans (Functor.assoc _ _ _)

/-- `code` commutes with substitution. -/
theorem code_pull (σ : Δ ⟶ Γ) (A : Γ ⥤ Cat.{v, v}) :
    (code A)⦃σ⦄ = code (σ.toFunctor ⋙ A) :=
  (Tm.ofConst_pull σ _).trans (congrArg Tm.ofConst (Functor.assoc _ _ _).symm)

/-- The universe of the types of level `v`, along their lift into the category model. -/
instance preUniverse : PreUniverse OverCat.liftComprehensionMap.{v} where
  univ Γ := U Γ
  pull_univ σ := pull_U σ

/-- **The category model has a Coquand-style universe of the types of level `v`**, along their lift
into the category model. -/
instance hasUniverse : HasUniverse OverCat.liftComprehensionMap.{v} where
  El t := El t
  code A := code A
  El_code A := El_code A
  code_El t := code_El t
  El_pull σ t := El_pull σ t

end ComprehensionCategory.CatModel
