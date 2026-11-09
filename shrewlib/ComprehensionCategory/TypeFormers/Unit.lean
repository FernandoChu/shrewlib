import ComprehensionCategory.Map
import ComprehensionCategory.Term

/-!
# Unit types in a comprehension category

A comprehension category has (split) *unit types* if there is a type `D.unit Γ` in every context
`Γ`, stable under substitution on the nose, `(D.unit Γ)⦃σ⦄ = D.unit Δ`, with a term
`D.star Γ : Tm(Γ, D.unit Γ)` that is η: `𝐩 (D.unit Γ) ≫ (D.star Γ).sec = 𝟙`. So the projection is
an isomorphism of contexts

```
  𝐩 (D.unit Γ) : Γ ▹ D.unit Γ ≅ Γ
```

(`unitIso`), with inverse `(D.star Γ).sec`: Jacobs' strong unit types, the terminal objects of
the fibers that comprehension sends to terminal objects of `C / Γ`.

The other laws follow from η: every term of `D.unit Γ` is `D.star Γ` (`Tm.eq_star`), and so the
star is stable under substitution, `(D.star Γ)⦃σ⦄ = D.star Δ` (`star_pull`), which is well typed
by the rule `pull_unit`.

As for Σ-types, it comes in two classes:

* `PreUnit D`: the type former and its stability, `(D.unit Γ)⦃σ⦄ = D.unit Δ`, a rewrite rule;
* `HasUnit D`: the term `star` and η. The `PreUnit D` is an instance field, so that the rule
  applies to the statements about `star`, such as its substitution.

A strict map of comprehension categories *preserves unit types strictly*
(`StrictComprehensionMap.PreservesUnit`) if it sends unit types to unit types. Unlike the pairings
of Σ-types, the stars then go to stars (`StrictComprehensionMap.PreservesUnit.map_star`), since
`(D.star Γ).sec` is the inverse of the projection, which a strict map preserves. As for pairings,
this is stated heterogeneously.
-/

universe v u v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- Unit types on a comprehension category: a type in every context, stable under substitution
on the nose. The stability is a rewrite rule, stated with `Fib.pull`, on which the rules for
substitution are keyed; `pull_unit` below is the rule for `D.pull`. -/
class PreUnit (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] where
  /-- The unit type in context `Γ`. -/
  unit : ∀ Γ : C, D.Ty Γ
  /-- The unit type is closed: `(unit Γ)⦃σ⦄ = unit Δ`. -/
  pull_unit : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ), Fib.pull σ (unit Γ) = unit Δ

attribute [rewrite_rule] PreUnit.pull_unit

section

variable (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] [PreUnit D]

/-- The unit type in context `Γ`. -/
@[reducible] def unit (Γ : C) : D.Ty Γ :=
  PreUnit.unit Γ

/-- **The unit type is closed**: it is stable under substitution. -/
@[rewrite_rule]
theorem pull_unit {Δ Γ : C} (σ : Δ ⟶ Γ) : (D.unit Γ)⦃σ⦄ = D.unit Δ :=
  PreUnit.pull_unit σ

end

/-- Unit types on a comprehension category: closed unit types with a term `star Γ` that is η,
`𝐩 (D.unit Γ) ≫ (star Γ).sec = 𝟙`, so that the projection `Γ ▹ D.unit Γ ⟶ Γ` is an
isomorphism. -/
class HasUnit (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] where
  /-- The underlying unit types. -/
  [toPreUnit : PreUnit D]
  /-- The term of the unit type. -/
  star : ∀ Γ : C, Tm(Γ, D.unit Γ)
  /-- η: the section of the star is inverse to the projection. -/
  proj_star : ∀ Γ : C, 𝐩 (D.unit Γ) ≫ (star Γ).sec = 𝟙 (Γ ▹ D.unit Γ)

attribute [instance_reducible, instance] HasUnit.toPreUnit

section

variable (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] [HasUnit D] {Δ Γ : C}

/-- The term of the unit type in context `Γ`. -/
def star (Γ : C) : Tm(Γ, D.unit Γ) :=
  HasUnit.star Γ

/-- η: the section of the star is inverse to the projection. -/
theorem proj_star (Γ : C) : 𝐩 (D.unit Γ) ≫ (D.star Γ).sec = 𝟙 (Γ ▹ D.unit Γ) :=
  HasUnit.proj_star Γ

/-- **The projection of the unit type is an isomorphism** `Γ ▹ D.unit Γ ≅ Γ`, whose inverse is
the section of the star. -/
@[simps]
def unitIso (Γ : C) : Γ ▹ D.unit Γ ≅ Γ where
  hom := 𝐩 (D.unit Γ)
  inv := (D.star Γ).sec
  hom_inv_id := D.proj_star Γ
  inv_hom_id := (D.star Γ).sec_proj

instance (Γ : C) : IsIso 𝐩 (D.unit Γ) :=
  (D.unitIso Γ).isIso_hom

/-- **Every term of the unit type is the star.** -/
theorem Tm.eq_star (t : Tm(Γ, D.unit Γ)) : t = D.star Γ :=
  Tm.ext (by rw [← Category.id_comp (D.star Γ).sec, ← t.sec_proj, Category.assoc, D.proj_star,
    Category.comp_id])

/-- **The star is stable under substitution**: `(D.star Γ)⦃σ⦄ = D.star Δ`, which is well typed by
the rule `pull_unit`. -/
theorem star_pull (σ : Δ ⟶ Γ) : (D.star Γ)⦃σ⦄ = D.star Δ :=
  Tm.eq_star D _

/-- The section of the star commutes with the morphisms `𝐪` over `σ`. -/
theorem star_sec_q (σ : Δ ⟶ Γ) : (D.star Δ).sec ≫ 𝐪(σ, D.unit Γ) = σ ≫ (D.star Γ).sec := by
  rw [← D.star_pull σ]
  exact Tm.pull_sec_q σ (D.star Γ)

end

section Preservation

variable {C' : Type u₃} [Category.{v₃} C'] {F : C ⥤ C'} {D : Displayed.{v₂, u₂} C}
  {E : Displayed.{v₄, u₄} C'} [Fib D] [Comprehension D] [HasUnit D] [Fib E]
  [Comprehension E] [HasUnit E]

/-- A strict map of comprehension categories *preserves unit types strictly* if it sends unit
types to unit types, `M (D.unit Γ) = E.unit (F.obj Γ)`. It then sends stars to stars
(`PreservesUnit.map_star`). -/
structure StrictComprehensionMap.PreservesUnit (M : StrictComprehensionMap F D E) : Prop where
  /-- Unit types go to unit types. -/
  obj_unit : ∀ Γ : C, M.toPre.obj (D.unit Γ) = E.unit (F.obj Γ)

/-- A section of the projection of a type equal to the unit type is the star. It is stated
heterogeneously, since the types of the two sections are identified only by the equation. -/
theorem sec_heq_star {Γ : C} {A : D.Ty Γ} (h : A = D.unit Γ) (s : Γ ⟶ Γ ▹ A)
    (hs : s ≫ 𝐩 A = 𝟙 Γ) : s ≍ (D.star Γ).sec := by
  subst h
  exact heq_of_eq (congrArg Tm.sec (Tm.eq_star D ⟨s, hs⟩))

/-- **A strict map preserving unit types sends stars to stars**: `F.map (D.star Γ).sec` is a
section of `F.map (𝐩 (D.unit Γ))`, which is the projection of `M (D.unit Γ) = E.unit (F.obj Γ)` by
the rules of strict maps. -/
theorem StrictComprehensionMap.PreservesUnit.map_star {M : StrictComprehensionMap F D E}
    (hM : M.PreservesUnit) (Γ : C) : F.map (D.star Γ).sec ≍ (E.star (F.obj Γ)).sec :=
  sec_heq_star (hM.obj_unit Γ) (F.map (D.star Γ).sec)
    ((F.map_comp _ _).symm.trans ((congrArg F.map (D.star Γ).sec_proj).trans (F.map_id Γ)))

end Preservation

end Displayed
