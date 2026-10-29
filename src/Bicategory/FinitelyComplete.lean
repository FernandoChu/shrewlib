import Bicategory.Comma
import Bicategory.Spans
import Bicategory.Monad

/-!
# Finitely complete 2-categories

A 2-category is *finitely complete* (`FinitelyComplete`) if it has chosen comma objects and finite
conical (strict 2-)limits. As for categories, finite conical limits are given by a terminal object
and pullbacks: Mathlib's `Limits.HasTerminal` and `Limits.HasPullbacks` for the underlying
1-category, with the 2-dimensional universal property (`HasTerminal`, `HasPullbacks`): for a
2-terminal object `⊤`, there is a unique 2-cell between any two 1-cells `x ⟶ ⊤`.

The *arrow object* of an object `a` is the comma object of `𝟙 a` and `𝟙 a`. As a span
`arrowSpan a` from `a` to `a`, by its legs, it is a monad (`Bicategory.Monad`, a monoid in the
monoidal category `a ⟶ a`) in the bicategory of spans `Spans B`:

* the unit `𝟙 a ⟶ arrowSpan a` is induced by the identity 2-cell of `𝟙 a`;
* the multiplication `arrowSpan a ≫ arrowSpan a ⟶ arrowSpan a` is induced by the composite of the
  universal 2-cells along the two projections of the pullback, which are composable because the
  equation of the pullback square is a rule.

This makes the arrow object an internal category in `B`, whose objects are `a`. The monad laws are
equations between 1-cells into the arrow object, which hold by the 1-dimensional universal property
of the comma object, whose equations are rules: both sides compute to the same comma cone, which is
checked by `kernel_rfl`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory

namespace TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B]

/-! ## Terminal objects -/

/-- A 2-terminal object: a terminal object of the underlying category, with a unique 2-cell
between any two 1-cells `x ⟶ t`. That is, the categories `x ⟶ t` are terminal. -/
structure IsTerminal (t : B) where
  /-- The object is terminal in the underlying category. -/
  isTerminal : Limits.IsTerminal t
  uniq₂ {x : B} {u v : x ⟶ t} (θ θ' : u ⟶ v) : θ = θ'

variable (B) in
/-- A 2-category whose chosen terminal object, in the underlying category, is 2-terminal. -/
class HasTerminal [Limits.HasTerminal B] : Prop where
  uniq₂ {x : B} {u v : x ⟶ Limits.terminal B} (θ θ' : u ⟶ v) : θ = θ'

/-- The chosen terminal object is 2-terminal. -/
noncomputable def HasTerminal.isTerminal [Limits.HasTerminal B] [HasTerminal B] :
    IsTerminal (Limits.terminal B) :=
  ⟨Limits.terminalIsTerminal, HasTerminal.uniq₂⟩

variable (B) in
/-- A finitely complete 2-category: one with chosen comma objects and finite conical limits, which
are given by a terminal object and pullbacks. -/
class FinitelyComplete extends HasCommas B where
  [hasTerminal : Limits.HasTerminal B]
  [hasTerminal₂ : HasTerminal B]
  [hasPullbacks : Limits.HasPullbacks B]
  [hasPullbacks₂ : HasPullbacks B]

attribute [instance] FinitelyComplete.hasTerminal FinitelyComplete.hasTerminal₂
  FinitelyComplete.hasPullbacks

attribute [instance_reducible, instance] FinitelyComplete.hasPullbacks₂

/-! ## The arrow object -/

noncomputable section

namespace FinitelyComplete

open HasCommas Limits

variable [FinitelyComplete B] (a : B)

/-- The arrow object of `a`: the comma object of `𝟙 a` and `𝟙 a`. -/
abbrev arrow : B :=
  comma (𝟙 a) (𝟙 a)

/-- The arrow object of `a` as a span from `a` to `a`, by its source and target. -/
def arrowSpan : (⟨a⟩ : Spans B) ⟶ ⟨a⟩ :=
  ⟨arrow a, (commaCone (𝟙 a) (𝟙 a)).left, (commaCone (𝟙 a) (𝟙 a)).right⟩

/-- The unit of the arrow monad: identity arrows, induced by the identity 2-cell of `𝟙 a`. -/
def arrowUnit : 𝟙 (⟨a⟩ : Spans B) ⟶ arrowSpan a :=
  Span.Hom.mk ((isComma (𝟙 a) (𝟙 a)).lift ⟨𝟙 a, 𝟙 a, 𝟙 (𝟙 a)⟩) (by kernel_rfl) (by kernel_rfl)

/-- The multiplication of the arrow monad: composition of arrows, induced by the composite of the
universal 2-cells along the projections of the pullback of the target and the source. -/
def arrowMul : arrowSpan a ≫ arrowSpan a ⟶ arrowSpan a :=
  Span.Hom.mk ((isComma (𝟙 a) (𝟙 a)).lift
    ⟨pullback.fst (arrowSpan a).right (arrowSpan a).left ≫ (commaCone (𝟙 a) (𝟙 a)).left,
      pullback.snd (arrowSpan a).right (arrowSpan a).left ≫ (commaCone (𝟙 a) (𝟙 a)).right,
      pullback.fst (arrowSpan a).right (arrowSpan a).left ◁ (commaCone (𝟙 a) (𝟙 a)).hom ≫
        pullback.snd (arrowSpan a).right (arrowSpan a).left ◁ (commaCone (𝟙 a) (𝟙 a)).hom⟩)
    (by kernel_rfl) (by kernel_rfl)

/-- Proves an equation of morphisms of spans into the arrow span: by the universal property of the
comma object, it reduces to an equation of comma cones that holds by `rfl`. -/
macro "arrow_ext" : tactic =>
  `(tactic| (apply Span.Hom.ext; apply (isComma _ _).ext; kernel_rfl))

theorem arrow_one_mul : arrowUnit a ▷ arrowSpan a ≫ arrowMul a = (λ_ (arrowSpan a)).hom := by
  arrow_ext

theorem arrow_mul_one : arrowSpan a ◁ arrowUnit a ≫ arrowMul a = (ρ_ (arrowSpan a)).hom := by
  arrow_ext

theorem arrow_mul_assoc : arrowMul a ▷ arrowSpan a ≫ arrowMul a =
    (α_ (arrowSpan a) (arrowSpan a) (arrowSpan a)).hom ≫ arrowSpan a ◁ arrowMul a ≫ arrowMul a := by
  arrow_ext

/-- The arrow object is a monad in the bicategory of spans: an internal category. -/
instance arrowMonad : Bicategory.Monad (arrowSpan a) where
  one := arrowUnit a
  mul := arrowMul a
  one_mul := arrow_one_mul a
  mul_one := arrow_mul_one a
  mul_assoc := arrow_mul_assoc a

end FinitelyComplete

end

end TwoCategory

end CategoryTheory
