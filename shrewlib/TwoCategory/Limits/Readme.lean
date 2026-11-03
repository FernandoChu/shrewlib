import TwoCategory.Limits.Pullback
import TwoCategory.Limits.ChosenPullbacks
import TwoCategory.Limits.Comma
import TwoCategory.Limits.FinitelyComplete

/-!
# Limits in a 2-category

* `Pullback`: 2-pullbacks `IsPullback`, Mathlib's limit pullback cones `IsLimit t` in the
  underlying category with the 2-dimensional universal property. The equations of Mathlib's
  pullback cones and induced 1-cells are rules (`Rules.Pullback`), so 2-cells over
  `t.fst ≫ f = t.snd ≫ g` need no transport; here they get their whiskered forms.
* `ChosenPullbacks`: a chosen pullback (Mathlib's `ChosenPullback`) of every cospan, as data, so
  that constructions with them are computable, and `HasPullbacks`, the 2-dimensional universal
  property of the chosen pullbacks. Their equations are rules, imported only where chosen pullbacks
  are used, and `pullback_ext` applies extensionality.
* `Comma`: comma cones (Mathlib's `Comma (postcomp x f) (postcomp x g)`) and comma objects
  `IsComma s`: precomposing with `s` is an isomorphism of categories `(x ⟶ p) ≅ CommaCone f g x`.
  The induced 1-cells compute by rules. Comma objects are unique up to isomorphism of apexes,
  pasting a pullback on their left gives a comma object (`IsComma.pasteLeft`), and in the
  2-category `Cat`, `Comma L R` is a comma object, with the universal property by `rfl`.
  `comma_ext` and `comma_ext₂` apply extensionality into chosen comma objects.
* `FinitelyComplete`: finitely complete 2-categories (Mathlib's terminal object and pullbacks,
  with the 2-dimensional universal property, and comma objects), and the arrow object
  `comma (𝟙 a) (𝟙 a)` as a monad in `Spans B`: an internal category. Its laws hold by the
  universal property of the comma object and `kernel_rfl`.
-/

universe w v u

open CategoryTheory TwoCategory

/-! ## Main results -/

/-- Pasting a pullback on the left of a comma object gives a comma object. -/
example {B : Type u} [TwoCategory.{w, v} B] {a b c a' p : B} {f : a ⟶ c} {g : b ⟶ c}
    {h : a' ⟶ a} {s : CommaCone f g p} {t : Limits.PullbackCone h s.left} (hs : IsComma s)
    (ht : IsPullback t) : IsComma (s.pasteLeft t) :=
  hs.pasteLeft ht

/-- In `Cat`, the comma category is a comma object. -/
example {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C] (L : A ⥤ C)
    (R : B ⥤ C) : IsComma (Comma.commaCone L R) :=
  Comma.isComma L R

/-- In a finitely complete 2-category, the arrow object is an internal category. -/
example {B : Type u} [TwoCategory.{w, v} B] [FinitelyComplete B] (a : B) :
    Bicategory.Monad (FinitelyComplete.arrowSpan a) :=
  inferInstance
