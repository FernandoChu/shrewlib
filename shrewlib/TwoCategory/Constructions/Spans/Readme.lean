import TwoCategory.Constructions.Spans.Hom
import TwoCategory.Constructions.Spans.Basic

/-!
# Spans in a 2-category

* `Hom`: spans in a 2-category. The spans between two objects form a 2-category
  (`Span.twoCategory`), whose laws hold by `rfl`.
* `Basic`: the bicategory of spans `Spans B`, whose hom-categories are those of `Hom`, composed by
  Mathlib's chosen pullbacks. Its laws reduce by extensionality to `rfl`, checked in the kernel:
  the elaborator is much slower on these. Mathlib's `Span` and `SpanBicat` are not used:
  `SpanBicat` hides its projections and associator, and the matcher of rules does not see through
  the instances of Mathlib's category of spans, so their composites do not compute.
-/

universe w v u

open CategoryTheory

/-! ## Main results -/

/-- The spans between two objects of a 2-category form a 2-category. -/
example {B : Type u} [TwoCategory.{w, v} B] (a b : B) : TwoCategory (TwoCategory.Span a b) :=
  inferInstance

/-- The spans in a 2-category with chosen pullbacks form a bicategory. -/
example {B : Type u} [TwoCategory.{w, v} B] [TwoCategory.ChosenPullbacks B] :
    Bicategory (TwoCategory.Spans B) :=
  inferInstance
