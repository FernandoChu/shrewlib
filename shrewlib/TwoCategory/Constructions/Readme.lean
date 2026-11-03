import TwoCategory.Constructions.Arrow
import TwoCategory.Constructions.Slice
import TwoCategory.Constructions.Spans.Readme

/-!
# Constructions of 2-categories

2-categories built from a 2-category `B`, whose 1- and 2-cells are those of `B` subject to
equations. These equations are rules, so the conditions on 2-cells need no transport, and the laws
hold by `rfl`.

* `Arrow`: the arrow 2-category `Arr B`, whose 1-cells are commutative squares and whose 2-cells
  are pairs of 2-cells `(α, β)` with `α ▷ g = f ◁ β`.
* `Slice`: the strict slice 2-category `Slice b`, whose 1-cells are 1-cells over `b` and whose
  2-cells `α` satisfy `α ▷ y.hom = 𝟙 x.hom`.
* `Spans/`: the 2-categories of spans `Span a b`, and the bicategory of spans `Spans B`.
-/

universe w v u

open CategoryTheory

/-! ## Main results -/

/-- The arrow 2-category. -/
example {B : Type u} [TwoCategory.{w, v} B] : TwoCategory (TwoCategory.Arr B) :=
  inferInstance

/-- The strict slice 2-category. -/
example {B : Type u} [TwoCategory.{w, v} B] (b : B) : TwoCategory (TwoCategory.Slice b) :=
  inferInstance
