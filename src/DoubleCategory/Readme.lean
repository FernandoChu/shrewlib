import DoubleCategory.Basic

/-!
# Double categories

* `Basic`: pseudo double categories, following *Univalent Double Categories* (van der Weide,
  Rasekh, Ahrens, North) without univalence: a two-sided displayed category of horizontal
  morphisms and squares, horizontal identities and composition, and invertible, natural unitors
  and associator subject to the triangle and pentagon laws. With the category laws as rules, the
  displayed laws are stated without transport. The horizontal bicategory of globular squares is
  constructed as an application.
-/

universe w₁ w₂ v u

open CategoryTheory

/-! ## Main results -/

/-- The horizontal bicategory of a double category, whose 2-cells are the globular squares. -/
example {C : Type u} [Category.{v} C] [DoubleCategory.{w₁, w₂} C] :
    Bicategory (DoubleCategory.Horizontal C) :=
  inferInstance
