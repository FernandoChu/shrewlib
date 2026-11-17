import CategoryTheory.Discrete
import CategoryTheory.Opposite.Readme

/-!
# Category theory

In this folder are constructions on plain categories that the rest of the library builds on.

* `Discrete`: discrete categories `discrete' S`, whose morphisms are the proofs of equalities,
  and functions between them as functors; morphisms of any `IsDiscrete` category between equal
  objects are `HEq`. It imports no rewrite rules.
* `Opposite/`: the strictly involutive opposite of a category, `opFunctor' : Cat ⥤ Cat`, and the
  opposite of a discrete category, which is the category itself if empty types are unique.
-/
