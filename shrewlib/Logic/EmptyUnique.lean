import Mathlib.Basic.IsEmpty.Defs

/-!
# Uniqueness of empty types

`EmptyUnique.{u}` states that any two empty types of `Type u` are equal. It is the analogue for
types of what `propext` gives for propositions, where any two false propositions are equal.

It holds in the set-theoretic model of Lean, where types are sets and every empty type is the
empty set, so it is consistent with Lean's axioms, but it is independent of them: two empty types,
such as `PEmpty` and `Fin 0`, are not provably equal. It is used as a hypothesis, not an axiom, so
that the results that need it say so in their statements.

It makes a discrete category its own opposite (`CategoryTheory/Opposite/Discrete`): the morphisms
`x ⟶ y` and `y ⟶ x` of a discrete category are equal when `x = y`, and empty types otherwise.
-/

universe u

/-- **Uniqueness of empty types**: any two empty types of `Type u` are equal. It holds in the
set-theoretic model of Lean, but is independent of its axioms. -/
def EmptyUnique : Prop :=
  ∀ α β : Type u, IsEmpty α → IsEmpty β → α = β

/-- If empty types are unique, an empty type is `PEmpty`. -/
theorem EmptyUnique.eq_pempty (hE : EmptyUnique.{u}) (α : Type u) [IsEmpty α] : α = PEmpty :=
  hE α PEmpty inferInstance inferInstance
