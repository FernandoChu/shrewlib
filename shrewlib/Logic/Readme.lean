import Logic.EmptyUnique

/-!
# Logic

Principles about Lean's types that are independent of its axioms, used as hypotheses of the
results that need them rather than as axioms.

* `EmptyUnique`: uniqueness of empty types, `EmptyUnique.{u}`, which holds in the set-theoretic
  model of Lean. It makes discrete categories their own opposites
  (`CategoryTheory/Opposite/Discrete`), and so the discrete types of the discrete model
  (op-Disc, `ComprehensionCategory/Model/OverCat/Discrete`).
-/

universe u

/-! ## Main results -/

/-- If empty types are unique, an empty type is `PEmpty`. -/
recall EmptyUnique.eq_pempty (hE : EmptyUnique.{u}) (α : Type u) [IsEmpty α] : α = PEmpty
