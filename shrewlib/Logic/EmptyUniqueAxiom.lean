import Logic.EmptyUnique

/-!
# Uniqueness of empty types, as an axiom

`emptyUnique` asserts `EmptyUnique.{u}` in every universe. It holds in the set-theoretic model of
Lean, so it is consistent with Lean's axioms, from which it is independent.

It is an axiom so that op-Disc, `Aᵒᵖ = A` for a discrete type `A`, can be a rewrite rule
(`ComprehensionCategory/Model/OverCat/Shared/OpDisc`): a rule cannot have a hypothesis that its
left-hand side does not bind, such as `hE : EmptyUnique`. Elsewhere, uniqueness of empty types stays
a hypothesis, and only the files that import this one depend on the axiom.

Terms do not record the rules that the kernel used to check them, so `#print axioms` counts the
axioms of every rule reachable from the constants of a declaration, in the environment where it is
run. In a file that imports `Shared/OpDisc`, it lists `emptyUnique` for every declaration that
mentions an opposite type, even one checked before the rules existed (as `homDisc_eq`); in a file
that does not, only for the declarations that use the axiom directly.
-/

universe u

/-- **Uniqueness of empty types, as an axiom**: any two empty types of `Type u` are equal. -/
axiom emptyUnique : EmptyUnique.{u}
