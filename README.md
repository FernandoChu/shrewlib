# Rewrite rules for Lean

Experiments with user-declared rewrite rules in Lean 4, in the style of Agda's
`{-# REWRITE #-}` pragma ([Cockx, Tabareau, Winterhalter, *The Taming of the Rew*, POPL 2021]).
They need a patched Lean, on the branch `rewrite-rules-v4.35.0-rc2` of the fork in
`../lean4-v4.35.0-rc2`, built and linked in elan as the toolchain `rewrite-rc2`.

## Usage

Tag a theorem or axiom `h : ∀ xs, lhs = rhs` with `@[rewrite_rule]`:

```lean
axiom Circle.rec {α : Sort u} (b : α) (l : b = b) : Circle → α
@[rewrite_rule]
axiom Circle.rec_base {α : Sort u} (b : α) (l : b = b) : Circle.rec b l Circle.base = b

example (b : Nat) (l : b = b) : Circle.rec b l Circle.base = b := rfl

attribute [rewrite_rule] Category.id_comp Category.comp_id Category.assoc
```

From then on `lhs ↦ rhs` is part of definitional equality, in files that import the rule.

## How it works

**Where rules fire.** Both the elaborator (`Meta.whnfCore`) and the kernel (`whnf_core`) try
the rules on an application `f a₁ … aₙ` whose head constant `f` is otherwise stuck. That is,
after β, `match`/recursor and projection reduction fail, but before `f` is unfolded. Extra
arguments beyond the left-hand side are kept. Rules whose head is a projection function, such as
`Hom.app`, also fire on the corresponding primitive projection `η.1`.

When several rules apply, the one declared last is used, since later rules are usually more
specific. When the definitional-equality checker compares two applications of the same rule head,
it compares their arguments before rewriting either side, as lazy delta reduction does for
definitions.

**Patterns.** The left-hand side must be `f p₁ … pₙ` with `f` a constant that is neither an
inductive type nor a constructor. Each `pᵢ` is one of:

- a variable of `xs`. A repeated variable is checked by definitional equality.
- a constant applied to patterns, `c q₁ … qₘ`. The target is rewritten and unfolded one step at
  a time until `c` appears at its head, so the output of another rule or a β-redex can still
  match. If its arguments then don't match, the target is unfolded further and tried again.
- any other term, for example a closed term or a lambda. It is checked by definitional equality
  after the other positions have bound its variables.

Implicit and instance arguments are determined by the explicit ones only up to definitional
equality: an index `f ≫ g` in the type of an argument can appear as `𝟙 x` in the target, and the
same instance can be reached along different paths. So implicit arguments that are variables are
bound first, then explicit arguments are matched, and the remaining implicit arguments are checked
by definitional equality once their variables are bound (or matched structurally, falling back to
definitional equality, if not).

Every variable and universe parameter of `h` must occur in a pattern position (one of the first
two kinds).

**Trust.** Rules are stored in an environment extension that persists across imports. The
kernel only reads the *names* of the tagged declarations and re-derives each rule from the
declaration's checked type. A rule justified by a theorem therefore adds no logical strength:
definitional equality only gains equations that already hold. A rule justified by an axiom is
as trustworthy as the axiom.

**Not checked.** Neither confluence nor termination is checked:

- A looping rule makes type checking loop.
- Overlapping rules can make `rfl` depend on the order of reduction. For example, a naturality
  rule `η.app (P.lmap f x) ↦ Q.lmap f (η.app x)` also fires on concrete `η` whose naturality
  holds only propositionally.
- `#print axioms` doesn't report the rules a proof used.
- External checkers (lean4lean, nanoda) don't know about rules.

**Writing rules.** Some consequences of the above, learned in `Nfib/`:

- A rule on a definition `f` makes `f xs` stop being recognizably equal to its unfolding when the
  rule applies. Facts about the unfolding are best proved before the rule is declared, for example
  as `HEq`s that `eq_of_heq` turns into equations afterwards.
- A definition that the rules rewrite back into itself when unfolded, such as `transpMap` in `Nfib/`,
  must be an `irreducible_def`, or unfolding it loops.
- Nested subpatterns should use the most unfolded form of a term, since targets are unfolded
  towards the pattern and not the other way; heads need a rule for each form.
- Index-like arguments should be implicit, so that they are checked by definitional equality.
- A rule on `Functor.obj` or `Functor.map` is tried on every functor application. Rules keyed on
  dedicated constants are cheaper.

## Files

- `FunctorId.lean`: `F.map (𝟙 a) x = x` by `rfl` for any functor `F : A ⥤ Type`, after making
  Mathlib's `Functor.map_id` a rule.
- `Profunctor.lean`: profunctors as a structure with actions `lmap`/`rmap`; composition as a
  coend quotient; the bicategory `ProfCat`. The category laws, the action laws and the
  naturality of 2-cells are rules, so most coherence laws hold by `rfl`.
- `Unstraightening.lean`: the unstraightening of a lax normal functor
  `LocallyDiscrete C ⥤ ProfCat` to a category over `C`. With normality and `F.map₂ (𝟙 _) = 𝟙 _`
  as rules, the construction uses no `eqToHom` or `cast`.
- `DoubleCategory.lean`: pseudo double categories, following *Univalent Double Categories*
  (van der Weide, Rasekh, Ahrens, North) without univalence: a two-sided displayed category of
  horizontal morphisms and squares, horizontal identities and composition, and invertible,
  natural unitors and associator subject to the triangle and pentagon laws. With the category laws
  as rules, the displayed laws are stated without transport. The horizontal bicategory of
  globular squares is constructed as an application.
- `Nfib/`: displayed categories and dependent 2-sided fibrations. The main theorem
  `d2sfibEquivalence` is the equivalence between functors `∫(Bᵈᵒ) ⥤ Cat` and D2SFibs over a
  split opfibration `B`. It is a rewrite of a development on Lean and Mathlib `v4.30.0-rc2` whose
  laws were stated with `castHom`, `eqToHom` and `HEq` (commit `4b55ea2` of this repository). Here
  the displayed laws, the splitting of `B`, the functoriality of its transport, and the laws of the
  chosen pullbacks and pushforwards of a D2SFib are rules, so they are plain equations; the dual
  opfibration computes, and the Grothendieck construction, its `D2SFib` structure and much of the
  unit and counit hold by `rfl`. It is about half the size of the original. The plan, the list of
  deviations from it (for the original) and the paper are in `docs/nfib/`.
- `mathlib4/`: Mathlib master, pinned to `v4.35.0-rc2`, used as a path dependency.

## Building

```sh
lake build   # only compiles the Mathlib modules these files import
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1` for any `lake update`. Otherwise Mathlib's hook tries to
fetch its cache, which doesn't apply to the patched compiler. After rebuilding the toolchain with
a new commit, Lake will recompile the imported Mathlib modules.
