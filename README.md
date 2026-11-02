# Rewrite rules for Lean

Experiments with user-declared rewrite rules in Lean 4, in the style of Agda's
`{-# REWRITE #-}` pragma ([Cockx, Tabareau, Winterhalter, *The Taming of the Rew*, POPL 2021]).
They need a patched Lean, on the branch `local-rewrite-rules-v4.36.0-rc2` of the fork in
`../lean4-v4.36.0-rc2`, built and linked in elan as the toolchain `rewrite-v4.36.0-rc2`.

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

**Writing rules.** Some consequences of the above, learned in `src/`:

- A rule on a definition `f` makes `f xs` stop being recognizably equal to its unfolding when the
  rule applies. Facts about the unfolding are best proved before the rule is declared, for example
  as `HEq`s that `eq_of_heq` turns into equations afterwards.
- A definition that the rules rewrite back into itself when unfolded, such as `pushMap` in
  `Displayed/Opfibration/Basic.lean`, must be an `irreducible_def`, or unfolding it loops.
- Nested subpatterns should use the most unfolded form of a term, since targets are unfolded
  towards the pattern and not the other way; heads need a rule for each form.
- Index-like arguments should be implicit, so that they are checked by definitional equality.
- A rule on `Functor.obj` or `Functor.map` is tried on every functor application. Rules keyed on
  dedicated constants are cheaper.
- A failed match costs a full unfolding search for the subpattern head. A rule keyed on a common
  head such as displayed composition, whose subpatterns are absent from most terms, slows down every
  file that imports it. The cancellation lemmas of vertical natural isomorphisms are not rules for
  this reason: as rules, they made the D2SFib development time out.
- The kernel can reject an `rfl` between two structures that the elaborator accepts, though it
  accepts each component by `rfl`; extensionality then does it, as for the associativity of
  `ICat` and the functor laws of the comprehension of the category model.
- For a functor `B` out of a Grothendieck construction, `B(f, 𝟙) ∘ B(𝟙, φ)` and
  `B(𝟙, F f φ) ∘ B(f, 𝟙)` are definitionally equal, both being `B(f, F f φ)`, but the functor
  rules unfold them into different terms, which the checker does not identify. Comparing such
  nested applications is also slow in the elaborator, which first tries to unify their arguments
  (one comparison unfolded `Functor.map` some 100000 times), and rules keyed on them make it worse.
  The kernel compares them quickly, so `ComprehensionCategory/Model/Cat/TypeFormers/Sigma`
  checks these steps there.
- Rules on Mathlib's lemmas are declared only in `src/Rules/`, and each file imports only those it
  needs, so its imports show which foreign rules it sees.

## Files

The development is one library with sources in `src/`. Module names and namespaces follow the
folders. Each folder has a `Readme.lean`, which imports the whole folder,
summarizes its files in its module docstring and restates its main results with `recall`, so that
the build checks them.

Displayed and doubly displayed categories are developed in parallel: each has `Basic` and `Total`
files, (op)cartesian morphisms (in `Displayed/{Opfibration,Fibration}/Basic` and
`DoubleDisplayed/Cartesian`), fibrations (`Displayed/{Opfibration,Fibration}`,
`DoubleDisplayed/D2SFib`) and `Straightening` folders.

- `Rules/`: rules on Mathlib's lemmas: the category and functor laws, locally discrete
  bicategories, pullback cones and strict pseudofunctors.
- `Tactic/`: `kernel_exact`, `kernel_rfl'` and `kernel_rfl`, which check definitional equalities in
  the kernel. `kernel_rfl` first makes the implicit arguments of whiskerings canonical and, if
  needed, goes through weak head normal forms.
- `Examples/`: small examples of the rules.
- `Profunctor.lean`: profunctors as a structure with actions `lmap`/`rmap`; composition as a
  coend quotient; the bicategory `ProfCat`. The action laws and the naturality of 2-cells are
  rules, so most coherence laws hold by `rfl`.
- `TwoCategory/`: 2-categories (strict bicategories), whose laws are rules, so the coherence laws
  hold by `rfl`. `Basic` has `TwoCategory`, strict pseudofunctors and adjunctions are at the top
  level, and there are four folders: `Constructions/` (the arrow 2-category, strict slices and
  spans), `Limits/` (2-pullbacks, comma objects and finitely complete 2-categories), `Monad/`
  (monads in a bicategory, strict 2-monads and their algebras, pseudo-algebras, lax idempotent
  2-monads, whose algebras are left adjoints of the units, distributive laws) and
  `Factorization/` (AWFSs; in `Comma/`, the comma factorization `f = Lf ≫ Rf` is an AWFS whose
  2-monad `R` is lax idempotent, and `R`-algebras are split reflections).
- `DoubleCategory/`: pseudo double categories, and the horizontal bicategory of globular squares.
- `Displayed/`: categories displayed over a category, in five folders: `Displayed/` (displayed
  categories in general), `Opfibration/` (including the unstraightening of functors `A ⥤ Cat`),
  `Fibration/` (including the codomain fibration), `Straightening/`
  (straightening–unstraightening for displayed categories, an isomorphism
  `LaxNormalCat ≅ DisplayedCat` over `Cat`), and `CodCatEquiv/` (the equivalence
  `DisplayedCat ≃ cod Cat` over `Cat`, taking total categories).
- `ComprehensionCategory/`: comprehension categories, their type formers, and models: the
  category model, with Σ-types, opposite types and Hom-types, and the codomain model.
- `DoubleDisplayed/`: categories doubly displayed over a displayed category, and dependent 2-sided
  fibrations with their straightening.
- `mathlib4/`: Mathlib, checked out at its `v4.36.0-rc2` tag, used as a path dependency.

## Building

```sh
lake build   # only compiles the Mathlib modules these files import
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1` for any `lake update`. Otherwise Mathlib's hook tries to
fetch its cache, which doesn't apply to the patched compiler. After rebuilding the toolchain with
a new commit, Lake will recompile the imported Mathlib modules.
