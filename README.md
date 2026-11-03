# ShrewLib

Category theory and type theory in a fork of Lean 4 with user-declared rewrite rules, in the style
of Agda's `{-# REWRITE #-}` pragma (Cockx, Tabareau, Winterhalter, *The Taming of the Rew*,
POPL 2021, whence the name). Tagging a theorem or axiom `h : ∀ xs, lhs = rhs` with
`@[rewrite_rule]` makes `lhs ↦ rhs` part of definitional equality. Here the category and functor
laws, among others, are rules, so that many coherence laws hold by `rfl`.

The fork is [FernandoChu/lean4](https://github.com/FernandoChu/lean4), on the branch
[`local-rewrite-rules-v4.36.0-rc2`](https://github.com/FernandoChu/lean4/tree/local-rewrite-rules-v4.36.0-rc2).
Where rules fire, which left-hand sides are allowed, and what is not checked (confluence,
termination) are documented there, in
[`src/Lean/RewriteRules.lean`](https://github.com/FernandoChu/lean4/blob/local-rewrite-rules-v4.36.0-rc2/src/Lean/RewriteRules.lean).

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
- `Displayed/`: categories displayed over a category, in six folders: `Displayed/` (displayed
  categories in general), `Opfibration/` (including the unstraightening of functors `A ⥤ Cat`),
  `Fibration/` (including the codomain fibration), `Straightening/`
  (straightening–unstraightening for displayed categories, an isomorphism
  `LaxNormalCat ≅ DisplayedCat` over `Cat`), `CodCatEquiv/` (the equivalence
  `DisplayedCat ≃ cod Cat` over `Cat`, taking total categories), and `Discrete/` (discrete
  opfibrations, equivalent over `Cat` to the functors into discrete categories).
- `ComprehensionCategory/`: comprehension categories, their type formers, and models: the
  codomain model, and three models over `Cat` (`Model/OverCat/`): the category model, with
  Σ-types, opposite types and Coquand-style universes of its types and of the discrete types, its
  discrete submodel of functors into discrete categories, with Σ-types and opposite types
  preserved strictly by the inclusion, and the displayed category model of lax normal functors
  into profunctors, with Σ-types; with the type formers relating them, such as the Hom-types of
  the category model in the discrete model, and the maps between them.
- `DoubleDisplayed/`: categories doubly displayed over a displayed category, and dependent 2-sided
  fibrations with their straightening.

## Building

Build the fork's branch and link it in elan as the toolchain `rewrite-v4.36.0-rc2`, which
`lean-toolchain` names:

```sh
elan toolchain link rewrite-v4.36.0-rc2 <path-to-fork>/build/release/stage1
lake build   # only compiles the Mathlib modules these files import
```

Mathlib is a git dependency, pinned to its `v4.36.0-rc2` tag, which the fork is based on, and
cloned by Lake into `.lake/packages/`. Use `MATHLIB_NO_CACHE_ON_UPDATE=1` for any `lake update`. Otherwise Mathlib's hook tries to
fetch its cache, which doesn't apply to the patched compiler. After rebuilding the toolchain with
a new commit, Lake will recompile the imported Mathlib modules.
