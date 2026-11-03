# ShrewLib

Category theory and type theory (displayed categories, fibrations, straightening, 2-categories,
comprehension categories and their models) in a fork of Lean 4 where theorems tagged
`@[rewrite_rule]` become part of definitional equality. `README.md` summarizes every folder. Keep
it up to date when a folder's content changes.

## Toolchain and building

- `lean-toolchain` names `rewrite-v4.36.0-rc2`, the fork in `../lean4` (branch
  `local-rewrite-rules`) linked in elan. Plain Lean does not know `@[rewrite_rule]`, and most proofs
  here only hold with the rules.
- Mathlib is a git dependency at its `v4.36.0-rc2` tag. Its cache (`lake exe cache get`) does not
  apply to the patched compiler. Run any `lake update` with `MATHLIB_NO_CACHE_ON_UPDATE=1`.
- `lake build` from the repo root builds everything. `lake build Displayed.Opfibration.Basic`
  builds one module and its imports. The warnings that a file imports Mathlib modules "designed for
  use with the module system" are expected; the files here do not use `module`.
- After changing or adding a rule, rebuild everything that imports it: a rule can slow down or
  break files far from where it is declared.

## Layout

- Sources are in `shrewlib/` (`srcDir` in `lakefile.toml`). Module names have no package prefix:
  `shrewlib/Displayed/Opfibration/Basic.lean` is `Displayed.Opfibration.Basic`. A new top-level
  folder or file needs its own entry in the `globs` of `lakefile.toml`.
- Each folder has a `Readme.lean` that imports the whole folder (directly or through its top
  files and subfolder Readmes). Its module docstring summarizes each file, and it restates the main
  results with `recall`, so the build checks that they keep their statements. Update it when you
  add a file or a main result.
- Some folders are each other's duals and are kept in sync. `Displayed/Fibration/Basic.lean` mirrors
  `Displayed/Opfibration/Basic.lean` section by section (`pull`/`clift`/`pullMap` against
  `push`/`olift`/`pushMap`), and so do their `Straightening/` subfolders. Displayed and doubly
  displayed categories (`Displayed/`, `DoubleDisplayed/`) are developed in parallel.
- `Rules/` holds the rules on Mathlib's lemmas, `Tactic/` the kernel tactics, and `Examples/`
  small `#guard_msgs` demonstrations of the rules.

## Style

- Every file starts with its imports and a module docstring `/-! # Title ... -/`. The docstring
  says what the file defines and why: which equations are rules, how they are oriented, and what
  holds by `rfl` as a result. Read it before editing the file. Every declaration has a docstring.
- Lines are at most 100 characters. Proofs follow Mathlib's style. Universes are named
  `v₁ u₁ v₂ u₂ …`, and notation such as `⟶[f]`, `≫ᵈ`, `𝟙ᵈ` is used through
  `open scoped Displayed` (or `DoubleDisplayed`).
- No `sorry`, no new axioms, no `noncomputable`. Factorizations are data (as in `IsOpcartesian`)
  rather than `∃!` so that constructions from them compute and reduce.
- `set_option maxHeartbeats` is a last resort. The two uses in `D2SFib/Straightening` have a
  comment on why the computation is long. Prefer the kernel tactics below.
- Commit messages name the mathematical content ("Opposite types: HasOp with (Aᵒᵖ)ᵒᵖ = A and
  stability as rules; the category model has them"), with a wrapped body if more is needed.

## Categories of (op)fibrations

The categories displayed over `Cat` of indexed categories and of (op)fibrations are named
`⟨objects⟩⟨morphisms⟩`:

- Objects: `ICat` (functors `A ⥤ Cat`), `ICatOp` (functors `Aᵒᵖ ⥤ Cat`), and `SplitOpfib`,
  `SplitFib`, `Opfib`, `Fib` after the class of the displayed categories (split or only cloven).
- Morphisms: `Lax` (any displayed functor; lax transformations), `Ps` (displayed functors
  preserving (op)cartesian morphisms; pseudonatural transformations) or `Str` (displayed functors
  sending chosen lifts to chosen lifts, `OpcartesianFunctor` and `CartesianFunctor`; strict
  transformations). The two sides of a straightening theorem have the same suffix, as in
  `straighteningEquivLax : VertEquivalence ICatLax SplitOpfibLax`.

`DisplayedCat`/`LaxNormalCat` and `DiscOpfibCat`/`IDisc` have no suffix: their objects have no
chosen lifts, or all functors between them preserve them. Construct the functors of an
equivalence both ways, with an explicit unit and counit, rather than through
`VertEquivalence.ofFullyFaithful`, so that its inverse is the expected construction and compares
with others by `rfl`, as the strict straightening with the lax one (`straightenStr_comp_forget`).

## Kernel tactics

`Tactic/` provides `kernel_rfl'`, `kernel_exact e` and `kernel_rfl`, which check a definitional
equality in the kernel instead of the elaborator. Use them when `rfl` or `exact` is slow or times
out on terms that the rules reduce in many steps: the elaborator first tries to unify arguments of
applications with the same head, while the kernel normalizes. `kernel_rfl` also recomputes the
implicit 1-cells of whiskerings and compares weak head normal forms, for equations of 2-cells.
`kernel_exact e` elaborates `e` without the goal as expected type.

# Writing rules

How rewrite rules work (where they fire, which left-hand sides are allowed, what is not checked) is
documented in the fork, in `../lean4/src/Lean/RewriteRules.lean`. Rules are declared with
`@[rewrite_rule]` on a theorem, or `attribute [rewrite_rule]` on a structure field (often both
`simp` and `rewrite_rule`). The module docstring of each file lists its rules and their
orientation. Some lessons learned in `shrewlib/`:

- Orient rules towards a normal form: composites right-associated without identities, chosen
  lifts first, functor applications pushed inside. A new rule must agree with this orientation,
  since confluence and termination are not checked.
- A rule on a definition `f` makes `f xs` stop being recognizably equal to its unfolding when the
  rule applies. Facts about the unfolding are best proved before the rule is declared, for example
  as `HEq`s that `eq_of_heq` turns into equations afterwards.
- A definition that the rules rewrite back into itself when unfolded, such as `pushMap` in
  `Displayed/Opfibration/Basic.lean`, must be an `irreducible_def`, or unfolding it loops. Give it
  an unfolding lemma stated with constants that no rule is keyed on (`pushMap_eq_desc`) to compute
  it later. `irreducible_def` also keeps rules from seeing through a definition, as for the
  counit in `D2SFib/Straightening/Counit.lean`.
- When a structure has rules among its fields and a later field's statement needs an earlier
  rule to typecheck, make the earlier structure a field rather than a parent (`toPre` in
  `StrictComprehensionMap`, as for `SplitFib`), so that the rule applies to the later field.
- Nested subpatterns should use the most unfolded form of a term, since targets are unfolded
  towards the pattern and not the other way; heads need a rule for each form.
- Index-like arguments should be implicit, so that they are checked by definitional equality.
- A displayed category over `Cat` whose objects are an existing type (`ICatStr`, `SplitOpfibStr`,
  …) is an irreducible `def`, so `X.Ob A` is not that type for instance search, and its
  structure needs explicit instances (`ICatStr.splitOpfib`). Making it an `abbrev`, as Mathlib does
  for `Profunctor`, is right only when the category that the type then gets is the fiber category
  of `X`, as for `DProf` and `D2SFibStr`. Otherwise it picks the wrong category (the functor
  category on `ICatLax.Fiber A`, whose morphisms should be lax) or loses the fiber category, whose
  instance is indexed by the head `X`.
- A rule on `Functor.obj` or `Functor.map` is tried on every functor application. Rules keyed on
  dedicated constants are cheaper.
- A failed match costs a full unfolding search for the subpattern head. A rule keyed on a common
  head such as displayed composition, whose subpatterns are absent from most terms, slows down every
  file that imports it. The cancellation lemmas of vertical natural isomorphisms are not rules for
  this reason: as rules, they made the D2SFib development time out.
- The kernel can reject an `rfl` between two structures that the elaborator accepts, though it
  accepts each component by `rfl`; extensionality then does it, as for the associativity of
  `ICatLax` and the functor laws of the comprehension of the category model.
- For a functor `B` out of a Grothendieck construction, `B(f, 𝟙) ∘ B(𝟙, φ)` and
  `B(𝟙, F f φ) ∘ B(f, 𝟙)` are definitionally equal, both being `B(f, F f φ)`, but the functor
  rules unfold them into different terms, which the checker does not identify. Comparing such
  nested applications is also slow in the elaborator, which first tries to unify their arguments
  (one comparison unfolded `Functor.map` some 100000 times), and rules keyed on them make it worse.
  The kernel compares them quickly, so `ComprehensionCategory/Model/OverCat/Cat/TypeFormers/Sigma`
  checks these steps there.
- Rules on Mathlib's lemmas are declared only in `shrewlib/Rules/`, and each file imports only those
  it needs, so its imports show which foreign rules it sees.
