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
  `v₁ u₁ v₂ u₂ …`. `Displayed` and `DoubleDisplayed` take their own universes first, as
  `Category.{v}`: write `Displayed.{v₂, u₂} A` and `DoubleDisplayed.{v₃, u₃} B`, leaving those of
  the base to be inferred. Notation such as `⟶[f]`, `≫ᵈ`, `𝟙ᵈ` is used through
  `open scoped Displayed` (or `DoubleDisplayed`).
- No `sorry`, no new axioms, no `noncomputable`. Factorizations are data (as in `IsOpcartesian`)
  rather than `∃!` so that constructions from them compute and reduce.
- Law fields that usually hold definitionally (the laws of displayed categories and functors, of
  split (op)fibrations and D2SFibs, of (op)cartesian functors and maps of D2SFibs, …) default to
  `by intros; rfl`: omit them in instances. In a literal nested in another structure the default
  can be much slower than the term `rfl` (the `LaxTrans` literals of `unitIso` in
  `Opfibration/Straightening/Equivalence.lean` time out), and there the proof is given.
- `set_option maxHeartbeats` is a last resort. The two uses in `D2SFib/Straightening` have a
  comment on why the computation is long. Prefer the kernel tactics below.
- Commit messages name the mathematical content ("Opposite types: HasOp with (Aᵒᵖ)ᵒᵖ = A and
  stability as rules; the category model has them"), with a wrapped body if more is needed.

## Categories of (op)fibrations

The categories displayed over `Cat` of indexed categories and of (op)fibrations are named
`⟨objects⟩⟨morphisms⟩`:

- Objects: on the fibred side, `SplitOpfib`, `SplitFib`, `Opfib`, `Fib` after the class of the
  displayed categories (split or only cloven). On the indexed side, `I⟨target⟩`: `ICat` (functors
  `A ⥤ Cat`), `ICatOp` (contravariant ones, `Aᵒᵖ ⥤ Cat`; `Op` is not the pointwise opposite
  `F ⋙ opFunctor'`), `IDisc` (functors into discrete categories) and `IProf` (lax normal functors
  into profunctors).
- Morphisms: the fibred side defines the suffix, `Lax` (any displayed functor), `Ps` (displayed
  functors preserving (op)cartesian morphisms) or `Str` (displayed functors sending chosen lifts
  to chosen lifts, `OpcartesianFunctor` and `CartesianFunctor`). The indexed side takes the suffix
  of the fibred side it straightens to, so the two sides of a straightening theorem have the same
  suffix, as in `straighteningEquivLax : VertEquivalence ICatLax SplitOpfibLax`. On `ICat` these
  are the lax, pseudonatural and strict transformations. On `ICatOp`, `Lax` follows `SplitFibLax`:
  its transformations are the oplax ones of `[Aᵒᵖ, Cat]` (Mathlib's `Oplax.OplaxTrans`).

A morphism suffix appears exactly when there is a choice of morphisms. `DisplayedCat`, `IProf`,
`DiscOpfibCat` and `IDisc` have one class of morphisms and no suffix: their objects have no chosen
lifts, or all functors between them preserve them. Such a name ends in `Cat` when the bare name is,
or would read as, the class or structure of its objects: `Displayed` is a structure, and
`DiscOpfib` would read as a class like `SplitOpfib` (the objects are the structure `DiscOpfibOb`,
as those of `SplitOpfibLax` are `SplitOpfibOb`). `D2SFibCat B`, the category of D2SFibs over `B`
(the fiber of `D2SFibStr`), ends in `Cat` too, since `D2SFib` is a class.

The straightenings:

| Indexed     | Fibred          | Morphisms              |
| ----------- | --------------- | ---------------------- |
| `IProf`     | `DisplayedCat`  | only one class         |
| `ICatLax`   | `SplitOpfibLax` | any displayed functor  |
| `ICatStr`   | `SplitOpfibStr` | chosen lifts preserved |
| `ICatOpLax` | `SplitFibLax`   | any displayed functor  |
| `IDisc`     | `DiscOpfibCat`  | only one class         |
| `DProf`     | `D2SFibStr`     | chosen lifts preserved |

`DProf` (dependent profunctors) and `D2SFibStr` are doubly displayed, over `ICatStr` and
`SplitOpfibStr` respectively.

Construct the functors of an equivalence both ways, with an explicit unit and counit, rather than
through `VertEquivalence.ofFullyFaithful`, so that its inverse is the expected construction and
compares with others by `rfl`, as the strict straightening with the lax one
(`straightenStr_comp_forget`).

These categories are displayed over `Cat.{v₁, u₁}`, with fibers in other universes, `Cat.{v₂, u₂}`
or `Displayed.{v₂, u₂}`. Their universe parameters are those of the fibers, then those of the
base, as for `Displayed`: `ICatLax.{v₂, u₂, v₁, u₁}`, an order that comes from declaring
`universe v₂ u₂ v₁ u₁` in their files. The fiber universes only occur in a `max` in the levels of
these categories (hence `set_option linter.checkUnivs false` on them) and are never inferred, so
statements give all four, or the first two when an argument fixes the base
(`ICatLax.{u, u}.Ty Γ`). Categories doubly displayed over them put their own universes before
these: `DProf.{v₃, u₃, v₂, u₂, v₁, u₁}` over `ICatStr.{v₂, u₂, v₁, u₁}`, and `D2SFibCat.{v₃, u₃} B`
as `DoubleDisplayed.{v₃, u₃} B`. `IProf.{u, v₁, u₁}` has one fiber universe, since
profunctors are between small categories. `DisplayedCat.{v, u, v, u} ≃ cod Cat.{v, u}` needs the
total categories in the base, as do the comprehension models, which use these categories at
`u, u, u, u`.

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
  counit in `D2SFib/Straightening/Equivalence.lean`.
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
- The kernel too compares the arguments of two applications with the same head before unfolding
  them. `F.map g = G.map g'`, for functors `F` and `G` on different categories that are equal on
  `g`, can take seconds, while each side compared with its value is immediate: prove it as
  `(rfl : _ = value).trans rfl`.
- Rules on Mathlib's lemmas are declared only in `shrewlib/Rules/`, and each file imports only those
  it needs, so its imports show which foreign rules it sees.
