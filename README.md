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

**Writing rules.** Some consequences of the above, learned in `src/`:

- A rule on a definition `f` makes `f xs` stop being recognizably equal to its unfolding when the
  rule applies. Facts about the unfolding are best proved before the rule is declared, for example
  as `HEq`s that `eq_of_heq` turns into equations afterwards.
- A definition that the rules rewrite back into itself when unfolded, such as `pushMap` in
  `Displayed/Fibration/Opfib.lean`, must be an `irreducible_def`, or unfolding it loops.
- Nested subpatterns should use the most unfolded form of a term, since targets are unfolded
  towards the pattern and not the other way; heads need a rule for each form.
- Index-like arguments should be implicit, so that they are checked by definitional equality.
- A rule on `Functor.obj` or `Functor.map` is tried on every functor application. Rules keyed on
  dedicated constants are cheaper.
- A failed match costs a full unfolding search for the subpattern head. Two sets of rules keyed on
  the same head whose subpatterns never occur in each other's terms (as for displayed composition
  in `Displayed/Functor.lean` and `Displayed/Fibration/`) should not be imported together where
  there is much computation: `Displayed/Fibration/Transfer.lean` is the only file importing both.
- Rules on Mathlib's lemmas are declared only in `src/Rules/`, and each file imports only those it
  needs, so its imports show which foreign rules it sees.

## Files

The development is one library with sources in `src/`. Module names and namespaces follow the
folders. Displayed and doubly displayed categories are developed in parallel: each has `Basic`,
`Total`, `Cartesian` and `Functor` files, a folder of fibrations (`Displayed/Fibration`,
`DoubleDisplayed/D2SFib`) and a `Straightening` folder.

- `Rules/`: the category laws, the functor laws, and the laws of locally discrete bicategories and
  strictly unitary lax functors, as rules.
- `Examples/FunctorId.lean`: `F.map (𝟙 a) x = x` by `rfl` for any functor `F : A ⥤ Type`, after
  making Mathlib's `Functor.map_id` a rule.
- `Profunctor.lean`: profunctors as a structure with actions `lmap`/`rmap`; composition as a
  coend quotient; the bicategory `ProfCat`. The action laws and the naturality of 2-cells are
  rules, so most coherence laws hold by `rfl`.
- `DoubleCategory.lean`: pseudo double categories, following *Univalent Double Categories*
  (van der Weide, Rasekh, Ahrens, North) without univalence: a two-sided displayed category of
  horizontal morphisms and squares, horizontal identities and composition, and invertible,
  natural unitors and associator subject to the triangle and pentagon laws. With the category laws
  as rules, the displayed laws are stated without transport. The horizontal bicategory of
  globular squares is constructed as an application.
- `Displayed/`: categories displayed over a category, whose laws are rules and hold as plain
  equations. `Basic` (with fibers), `Total` (the total category, `π`, `ι`), `Cartesian`
  ((op)cartesian morphisms), `Functor` (`VertFunctor`, `VertNatIso`, `VertEquivalence`: functors
  and equivalences over the base, which are fully faithful, preserve (op)cartesian morphisms and
  induce equivalences of total categories).
  - `Fibration/`: cloven (op)fibrations as mirror images, `Opfib.lean` and `Fib.lean`, with chosen
    `push f x`/`olift` and `pull f y`/`clift`, the (op)cartesian factorization, the transport
    `pushMap`/`pullMap` and its functors, and split versions. `PreSplitOpfib` (`PreSplitFib`) adds
    the splitting axioms on objects, which are rules; `SplitOpfib` (`SplitFib`) holds it as an
    instance field rather than a parent, since the fields of a parent are local variables while a
    class is elaborated and the rules would not apply to the axioms on lifts. `DualOp.lean` is the
    dual opfibration of a split opfibration, which computes; `Transfer.lean` transfers cleavages
    along equivalences.
  - `Straightening/`: Proposition 9 of the notes. `DCat` (lax normal functors
    `LocallyDiscrete A ⥤ᴸ ProfCat`, with lax transformations with representable components as
    morphisms, on elements via `LaxNormal.lean`) and `Arr` (`Cat^→`, by the codomain) are displayed
    over `Cat`. `unstraighten` (`(▷ᵈ)*`, through the category `Unstraightening F` over `A`, built
    without `eqToHom` or `cast`) and `straighten` (fibres `{e // p e = a}`) form a
    `VertEquivalence DCat Arr`, `straighteningEquiv`. `DCat` is a `SplitFib` by strict pullback,
    with the splitting laws by `rfl`; `Cat^→` gets a `Fib` instance by transfer, and both functors
    preserve cartesian morphisms. Only the inverses of the unit and counit transport along
    equations `p e = a`.
- `DoubleDisplayed/`: categories doubly displayed over a displayed category `B`, with `Basic`,
  `Total` (`C.total : Displayed A`), `Cartesian` and `Functor` (`VertFunctor` over `B`).
  - `D2SFib/`: dependent 2-sided split fibrations over a split opfibration `B` (`Basic`) and their
    category (`Category`).
  - `D2SFib/Straightening/`: `straighten` (`Ψ`) and `unstraighten` (`Φ`, the dependent 2-sided
    Grothendieck construction), with `straighteningEquiv` between functors `∫(Bᵈᵒ) ⥤ Cat` and
    D2SFibs over `B`. The laws of D2SFibs are rules, so the Grothendieck construction, its `D2SFib`
    structure and much of the unit and counit hold by `rfl`. This is a rewrite of a development on
    Lean and Mathlib `v4.30.0-rc2` whose laws were stated with `castHom`, `eqToHom` and `HEq`
    (commit `4b55ea2` of this repository), at about half its size.
- `docs/nfib/`: the notes (`main.tex`) referred to in docstrings, and the plan and list of
  deviations of the original development.
- `mathlib4/`: Mathlib master, pinned to `v4.35.0-rc2`, used as a path dependency.

## Building

```sh
lake build   # only compiles the Mathlib modules these files import
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1` for any `lake update`. Otherwise Mathlib's hook tries to
fetch its cache, which doesn't apply to the patched compiler. After rebuilding the toolchain with
a new commit, Lake will recompile the imported Mathlib modules.
