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
folders. Displayed and doubly displayed categories are developed in parallel: each has `Basic` and
`Total` files, (op)cartesian morphisms (in `Displayed/{Opfibration,Fibration}/Basic` and
`DoubleDisplayed/Cartesian`), fibrations (`Displayed/{Opfibration,Fibration}`,
`DoubleDisplayed/D2SFib`) and `Straightening` folders.

- `Rules/`: the category laws, the functor laws, the laws of locally discrete bicategories and
  strictly unitary lax functors, and the laws of pullback cones and chosen pullbacks, as rules.
- `Tactic/KernelTactic.lean`: `kernel_exact` and `kernel_rfl'`, which hand definitional
  equalities that the rules reduce in many steps to the kernel, faster than the elaborator.
- `Examples/FunctorId.lean`: `F.map (𝟙 a) x = x` by `rfl` for any functor `F : A ⥤ Type`, after
  making Mathlib's `Functor.map_id` a rule.
- `Profunctor.lean`: profunctors as a structure with actions `lmap`/`rmap`; composition as a
  coend quotient; the bicategory `ProfCat`. The action laws and the naturality of 2-cells are
  rules, so most coherence laws hold by `rfl`.
- `Bicategory/`: 2-categories, their limits and spans. `Basic` has `TwoCategory`, a bicategory
  with Mathlib's `Bicategory.Strict`, whose laws are rules: composition of 1-cells is
  right-associated without identities, unitors and associators are `Iso.refl`, and whiskering is
  functorial, unital and associative, so the coherence laws hold by `rfl`. (Rules can't be stated
  for `[Bicategory B] [Bicategory.Strict B]`, since the `Strict` instance would not occur in their
  left-hand sides.) It also has `kernel_rfl`, which checks `rfl` in the kernel, after making the
  implicit arguments of whiskerings canonical and, if needed, going through weak head normal forms.
  - `Pullback`: 2-pullbacks `IsPullback`, Mathlib's limit pullback cones `IsLimit t` in the
    underlying category with the 2-dimensional universal property, and `HasPullbacks`, the same
    for Mathlib's chosen pullbacks. The equations of Mathlib's pullback cones and induced 1-cells
    are rules (`Rules/Pullback.lean`), so 2-cells over `t.fst ≫ f = t.snd ≫ g` need no transport;
    here they get their whiskered forms, and `pullback_ext` applies extensionality.
  - `Comma`: comma cones (Mathlib's `Comma (postcomp x f) (postcomp x g)`) and comma objects
    `IsComma s`: precomposing with `s` is an isomorphism of categories `(x ⟶ p) ≅ CommaCone f g x`.
    The induced 1-cells compute by rules. Comma objects are unique up to isomorphism of apexes,
    pasting a pullback on their left gives a comma object (`IsComma.pasteLeft`), and in the
    2-category `Cat`, `Comma L R` is a comma object, with the universal property by `rfl`.
  - `Arrow`: the arrow 2-category `Arr B`, whose 1-cells are commutative squares and whose 2-cells
    are pairs of 2-cells `(α, β)` with `α ▷ g = f ◁ β`. The equations of squares and of their
    2-cells are rules, so the latter needs no transport, and the laws hold by `rfl`.
  - `Factorization`: in a 2-category with comma objects, `f = Lf ≫ Rf` through `f/B`, the comma
    object of `f` and `𝟙 B`, as strict 2-functors `L R : Arr B ⥤ Arr B` (Mathlib's
    `StrictPseudofunctor`). Squares and their 2-cells act on `f/B` by the 1- and 2-dimensional
    universal property of comma objects, and the functor laws of these actions are rules, so the
    laws of `L` and `R` hold by `rfl` (checked by `kernel_rfl`).
  - `Monad`: strict 2-monads and 2-comonads on a 2-category, whose (co)unit and (co)multiplication
    are 2-natural; their 1-dimensional naturality is a rule, so the 2-dimensional one needs no
    transport. Their strict (co)algebras form 2-categories `Alg M` and `Coalg M`, whose laws hold
    by `rfl`. The laws of Mathlib's strict pseudofunctors are rules (`Rules/StrictPseudofunctor`).
  - `AlgebraicFactorization`: `R` is a 2-monad (`rMonad`, with unit `(Lf, 𝟙)` and multiplication
    `(π_f, 𝟙)`, composing the universal 2-cells of `f/B` and `Rf/B`) and `L` a 2-comonad
    (`lComonad`, with counit `(𝟙, Rf)` and comultiplication `(𝟙, σ_f)`, induced by a 2-cell from
    the 2-dimensional universal property of `f/B`). Their 2-categories of strict (co)algebras are
    `RAlg B` and `LCoalg B`. The laws are proved by extensionality into comma objects and
    `kernel_rfl`; a few equations about these 1- and 2-cells are proved first and made rules.
  - `Span`: spans in a 2-category. The spans between two objects form a 2-category
    (`Span.twoCategory`), whose laws hold by `rfl`.
  - `Spans`: the bicategory of spans `Spans B`, composed by Mathlib's chosen pullbacks, whose laws
    reduce by extensionality to `rfl`, checked in the kernel: the elaborator is much slower on
    these. Mathlib's `Span` and `SpanBicat` are not used: `SpanBicat` hides its projections and
    associator, and the matcher of rules does not see through the instances of Mathlib's category
    of spans, so their composites do not compute.
  - `FinitelyComplete`: finitely complete 2-categories (Mathlib's terminal object and pullbacks,
    with the 2-dimensional universal property, and comma objects), monads in a bicategory
    (`Bicategory.Monad`, as monoids in `a ⟶ a`, dually to Mathlib's comonads), and the arrow
    object `comma (𝟙 a) (𝟙 a)` as a monad in `Spans B`: an internal category. Its laws hold by the
    universal property of the comma object and `kernel_rfl`.
- `DoubleCategory/Basic.lean`: pseudo double categories, following *Univalent Double Categories*
  (van der Weide, Rasekh, Ahrens, North) without univalence: a two-sided displayed category of
  horizontal morphisms and squares, horizontal identities and composition, and invertible,
  natural unitors and associator subject to the triangle and pentagon laws. With the category laws
  as rules, the displayed laws are stated without transport. The horizontal bicategory of
  globular squares is constructed as an application.
- `Displayed/`: categories displayed over a category, whose laws are rules and hold as plain
  equations. Each of its three folders has a `Straightening/` subfolder.
  - `Displayed/`: displayed categories in general. `Basic` has fibers, vertical functors
    `VertFunctor` and vertical natural transformations `VertNatTrans`, which form a category as in
    Mathlib (vertical natural isomorphisms are its isomorphisms `F ≅ G`, with API in `VertNatIso`).
    `Equivalence` has equivalences over the base (`VertEquivalence`), which are fully faithful,
    and `Total`
    the total category, `π`, `ι`, and the induced functors, natural transformations and
    equivalences of total categories. `Codomain` has the codomain displayed category `cod C` (the
    arrow category of `C`, whose laws hold by `rfl`), whose cartesian morphisms are the pullback
    squares, so that it is a fibration if `C` has chosen pullbacks (Mathlib's `ChosenPullbacks C`,
    data rather than a `Prop`).
    - `Straightening/`: Proposition 9 of the notes. `DCat` (lax normal functors
      `LocallyDiscrete A ⥤ᴸ ProfCat`, with lax transformations with representable components as
      morphisms, on elements via `LaxNormal.lean`) and the codomain displayed category `cod Cat`
      (`Cat^→`) are displayed over `Cat`. `unstraighten` (`(▷ᵈ)*`, through the category
      `Unstraightening F` over `A`, built without `eqToHom` or `cast`) and `straighten` (fibres
      `{e // p e = a}`) form a `VertEquivalence DCat (cod Cat)`, `straighteningEquiv`. `DCat` is a
      `SplitFib` by strict pullback, with the splitting laws by `rfl`; `Cat^→` gets a `Fib`
      instance by transfer, and both functors preserve cartesian morphisms. Only the inverses of
      the unit and counit transport along equations `p e = a`.
  - `Opfibration/` and `Fibration/`: (op)cartesian morphisms, which vertical equivalences
    preserve, and cloven opfibrations and fibrations, as mirror images, each in its `Basic.lean`,
    with chosen `push f x`/`olift` and `pull f y`/`clift`, the (op)cartesian
    factorization, the transport `pushMap`/`pullMap` and its functors, and split versions.
    `PreSplitOpfib` (`PreSplitFib`) adds the splitting axioms on objects, which are rules;
    `SplitOpfib` (`SplitFib`) holds it as an instance field rather than a parent, since the fields
    of a parent are local variables while a class is elaborated and the rules would not apply to
    the axioms on lifts. `Opfibration/DualOp.lean` is the dual opfibration of a split opfibration,
    which computes. (Op)cleavages transfer along equivalences over the base.
    - `Opfibration/Straightening/`: functors `A ⥤ Cat` with lax transformations, as the split
      fibration `ICat = Cat ⋉⁻ [−, Cat]_lax` over `Cat` (`ICat.lean`), and their unstraightening
      `ICat ⟶ cod Cat` by Mathlib's Grothendieck construction `A ⋉ F` (`Unstraighten.lean`), which
      sends the chosen lifts to pullbacks and is fully faithful.
- `ComprehensionCategory/`: comprehension categories, the category model and its Σ-types. See
  `Readme.lean` in the folder.
- `DoubleDisplayed/`: categories doubly displayed over a displayed category `B`, with `Basic`,
  `Total` (`C.total : Displayed A`) and `Cartesian`; `Basic` includes `VertFunctor` over `B`.
  - `D2SFib/`: dependent 2-sided fibrations over a split opfibration `B` (`Basic`), as cloven
    (`D2SFib`), pre-split (`PreSplitD2SFib`, laws on objects as rules) and split (`SplitD2SFib`)
    classes, like `Displayed/Fibration`, and the category of split ones (`Category`).
  - `D2SFib/Straightening/`: `straighten` (`Ψ`) and `unstraighten` (`Φ`, through
    `Unstraightening F`, the dependent 2-sided Grothendieck construction), with `straighteningEquiv` between functors `∫(Bᵈᵒ) ⥤ Cat` and
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
