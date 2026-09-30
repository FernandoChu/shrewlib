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

**Patterns.** The left-hand side must be `f p₁ … pₙ` with `f` a constant that is neither an
inductive type nor a constructor. Each `pᵢ` is one of:

- a variable of `xs`. A repeated variable is checked by definitional equality.
- a constant applied to patterns, `c q₁ … qₘ`. The target is unfolded one step at a time until
  `c` appears at its head, so the output of another rule or a β-redex can still match.
- any other term, for example a closed term or a lambda. It is checked by definitional equality
  after the other positions have bound its variables.

Implicit and instance arguments that don't match structurally are also checked by definitional
equality. They are determined by the explicit arguments only up to definitional equality: an index
`f ≫ g` in the type of an argument can appear as `𝟙 x` in the target, and the same instance can be
reached along different paths.

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
- `mathlib4/`: Mathlib master, pinned to `v4.35.0-rc2`, used as a path dependency.

## Building

```sh
lake build   # only compiles the Mathlib modules these files import
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1` for any `lake update`. Otherwise Mathlib's hook tries to
fetch its cache, which doesn't apply to the patched compiler. After rebuilding the toolchain with
a new commit, Lake will recompile the imported Mathlib modules.
