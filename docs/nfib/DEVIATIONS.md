# Deviations from `PLAN.md`

This file records places where the implementation departs from the literal shape given in
`PLAN.md`, as permitted by §11 ("If a *statement shape* given in this plan does not elaborate as
written … you are free to adjust the shape … Note any such deviation in a `DEVIATIONS.md`.").
The load-bearing invariants (the prose next to each definition and the dictionary of §1) are
preserved.

## M1 — `Nfib/Displayed/Basic.lean`

### D1. Universes are inferred, not written as `Displayed.{v₂, u₂}`
`Displayed A` has **four** universe parameters — the base category contributes `u₁` (objects) and
`v₁` (homs), and the fields contribute `u₂` (`Ob : A → Type u₂`) and `v₂` (`Hom : … → Type v₂`).
So the two-argument application `Displayed.{v₂, u₂} A` from the plan does not elaborate. We simply
write `Displayed A` and let universe inference determine everything; `Ob` still lands in `Type u₂`
and `Hom` in `Type v₂` as intended. The M6 universe pinning against `Cat.{v₃, u₃}` is unaffected
(it is driven by the doubly-displayed fibers, not by `Displayed`'s own universe application).

### D2. Total-category morphisms use a `Total.Hom` structure, not a raw `Σ`
The plan writes `Hom x y := Σ f : x.1 ⟶ y.1, D.Hom f x.2 y.2`. With a raw `Sigma`, the anonymous
projections `.1`/`.2` do **not** unfold through `Quiver.Hom` (i.e. through the `⟶` notation), so
`F.1` on an `F : x ⟶ y` fails to elaborate. We instead use a dedicated

```lean
structure Total.Hom {D : Displayed A} (x y : D.Total) where
  base  : x.1 ⟶ y.1
  fiber : D.Hom base x.2 y.2
```

exactly as mathlib's `CategoryTheory.Grothendieck.Hom` does. Named projections `F.base`/`F.fiber`
**do** resolve through `⟶`, and the anonymous constructor `⟨α, β⟩` still builds morphisms, so the
dictionary's `totalOlift α b := ⟨α, olift α b⟩`, `dualHoriz α b := ⟨α, 𝟙 _⟩`, etc. continue to work.
Downstream code uses `.base`/`.fiber` in place of the plan's `.1`/`.2` on total morphisms.

### D3. `≍` notation for `HEq`
All `HEq a b` **statements** are written with the infix notation `a ≍ b` (see the amendment to
§2.1 of `PLAN.md`). This is purely cosmetic — `≍` is notation for `HEq` — but keeps the cast-heavy
coherence statements readable. `HEq.rfl` and other `HEq.*` term-level lemmas are still referenced by
name.

## M2 — `Cartesian.lean`, `SplitOpfib.lean`, `DualOp.lean`

### D4. `Fiber.comp_def`/`Fiber.id_def` are **not** `@[simp]`
The plan (§3) suggests `@[simp]` unfolding lemmas for the fiber category. In practice, making
`Fiber.comp_def` (`φ ≫ ψ = castHom … (φ ≫ᵈ ψ)`) a global `@[simp]` lemma unfolds every fiber
composition into `castHom`, which is exactly the vocabulary §2.1(3) says to *avoid* — it defeats
the `eqToHom` simp arsenal that closes the `dualOp` coherence axioms. Likewise `Fiber.id_def`
(`𝟙 x = D.id x`) as `@[simp]` rewrites `𝟙` to `D.id` and thereby blocks the category's own
`Category.id_comp`/`comp_id` simp lemmas. Both lemmas are kept (with the same statements) but
**without** `@[simp]`; apply them explicitly (`simp only [Fiber.comp_def]`) on the rare occasions
the displayed composite is wanted.

### D5. `dualOp.Hom` uses `B.Hom (𝟙 a')` rather than the fiber `⟶`
The plan writes `Hom f x y := (y ⟶ B.transp f x : B.Fiber a')`. Because the structure field's `y`
has type `B.Ob a'` (not `B.Fiber a'`), and `Fiber` is a `def` that δ-reduces to `Ob` during
instance search, the `⟶` fails to synthesize `Quiver (B.Fiber a')`. We instead write the
definitionally-equal `Hom f x y := B.Hom (𝟙 a') y (B.transp f x)`, which needs no `Quiver`
instance. Fiber-category operations (`≫`, `eqToHom`, `transpMap`) still apply to these homs by
defeq, so the `dualOp` composition formula is unchanged.

## M3/M4 — `Double.lean`, `Sigma.lean`

### D7. `sigma`'s morphisms use a `Sigma.Hom` structure, not a raw `Σ`
As with the total category (D2), `C.sigma`'s hom-type is a named structure `Sigma.Hom C f x y`
(fields `base : B.Hom f x.1 y.1`, `fiber : C.Hom base x.2 y.2`) rather than the plan's raw
`Σ g, C.Hom g x.2 y.2`, because anonymous `Σ`-projections do not resolve through `⟶`. Same rationale
and consequences as D2. The `sigma` coherence laws are proved with a heterogeneous ext lemma
`Sigma.Hom.hext` (the `.base` component is itself `≍`, since `sigma` is a `Displayed` category whose
coherences lie over base-morphism equalities).

### D8. `Fiber.comp_def`/`Fiber.id_def` at the double level are not `@[simp]`
Mirroring D4, the `DoubleDisplayed.Fiber` unfolding lemmas are kept without `@[simp]`, for the same
reason (keep proofs in `eqToHom`/fiber-category vocabulary rather than `castHom`).

### D9. `VertFunctor.ext` is a plain lemma (not tagged `@[ext]`)
`VertFunctor.ext` is provided with pointwise hypotheses (`obj` equality and `map` `≍`) but not
tagged `@[ext]`, because the implicit-argument-heavy hypothesis shape does not fit the `@[ext]`
attribute's expected form. It is applied explicitly where needed (M5's category laws).

## M5 — `D2SFib/Basic.lean`, `D2SFib/Category.lean`

### D10. `pushLift_pullLift` uses a `δ`-quantified form (no `▸`)
The interchange field is stated in the plan's recommended `▸`-free shape: it quantifies over an
arbitrary `δ ≍ pushLift α (pull β c)` of the `push_pull`-adjusted type and asserts the two ways
around the square are `≍`. This avoids motive problems and is exactly the "reshape freely as long
as it says the two ways around the square are heterogeneously equal" allowance of §6.1.

### D11. `push`/`pull` functor laws stated with `castHom`, and the fiber `⟶`/`𝟙` issue
`pushMap`/`pullMap` return `C.Hom (B.id …) …` (not the fiber `⟶`, which cannot synthesize its
`Category` on `C.Ob`-typed objects, cf. D2/D5). Consequently `pushMap_comp`/`pullMap_comp` are
stated with the fiber composite unfolded to `C.castHom (…) (pushMap … ≫ᵈᵈ pushMap …)` rather than
`pushMap … ≫ pushMap …`, and `pushMap_id` with `C.id` rather than `𝟙`. The functors
`pushFunctor`/`pullFunctor` then wire these through `Fiber.comp_def`/`Fiber.id_def`.

### D12. `pushMap_pullMap` and `d2sHomEquiv` deferred to M7/M9
§6.2's morphism-interchange lemma `pushMap_pullMap` and the two-step hom-equivalence `d2sHomEquiv`
are *not* yet provided. `d2sHomEquiv` is explicitly the tool that "powers the whole of M9's counit
isomorphism" and `pushMap_pullMap` is the paper's `d2sfib:lemma` consumed by M7's `map_comp`. Both
depend on the heavy `pushLift_pullLift` interchange and are most naturally built where consumed;
they are deferred to M7/M9 and will be added there. Everything else in §6.2 (the `push`/`pull`
functors and their laws) and all of §6.1/§6.3 (the class, `D2SFibHom`, `D2SFibCat` and its
`Category` instance) compile sorry-free, so M6's statement can proceed.

### D13. `D2SFibCat` field carries an explicit universe annotation
`D2SFibCat`'s field is written `C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B`; without the
explicit universes Lean cannot infer `v₃ u₃` (they appear only inside `DoubleDisplayed`'s fields).
This realizes the plan's `D2SFibCat.{v₃, u₃}`.

### D14. `sigma_opcartesian` sanity lemma not included
The optional `sigma_opcartesian` validation lemma (§6.1, explicitly "a sanity check, not a
dependency", permitted to be left out) is omitted.

## M2 (addendum)

### D6. `factorTotal`, `dual_factor`, `dualHoriz_comp_dualVert_swap` deferred to M8
The plan (§4.2/§4.3) marks `factorTotal`, `dual_factor`, and `dualHoriz_comp_dualVert_swap` as
"off the critical path" / "helpers for later files", and notes the swap lemma needs a
direction-check against `dual_factor` when proving (its statement as written in the plan does not
typecheck). Their precise typed form depends on how M8 (`D2SGC`) consumes them. To keep the M2 gate
clean (build passes, zero `sorry`), these three are **deferred to M8**, where they will be added in
the exact shape M8 needs. `dualOp`, `dualHoriz`, `dualVert` and their `base`/`π` simp lemmas — the
data the rest of the pipeline needs — are all present and compile.

## M8 — `Nfib/D2SFib/Grothendieck.lean` (and the M2 items it unblocks)

### D15. Typed constructors for the total category (`tot`, `totalMk`, `totalVert`)
`Displayed.Total` is a `def`, so `(⟨a, x⟩ : D.Total)` elaborates at the unfolded `Σ`-type and the
resulting term no longer carries the `Category D.Total` instance: `⟶`, `≫`, `𝟙` and `@[reassoc]`
all fail on it. `Nfib/Displayed/Basic.lean` therefore gains

* `Displayed.tot D x : D.Total` (objects),
* `Displayed.totalMk D f φ : D.tot x ⟶ D.tot y` (morphisms from base + displayed components),
* `Displayed.totalVert D β : D.tot x ⟶ D.tot y` (the vertical ones), with `totalVert_comp` etc.

`totalOlift`, `dualHoriz` and `dualVert` are restated with these, so their types are syntactically
`_ ⟶ _`. `Displayed.ι` is defined via `totalVert` (its old `⟨𝟙 a, β⟩` body would reintroduce the
same mismatch, this time as `(D.ι a).obj x` vs `D.tot x` under `instances` transparency, which
silently blocks `rw`).

### D16. The total-category bridge replaces `heq_comp` chains
`Displayed.heq_of_totalHom_eq` turns a `≍` of displayed morphisms with common endpoints into an
`Eq` in the honest category `D.Total`. With it, the deferred §4.2 lemmas (`factorTotal`,
`totalOlift_id`, `totalOlift_comp`, `totalVert_comp_totalOlift`, `factor_eq_of_totalEq`, and hence
`factor_vert`, `factor_id`, `factor_comp`) are ordinary `Category` calculations rather than
hand-written `heq_comp` chains. The plan's `factorTotal` is kept (it is load-bearing after all).

### D17. `dualHoriz_comp_dualVert_swap` renamed and direction-corrected
The plan's statement `dualVert (B.transpMap α β) ≫ dualHoriz α b = dualHoriz α b' ≫ dualVert β`
does not typecheck. The correct interchange, provided as `dualVert_comp_dualHoriz`, is

```lean
dualVert β ≫ dualHoriz α b = dualHoriz α b' ≫ dualVert (B.transpMap α β)
```

for `β : b ⟶ b'` in `B.Fiber a`. `DualOp.lean` also gains `dualOp_hom_ext`, `dualVert_id/comp/
eqToHom`, `dualHoriz_heq`, `dualHoriz_id` and `dualHoriz_comp` (splitness of `∫(Bᵈᵒ)`), all of
which M8 consumes.

### D18. `dualHoriz`/`dualVert` are `noncomputable`
Because they are now built with `totalMk` (an explicit `Displayed`-argument `def`), `B.dualOp`
occurs in their *values*, not just their types, so they inherit `dualOp`'s `noncomputable`. The
whole of `D2SGC` is consequently `noncomputable` as well; §2's wish that "`D2SGC` and its lifts
should stay computable" is unachievable given that `dualOp` is noncomputable (it depends on
`transpMap`, which is defined by a universal property).

### D19. `D2SGC` is organized through an auxiliary two-sided hom `GHom`
Rather than writing the three `eqToHom`s of §9.1 inline, every hom-type of `D2SGC F` is presented
as `D2SGC.GHom F u v c c' := (F.map u).obj c ⟶ (F.map v).obj c'` for a *pair* of
`∫(Bᵈᵒ)`-morphisms with common codomain, with three operations — `ofEq`, `reindex`, `push`,
`trans` — and their `≍`-algebra. The plan's `F_obj_congr`/`F_map_conj` reindexing lemmas appear as
`fmap_congr_obj` / `Functor.congr_hom` uses inside that algebra. `assoc` then follows the plan's
fallback strategy exactly: the five identities of `∫(Bᵈᵒ)` (`horizComp`/`vertComp`/`assocCmp`) are
proved first by `dualOp_hom_ext` + `simp`, and `assoc` reduces to them via a `tripleNF` normal
form. The associativity comparison is presented as `assocCmp` (a `dualVert`) rather than a raw
`eqToHom`, since `simp` cannot compute with `eqToHom` in `∫(Bᵈᵒ)` but does compute with the
`dualHoriz`/`dualVert` calculus; `assocCmp_eq_eqToHom` converts when needed.

### D20. The two `∃!` fields go through `existsUnique_of_heq_id`
Composition with `pullLift` (resp. `pushLift`) is *heterogeneously* the identity, because the
relevant comparison morphism is an `eqToHom`. The `∃!` is then obtained from
`existsUnique_of_heq_id` plus a `GHom.type_eq` identification of the two hom-types, rather than
from an explicitly constructed inverse.

### D21. M8 is complete; only `d2sfibEquivalence` (M9) remains `sorry`
`D2SGC`, `D2SGC.instD2SFib`, `D2SGCFib`, `D2SGCMap` and `D2SGCFunctor` are all sorry-free.

## M9 — `Nfib/D2SFib/Basic.lean` (partial)

### D22. D12 discharged: `d2sHomEquiv` now exists
The two items D12 deferred are both delivered: `pushMap_pullMap` in M5 (`D2SFib/Basic.lean`,
section `Interchange`) and `d2sHomEquiv` here, together with `pushDescEquiv`, `pullLiftEquiv`,
`olift_factor_heq`, `DoubleDisplayed.castHomEquiv` and the interface lemmas
`d2sHomEquiv_symm_apply`, `d2sHomEquiv_symm_apply_heq`, `d2sHomEquiv_heq` and
`d2sHomEquiv_eq_of_heq` (the uniqueness form that §10 wants for the counit's `map_comp`).

### D23. M9 is not finished
Still `sorry`: `d2sfibEquivalence` alone.

**Done so far.** `d2sHomEquiv` and its interface (D22), and — for the unit — the fiber calculus of
`D2SGC F` in `Grothendieck.lean`, section `Fiber`:

* `GHom.trans_heq'`: congruence for `trans` across a change of ambient fiber;
* `fiber_comp_eq`: composition in `(D2SGC F).Fiber b` is a `GHom.trans` along `dualHoriz_id_eq`,
  i.e. ordinary composition in `F.obj ⟨a, B.transp (𝟙 a) b⟩` once the two (equal) indexing
  morphisms are identified;
* `totIdOb`, `dualHoriz_id_eqToHom`: `dualHoriz (𝟙 a) b` *is* an `eqToHom` of `∫(Bᵈᵒ)`;
* `unitFiberFunctor` / `unitFiberInv`, the two directions of the unit's component, both the
  identity on objects; `unitFiber_comp` / `unitFiber_inv_comp`, their two *strict* round trips
  (`Cat`-isos are strict, so these are genuine `Functor.ext` equalities);
* `unitFiberIso b : F.obj ⟨a,b⟩ ≅ Cat.of ((D2SGC F).Fiber b)` in `Cat`.

**What remains.** The route changed: rather than building the counit isomorphism directly, `Ψ`
(`toFunctor`) is shown to be an equivalence via full + faithful + essentially surjective, and
`d2sfibEquivalence` will be `toFunctor.asEquivalence.symm`. Essential surjectivity is free from the
unit, and faithfulness is `D2SFibHom.map_heq_lifts`; both are done. **`Ψ.Full` is the only thing
left**, and with it `d2sfibEquivalence`.

For `Ψ.Full`: given `η : toFunctorObj C ⟶ toFunctorObj C'`, write `G b` for
`(η.app (B.dualOp.tot b)).toFunctor : C.Fiber b ⥤ C'.Fiber b`. Instantiating `η`'s naturality at
`dualHoriz α b` and at `dualVert β`, and using `pullFunctor_id` (`pullFunctor (B.id b) = 𝟭`, proved)
together with `pushFunctor (𝟙 a) b ⋙ pullFunctor (eqToHom (B.transp_id b).symm) = 𝟭`, gives

* `pushFunctor α b ⋙ G (B.transp α b) = G b ⋙ pushFunctor α b`  →  `obj_push`;
* `pullFunctor β ⋙ G b = G b' ⋙ pullFunctor β`  →  `obj_pull`.

Then `Φ.obj := (G _).obj` and `Φ.map θ := (d2sHomEquiv ..).symm` of the `G`-image of
`d2sHomEquiv θ` (transported along those two identities). The remaining fields:

* `map_pushLift` / `map_pullLift`: need `d2sHomEquiv` evaluated at the two chosen lifts (each is
  heterogeneously an identity, since `B.factor (B.olift α b) = 𝟙 _` and `pull_id`/`pullLift_id`);
* `map_id`: likewise;
* `map_comp`: **the one substantial piece still missing** — the compatibility of `d2sHomEquiv` with
  composition, i.e. the paper's pasted diagram. Concretely, a formula for
  `d2sHomEquiv (α ≫ α') (g ≫ᵈ g') (θ ≫ᵈᵈ θ')` in terms of `pushMap α' (d2sHomEquiv θ)` and
  `pullMap _ (d2sHomEquiv θ')`, obtained by chaining `d2sHomEquiv_heq` for `θ` and `θ'`,
  `pushLift_pullLift_square` (to swap the middle `pullLift ≫ᵈᵈ pushLift`), `pushLift_comp` and
  `pullLift_comp`, and concluding by `d2sHomEquiv_eq_of_heq`. Expect a proof of the size of
  `pushMap_pullMap` in `D2SFib/Basic.lean`.

### D24. The exact remaining statement

`Ψ.Full` needs one lemma, whose statement has been checked to elaborate (in
`D2SFib/Basic.lean`, section `HomEquiv`, with `variable {a a' : A}`):

```lean
/-- **The composition law for `d2sHomEquiv`** (the paper's pasted-square diagram). -/
theorem d2sHomEquiv_comp {a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : B.Hom α b b') (g' : B.Hom α' b' b'') (c : C.Ob b) (c' : C.Ob b')
    (c'' : C.Ob b'') (θ : C.Hom g c c') (θ' : C.Hom g' c' c'')
    (δ : C.Hom (B.id (B.transp α' (B.transp α b))) (push α' (pull (B.factor g) c'))
      (pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c'')))
    (hδ : δ ≍ pullMap (B.transpMap α' (B.factor g)) (d2sHomEquiv α' g' c' c'' θ'))
    (F : C.Hom (B.id (B.transp (α ≫ α') b)) (push (α ≫ α') c) (pull (B.factor (g ≫ᵈ g')) c''))
    (hF : F ≍ pushMap α' (d2sHomEquiv α g c c' θ) ≫ᵈᵈ δ) :
    d2sHomEquiv (α ≫ α') (g ≫ᵈ g') c c'' (θ ≫ᵈᵈ θ') = F
```

(The `δ`/`F` quantification is the `▸`-free style of `pushLift_pullLift`; `δ`'s source is matched by
`push_pull`, `F`'s by `push_comp` and `factor_comp`.)

Proof route: `refine (d2sHomEquiv_eq_of_heq _ _ (θ ≫ᵈᵈ θ') F ?_).symm`, then a chain from
`θ ≫ᵈᵈ θ'` using, in order, `d2sHomEquiv_heq` at both factors, `C.assoc` reassociations,
`pushLift_pullLift_square` (to swap the middle `pullLift (B.factor g) c' ≫ᵈᵈ pushLift α' c'`),
`pushLift_pushMap`, `pushLift_comp`, `pullMap_pullLift`, `pullLift_comp`, and finally `factor_comp`
to identify `B.transpMap α' (B.factor g) ≫ B.factor g'` with `B.factor (g ≫ᵈ g')`. All congruences
are `DoubleDisplayed.heq_comp'`.

**Recommendation for whoever picks this up.** Rather than writing that chain as raw `≍` steps, port
the M8 trick (D16) one level up: `heq_of_totalHom_eq` at the `C.sigma` level. A morphism
`θ : C.Hom g c c'` becomes `C.sigma.totalMk α ⟨g, θ⟩` in the honest category `C.sigma.Total`, where
reassociation is `Category.assoc` and the whole chain is a `rw`-sequence rather than nested
`heq_comp'`. That needs a bridge lemma (`Sigma.Hom` injectivity composed with
`Displayed.heq_of_totalHom_eq`) plus total-category restatements of `pushLift_comp`,
`pullLift_comp`, `pushLift_pushMap`, `pullMap_pullLift` and `pushLift_pullLift_square` — five short
lemmas that make the main computation mechanical, exactly as `factorTotal`/`totalOlift_comp` did for
`factor_comp`.

Once `d2sHomEquiv_comp` exists, `Ψ.Full` is: build `Φ` with `obj := (G _).obj` and
`map θ := (d2sHomEquiv ..).symm (G-image of d2sHomEquiv θ)`; `map_comp` then follows by applying
`d2sHomEquiv_comp` in `C` and in `C'` and using that `G` commutes with `pushMap`/`pullMap`
(the two functor identities extracted from `η`'s naturality). Then

```lean
noncomputable def d2sfibEquivalence (B : Displayed A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B :=
  (toFunctor.asEquivalence).symm
```

### D25. Concrete `sigma`-bridge skeleton for `d2sHomEquiv_comp`

Both directions of the bridge now exist (`totC`, `totC_comp`, `heq_of_totC_eq`, `totC_eq_of_heq`),
and the intended proof is the following, worked out but not yet written.

`d2sHomEquiv_eq_of_heq` reduces the goal to

```
pushLift (α ≫ α') c ≫ᵈᵈ (F ≫ᵈᵈ pullLift (B.factor (g ≫ᵈ g')) c'') ≍ θ ≫ᵈᵈ θ'
```

Apply `heq_of_totC_eq`; by `totC_comp` (a `@[simp]` `rfl`) both sides become single `totC`s of
`≫ᵈᵈ`-composites, so the goal is an equality of *composites of `totC`s* in the honest category
`(C.sigma).Total`, where all endpoints are the outer ones `⟨b, c⟩ ⟶ ⟨b'', c''⟩` and reassociation is
`Category.assoc`. The inputs, each obtained from an existing `≍` law by `totC_eq_of_heq`:

* (a) `totC g θ = totC _ (pushLift α c) ≫ totC _ f ≫ totC _ (pullLift (B.factor g) c')`
  from `(d2sHomEquiv_heq α g c c' θ).symm`, with `hα : α = α ≫ (𝟙 a' ≫ 𝟙 a')` by `simp` and
  `hg : g ≍ B.olift α b ≫ᵈ (B.id _ ≫ᵈ B.factor g)` from `olift_factor_heq` plus
  `(B.id_comp (B.factor g)).symm`;
* (b) the same for `θ'`;
* (c) `totC _ (pullLift (B.factor g) c') ≫ totC _ (pushLift α' c')`
  `= totC _ (pushLift α' (pull (B.factor g) c')) ≫ eqToHom h ≫ totC _ (pullLift (B.transpMap α' (B.factor g)) (push α' c'))`
  from `pushLift_pullLift_square`, where `h` is `congrArg` of `push_pull α' (B.factor g) c'` into
  `(C.sigma).Ob a''` (the two middle objects are `⟨B.transp α' (B.transp α b), push α' (pull β c')⟩`
  and `⟨…, pull (B.transpMap α' β) (push α' c')⟩`, equal since `push_pull` is an `Eq`);
* (d) `totC _ f ≫ totC _ (pushLift α' (pull (B.factor g) c')) = totC _ (pushLift α' (push α c)) ≫ totC _ (pushMap α' f)` from `pushLift_pushMap`;
* (e) `totC _ (pushLift α c) ≫ totC _ (pushLift α' (push α c)) = totC _ (pushLift (α ≫ α') c) ≫ eqToHom _` from `pushLift_comp` (plus `push_comp`, a `≍` of objects, for the object equality — cf. `totalOlift_comp` in `SplitOpfib.lean`, which is the exact analogue one level down);
* (f) `totC _ (pullLift (B.transpMap α' β) (push α' c')) ≫ totC _ f' = totC _ (pullMap (B.transpMap α' β) f') ≫ totC _ (pullLift (B.transpMap α' β) (pull (B.factor g') c''))` from `pullMap_pullLift`;
* (g) `totC _ (pullLift (B.transpMap α' β) (pull (B.factor g') c'')) ≫ totC _ (pullLift (B.factor g') c'') = eqToHom _ ≫ totC _ (pullLift (B.factor (g ≫ᵈ g')) c'')` from `pullLift_comp` and `factor_comp`.

Chaining (a)–(g) with `Category.assoc` gives the required equality. The `eqToHom`s introduced in
(c), (e), (g) are all in `(C.sigma).Total` and cancel against each other; if `simp` will not compute
with them, present them as `(C.sigma).totalVert (eqToHom …)` — the same trick `assocCmp` uses in
`Grothendieck.lean` (D19).


## M9 (completion)

### D26. `d2sHomEquiv_comp` is stated in "hypothesis style", with a `≍` companion

`Nfib/D2SFib/Basic.lean` proves the paper's pasted-square law as

```lean
theorem d2sHomEquiv_comp (α α') (g g') (θ θ')
    (X : C.Hom (B.id (B.transp (α ≫ α') b)) (push (α ≫ α') c) (pull (B.factor (g ≫ᵈ g')) c''))
    (hX : X ≍ (pushFunctor α' (B.transp α b)).map (d2sHomEquiv α g c c' θ)
        ≫ eqToHom (push_pull α' (B.factor g) c')
        ≫ (pullFunctor (B.transpMap α' (B.factor g))).map (d2sHomEquiv α' g' c' c'' θ')) :
    X = d2sHomEquiv (α ≫ α') (g ≫ᵈ g') c c'' (θ ≫ᵈᵈ θ')
```

The two sides live in *different* fibers (`B.transp (α ≫ α') b` vs `B.transp α' (B.transp α b)`),
so a homogeneous equation is impossible; the hypothesis style (as in `D2SFibHom.map_heq_lifts`)
avoids writing the transport. `d2sHomEquiv_comp_heq` is the derived `≍` form, obtained by feeding
`cast` of the composite along `hom_type_eq`.

The composite is written with `(pushFunctor _ _).map` / `(pullFunctor _).map` rather than
`pushMap` / `pullMap` because `pushMap α' f` has type `C.Hom (B.id _) _ _` and Lean will not
synthesise the fiber `Category` instance for `≫` from it; the functor form supplies the instance.
Inside the proof the statement is immediately restated with explicit `@CategoryStruct.comp` so that
the objects are syntactically `push …` / `pull …`, which is what the `push`/`pull` lemmas produce.

### D27. The proof of `d2sHomEquiv_comp` is a `slice_lhs` chain in `(C.sigma).Total`

Following the D25 skeleton. The bridge API of §"SigmaBridge" grew `sigmaTotEq`, `totC_vert_comp`,
`totC_vert_eqToHom`, `totC_heq_conj` (and later `totC_eq_eqToHom`, `totC_id`, `heq_of_totC_conj`).
`heq_of_totC_eq` reduces the goal to an equality in the honest category; `totC_heq_conj` turns the
two "outer" `≍` laws (`pushLift_comp`, `pullLift_comp` + `factor_comp`) into `eqToHom`-conjugations
that cancel; the remaining six steps (a)–(g) are applied with `slice_lhs i j => rw [...]`.

### D28. `Φ` and `Ψ` are assembled with `Equivalence.mk`, as in the plan

The final assembly is PLAN §10's:

```lean
noncomputable def d2sfibEquivalence (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₃, u₃, v₂, u₂} B :=
  CategoryTheory.Equivalence.mk D2SGCFunctor toFunctor unitIso counitIso
```

with `d2sfibEquivalence_functor : … .functor = D2SGCFunctor` and
`d2sfibEquivalence_inverse : … .inverse = toFunctor`, both `rfl`, so the theorem really exhibits
`Φ` and `Ψ` as the mutually inverse pair. `Equivalence.mk` must be written
`CategoryTheory.Equivalence.mk`: unqualified, `Equivalence.mk` resolves to core Lean's
relation-`Equivalence` constructor.

### D29. The universe *order* of `D2SFibCat` in the main statement

`D2SFibCat` has universe parameters in the order `{v₁, u₁, v₃, u₃, v₂, u₂}` (base hom/obj, then the
doubly-displayed hom/obj, then the displayed hom/obj), not the order `{v₁, u₁, v₂, u₂, v₃, u₃}`
written in PLAN §7. The main theorem is therefore stated as

```lean
noncomputable def d2sfibEquivalence (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₃, u₃, v₂, u₂} B
```

which is the pinning the plan intended: the fibers `E.C.Fiber b` are objects of `Cat.{v₃, u₃}` and
`B` is a `Displayed.{v₂, u₂}`. (With the plan's literal ordering the fibers would have landed in
`Cat.{v₂, u₂}` and the statement would have been unprovable.)

## M9 (the counit)

### D30. History: an earlier full/faithful/ess-surj assembly was removed

`d2sfibEquivalence` was first proved by showing `Ψ` full, faithful and essentially surjective and
taking `(toFunctor (B := B)).asEquivalence.symm`, with fullness in a file `Nfib/D2SFib/Full.lean`.
That route was later replaced by the plan's/paper's assembly (D28) and its supporting file and
lemmas deleted, since the counit gives the equivalence directly. Removed along with it:
`Nfib/D2SFib/Full.lean`; the `Faithful`, `EssSurj` and `IsEquivalence` instances for `toFunctor`;
and the `D2SFib`-level lemmas that only served them (`d2sHomEquiv_comp_heq`, `d2sHomEquiv_vert_heq`,
`heq_of_totC_conj`, `fiber_eqToHom_heq`, `hom_type_eq`, `base_id_congr`, together with the older
already-dead `push_congr_obj`, `pullLift_congr`, `pushLift_congr`).

`D2SFibHom.map_heq_lifts` survives (it moved from `Equivalence.lean` to `Category.lean`) because
`D2SFibHom.d2sHomEquiv_map_heq`, used by the counit's naturality, is derived from it.

### D31. The counit, and why `map_comp` is one lemma

For `F = Ψ C` the two structural functors of `∫(Bᵈᵒ)` are computed on the nose:
`fmap F (dualHoriz α b) = pushFunctor α b` and `fmap F (dualVert β) = pullFunctor β`
(`toFunctorObj_map_dualHoriz` / `_dualVert`, now in `ToFunctor.lean`). Hence
`D2SGC.push F α c = push α c` (`gpush`) and `D2SGC.pull F β c = pull β c` (`gpull`), and a
morphism of `D2SGC F` over `g` is, after those two `eqToHom`s (`Counit.vert`), exactly a vertical
morphism `push α c ⟶ pull (B.factor g) c'` of `C` — the codomain of `d2sHomEquiv α g c c'`. So the
counit is

```lean
Counit.map θ := (d2sHomEquiv α g c c').symm (Counit.vert θ)
```

Its `map_comp` is the paper's pasted square and reduces to a *single* lemma,
`Counit.comp'_heq_vert`: `D2SGC.comp'` in `D2SGC (Ψ C)` is the very composite that appears on the
right of `d2sHomEquiv_comp`. That in turn is four small computations
(`fmap_horizComp_obj/_map`, `fmap_vertComp_obj/_map`) saying that `Ψ C` sends the comparison
morphisms `horizComp`/`vertComp` of `Grothendieck.lean` to `pushMap`/`pullMap` up to the `eqToHom`
of `transp_comp`. `map_id`, `map_pullLift`, `map_pushLift` fall out of `d2sHomEquiv_id`,
`d2sHomEquiv_pullLift`, `d2sHomEquiv_pushLift` (all three say "`d2sHomEquiv` of a chosen lift is an
`eqToHom`") together with `heq_of_d2sHomEquiv_heq`.

The inverse `Counit.invD2S` is `d2sHomEquiv` conjugated the other way; all of its fields are
derived from `homD2S`'s by `Counit.map_injective`, and the two round-trip identities of the
isomorphism are `Counit.map_invMap` / `Counit.invMap_map`.

Naturality in `E` (glossed as "immediate" in the paper) is `Counit.map_gmap`: both sides are
determined by their `d2sHomEquiv`, `D2SGC.gmap` is heterogeneously `Φ`'s fiber functor
(`gmap_heq_map`), and `d2sHomEquiv` commutes with a `D2SFibHom` by
`D2SFibHom.d2sHomEquiv_map_heq` (extracted from `map_heq_lifts`, which moved from
`Equivalence.lean` to `Category.lean`).

### D32. Where the shared helpers live

`fiberHom`, `fiber_comp_heq`, `fiber_eqToHom_heq'` are in `D2SFib/Basic.lean` and
`toFunctorObj_map_dualHoriz` / `toFunctorObj_map_dualVert` in `D2SFib/ToFunctor.lean`; `Counit.lean`
imports only `Grothendieck.lean` and `ToFunctor.lean`.
