# PLAN: Displayed D2SFibs and the equivalence `Functor(∫(Bᵈᵒ), Cat) ≌ D2SFib(A, B)`

This plan formalizes, in Lean 4 + mathlib (pinned `v4.30.0-rc2`, already in the lakefile), a
displayed-category version of the main result of `main.tex` (Proposition `prop:d2sfibequiv`):

> **Main theorem.** Let `A` be a category and `B` a displayed category over `A` equipped with a
> split opfibration structure. Then the category of functors from the total category of the
> *dual opfibration* of `B` into `Cat` is equivalent to the category `D2SFib(A, B)` of dependent
> 2-sided fibrations over `B`.

This differs from the paper in that the paper works with a functor `B : A ⥤ Cat` and its
Grothendieck construction `A ⧐ B`; here `B` is instead a **displayed split opfibration over `A`**,
the total data of a D2SFib is a category **doubly displayed over `B`** (a genuinely two-level
curried structure `DoubleDisplayed B`, §5) instead of a functor into `A ⧐ B`, and the functor
category on the other side is indexed by `∫(Bᵈᵒ)` (total category of the fiberwise dual) instead
of `A ⧐ B^op`. All definitions from the paper must be adapted accordingly; the dictionary in §1
makes the translation precise. Everything is *split* (cloven with strictly functorial cleavages),
matching the paper's conventions.

**Deliverables, in order of priority:**

1. (M1–M5) All definitions compile sorry-free: displayed categories, opcartesian morphisms,
   `SplitOpfib`/`SplitFib`, fiber and total categories, dual opfibration, doubly displayed
   categories (`DoubleDisplayed B`, with their own casts, opcartesianness, fibers, vertical
   functors, and the sigma construction), the `D2SFib` class, and its bundled category
   `D2SFibCat B`.
2. (M6) The main theorem *statement* compiles (proof may temporarily be `sorry`).
3. (M7–M9) The full proof of the equivalence, sorry-free.

Do the milestones in order and run `lake build` as a gate after each one. Do not start a later
milestone with `sorry`s remaining in an earlier one, except that M6's single `sorry` (the
equivalence itself) is discharged across M7–M9.

---

## 1. Dictionary: paper ↔ this formalization

| Paper (`main.tex`) | Here |
|---|---|
| functor `B : A ⥤ Cat` | `B : Displayed A` with `[SplitOpfib B]` |
| `B(a)` (fiber category) | `B.Fiber a` (objects `B.Ob a`, homs `B.Hom (𝟙 a) b b'`) |
| `B(α) b` for `α : a ⟶ a'` | `B.transp α b` (chosen pushforward) |
| `B(α) β` for vertical `β` | `B.transpMap α β` (= `(B.transpFunctor α).map β`) |
| Grothendieck construction `A ⧐ B` | total category `B.Total` (notation `∫B` below, informally) |
| the opcartesian lift `(α, id)` in `A ⧐ B` | `B.totalOlift α b : (⟨a,b⟩ : B.Total) ⟶ ⟨a', B.transp α b⟩ := ⟨α, B.olift α b⟩` |
| `A ⧐ B^op` (fiberwise opposite) | `(B.dualOp).Total` where `dualOp : Displayed A` is the dual opfibration |
| category `C` with `q : C → A ⧐ B` | `C : DoubleDisplayed B` (§5) |
| `C(a, b)` | `C.Fiber b` (for `b : B.Ob a`) |
| D2SFib data (1)–(4) of Def. `def:d2sfib` | fields of `class D2SFib C`, for `C : DoubleDisplayed B` (§6) |
| cartesian lift `β* e` (local fibration) | `pull β c` and `pullLift β c` |
| opcartesian lift `α_! e` | `push α c` and `pushLift α c` |
| axiom (3): `q(α_!) = (α, id)` | built in: `pushLift α c` lies over `B.olift α b` *by its type* |
| axiom (4): `α_! β* e = (B(α)β)* α_! e`, canonical map is identity | fields `push_pull` (object equality) + `pushLift_pullLift` (the square of lifts commutes, as a `HEq`) |
| D2S cartesian functor | `D2SFibHom`: vertical functor over `B` preserving `pull`/`push` data strictly |
| category `D2SFib(A,B)` | `D2SFibCat B`: bundled `C` + `[D2SFib C]` instance (§6.3) |
| `Functor(A ⧐ B^op, Cat)` | `B.dualOp.Total ⥤ Cat.{v₃, u₃}` with its mathlib functor-category structure |
| `Ψ` | `D2SFib.toFunctor : D2SFibCat B ⥤ (B.dualOp.Total ⥤ Cat)` … (M7) |
| D2SGC `A ⧐ B ⧐^{2𝔣} C` and `Φ` | `D2SGC : (B.dualOp.Total ⥤ Cat) → DoubleDisplayed B` + its `D2SFib` instance … (M8) |
| Prop. `prop:d2sfibequiv` | `d2sfibEquivalence : (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat B` … (M9) |

Note a pleasant simplification vs. the paper: because a D2SFib's opfibration lifts are *typed*
over `B.olift α b`, the paper's axiom (3) is absorbed into the type of `pushLift` and needs
no separate field.

**Out of scope** (do not formalize): the non-split remark, D2SOpfibs and Corollary
`coro:d2sopfibequiv`, the 2SFib/opfib specialization remarks, Lemmas `lemma:sigma2opcomp` and the
`Σ`-type isomorphism lemmas, and the compact "fibration in Opfib(A)" characterization.

---

## 2. Global conventions

- **Project layout.** All code under `Nfib/`, root import file `Nfib.lean` updated to import every
  new module. Delete `Nfib/Basic.lean` (it's a stub) and remove its import.
- **Namespace.** Everything in `namespace Nfib`, with `open CategoryTheory` at the top of each
  file. Key types: `Nfib.Displayed`, `Nfib.SplitOpfib`, `Nfib.D2SFib`, etc.
- **Universes.** Use `universe v₁ u₁ v₂ u₂ v₃ u₃`. Base: `{A : Type u₁} [Category.{v₁} A]`.
  `Displayed.{v₂, u₂}` has `Ob : A → Type u₂` and hom-types in `Type v₂` (hom universe first,
  mathlib convention). `D2SFib` is a class on a `C : DoubleDisplayed.{v₃, u₃} B`; the main theorem uses
  `Cat.{v₃, u₃}` on the functor side so that fibers of `C` literally are objects of `Cat.{v₃,u₃}`.
- **`relaxedAutoImplicit` is off** in the lakefile: bind every variable explicitly.
- **The `mathlibStandardSet` linter is on**: every file needs a module docstring (`/-! ... -/`)
  and public declarations need doc comments. Write them as you go, not at the end.
- **`noncomputable` policy.** Anything built from a universal property (`desc` of an opcartesian
  morphism, `transpMap`, the functors `Ψ`, the unit/counit) may freely be `noncomputable` (they
  use `ExistsUnique.choose`). Do not fight this. Explicit constructions (`Total`, `Fiber`,
  `dualOp`, `sigma`, `D2SGC` and its lifts) should stay computable — their data is given directly,
  not by choice.

### 2.1 The dependent-equality strategy (read this before writing any code)

Displayed categories are cast-heavy: `D.Hom f x y` depends on `f`, and coherence laws relate homs
over *propositionally equal but not definitionally equal* base morphisms (and, once `SplitOpfib`
enters, over propositionally equal objects like `transp (𝟙 a) x = x`). The strategy, in order of
preference:

0. **Always write `HEq` statements with the infix notation `a ≍ b`, never `HEq a b`.** This is
   mandatory throughout the project (it is available in this mathlib and keeps the cast-heavy
   statements readable). Term-level `HEq.*` lemmas (`HEq.rfl`, `HEq.trans`, `eq_of_heq`, …) are
   still referenced by name. Every `HEq` shown elsewhere in this plan should be read as `≍`.
1. **State all coherence *fields* and cross-base equations with `≍`** (e.g.
   `assoc : (φ ≫ᵈ ψ) ≫ᵈ χ ≍ φ ≫ᵈ (ψ ≫ᵈ χ)`). `≍` statements are uniform: they work
   whether the mismatch is in the base morphism, the endpoints, or both.
2. **Provide one cast operator and a small bridge API** in `Displayed/Basic.lean` (§3.1) and use
   it to *consume* `HEq` facts: convert `HEq` to `Eq`-after-`cast` when both sides' types are
   forced, and back.
3. **Whenever a construction lands inside a single fiber, work in the category `D.Fiber a` and
   use mathlib's `eqToHom`** for object equalities (e.g. `transp_comp`). `Fiber a` is an honest
   mathlib `Category`, so the entire `eqToHom` simp arsenal (`eqToHom_trans`, `eqToHom_map`,
   `eqToHom_refl`, `Functor.map_comp`, …) applies. This is the single biggest pain-killer:
   `dualOp`, `transpFunctor`, `factor`, the D2SGC hom-sets, and both natural isomorphisms of M9
   should all be phrased with fiber-category `eqToHom`s rather than raw casts wherever possible.
4. To *prove* a `HEq` between displayed morphisms: first `subst`/`obtain rfl` every available
   object- and base-equality (they are all `Eq` in a fixed type, so `subst` works), after which
   the goal usually becomes a plain `Eq` provable by `simp` with the bridge API. Avoid bare `▸`
   in definitions (motive hell); use the named `cast` operator or `eqToHom`.
5. For equalities of *functors into `Cat`* (needed for functoriality of `Ψ C` and naturality
   squares in `Cat`), use `CategoryTheory.Functor.ext` (object part by `funext`-style equality,
   hom part modulo `eqToHom` conjugation). Prove hom parts by reducing to uniqueness of the
   relevant universal property (§6, "uniqueness beats computation").

---

## 3. M1 — Displayed categories. File `Nfib/Displayed/Basic.lean`

```lean
/-- A category displayed over `A`. -/
structure Displayed (A : Type u₁) [Category.{v₁} A] where
  Ob : A → Type u₂
  Hom : {a a' : A} → (a ⟶ a') → Ob a → Ob a' → Type v₂
  id : {a : A} → (x : Ob a) → Hom (𝟙 a) x x
  comp : {a a' a'' : A} → {f : a ⟶ a'} → {g : a' ⟶ a''} → {x : Ob a} → {y : Ob a'} →
    {z : Ob a''} → Hom f x y → Hom g y z → Hom (f ≫ g) x z
  id_comp : ∀ {a a'} {f : a ⟶ a'} {x y} (φ : Hom f x y), HEq (comp (id x) φ) φ
  comp_id : ∀ {a a'} {f : a ⟶ a'} {x y} (φ : Hom f x y), HEq (comp φ (id y)) φ
  assoc : ∀ {…} (φ : Hom f x y) (ψ : Hom g y z) (χ : Hom h z w),
    HEq (comp (comp φ ψ) χ) (comp φ (comp ψ χ))
```

Scoped notation (in `scoped notation` under namespace `Nfib.Displayed`):
`x ⟶[f] y` for `D.Hom f x y` where inferable, and `φ ≫ᵈ ψ` for `D.comp φ ψ`.
(If elaboration of `⟶[f]` is troublesome because `D` is implicit, drop the arrow notation and use
`D.Hom` applied explicitly — do not burn time on notation.)

**Cast + bridge API** (all `@[simp]` where sensible):

```lean
/-- Transport a displayed morphism along an equality of base morphisms. -/
def castHom (D : Displayed A) {f g : a ⟶ a'} {x y} (h : f = g) :
    D.Hom f x y → D.Hom g x y   -- by cases h; exact id

@[simp] castHom_rfl, castHom_castHom
theorem castHom_heq  : HEq (D.castHom h φ) φ
theorem heq_iff_castHom_eq {φ : D.Hom f x y} {ψ : D.Hom g x y} (h : f = g) :
    HEq φ ψ ↔ D.castHom h φ = ψ
theorem comp_castHom / castHom_comp  -- push casts out of composites
theorem heq_comp  -- congruence: base eqs + HEq φ φ' + HEq ψ ψ' → HEq (φ ≫ᵈ ψ) (φ' ≫ᵈ ψ')
                  -- (endpoints may differ; state with the needed object equalities)
```

Also `Eq`-versions of the axioms via `castHom` (e.g. `id_comp' : D.id x ≫ᵈ φ = D.castHom
(Category.id_comp f).symm φ`), tagged `@[simp]` — these are the workhorses; the `HEq` fields are
mainly for *building* instances.

**Fiber category:**

```lean
def Fiber (D : Displayed A) (a : A) : Type u₂ := D.Ob a
instance : Category.{v₂} (D.Fiber a) where
  Hom x y := D.Hom (𝟙 a) x y
  id x := D.id x
  comp φ ψ := D.castHom (by simp) (φ ≫ᵈ ψ)
```
Category laws follow from the bridge API. Provide `@[simp]` unfolding lemmas
(`Fiber.comp_def`, `Fiber.id_def`) so later files never unfold the instance manually.

**Total category and projection:**

```lean
def Total (D : Displayed A) : Type (max u₁ u₂) := Σ a : A, D.Ob a
instance : Category.{max v₁ v₂} D.Total where
  Hom x y := Σ f : x.1 ⟶ y.1, D.Hom f x.2 y.2
  id x := ⟨𝟙 x.1, D.id x.2⟩
  comp F G := ⟨F.1 ≫ G.1, F.2 ≫ᵈ G.2⟩

def π (D : Displayed A) : D.Total ⥤ A      -- first projections
def ι (D : Displayed A) (a : A) : D.Fiber a ⥤ D.Total   -- b ↦ ⟨a, b⟩, β ↦ ⟨𝟙 a, β⟩
```
Category laws for `Total`: `Sigma.ext`, first component by `A`'s laws, second by the `HEq` fields
— this is exactly why the fields are `HEq`. Prove a hom-extensionality lemma
`Total.hom_ext : F.1 = G.1 → HEq F.2 G.2 → F = G` and `@[simp]` lemmas for `π`/`ι` on objects,
morphisms, and for `(ι a).map (β ≫ γ)`, `(ι a).map (𝟙 b)`, `π.map ((ι a).map β) = 𝟙 a`.

(Vertical functors between displayed categories are only needed at the doubly displayed level,
for D2SFib morphisms — they are defined in §5 as `DoubleDisplayed.VertFunctor`, not here.)

**Gate:** `lake build` clean; no `sorry`.

---

## 4. M2 — (Op)cartesian morphisms, split (op)fibrations, dual opfibration

### 4.1 `Nfib/Displayed/Cartesian.lean`

```lean
/-- `φ : x ⟶[f] y` is opcartesian: every map out of `x` over `f ≫ g` factors uniquely
through `φ` over `g`. (In displayed form this is the *strong* opcartesian property.) -/
def IsOpcartesian {D : Displayed A} {f : a ⟶ a'} {x y} (φ : D.Hom f x y) : Prop :=
  ∀ {a'' : A} (g : a' ⟶ a'') (z : D.Ob a'') (χ : D.Hom (f ≫ g) x z),
    ∃! ψ : D.Hom g y z, φ ≫ᵈ ψ = χ

def IsCartesian … (φ : D.Hom f x y) : Prop :=
  ∀ {a₀ : A} (g : a₀ ⟶ a) (z : D.Ob a₀) (χ : D.Hom (g ≫ f) z y),
    ∃! ψ : D.Hom g z x, ψ ≫ᵈ φ = χ
```

API (all four for the cartesian dual too):
`noncomputable def IsOpcartesian.desc (H) (g) (χ) : D.Hom g y z`, `@[simp] desc_fac :
φ ≫ᵈ H.desc g χ = χ`, `desc_uniq` / `hom_ext` (two maps postcomposing equally with `φ` are
equal), and stability lemmas: `IsOpcartesian.castHom` (opcartesian is preserved by `castHom`),
uniqueness-of-lifts up to iso is *not* needed — skip it.

### 4.2 `Nfib/Displayed/SplitOpfib.lean`

```lean
class SplitOpfib (D : Displayed A) where
  transp : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Ob a'
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → D.Hom f x (transp f x)
  olift_opcartesian : ∀ {a a'} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)
  transp_id : ∀ {a} (x : D.Ob a), transp (𝟙 a) x = x
  olift_id : ∀ {a} (x : D.Ob a), HEq (olift (𝟙 a) x) (D.id x)
  transp_comp : ∀ {a a' a''} (f : a ⟶ a') (g : a' ⟶ a'') (x),
    transp (f ≫ g) x = transp g (transp f x)
  olift_comp : ∀ …, HEq (olift (f ≫ g) x) (olift f x ≫ᵈ olift g (transp f x))

class SplitFib (D : Displayed A) where   -- exact mirror
  pull : {a a' : A} → (f : a ⟶ a') → D.Ob a' → D.Ob a
  clift : (f : a ⟶ a') → (y : D.Ob a') → D.Hom f (pull f y) y
  clift_cartesian, pull_id, clift_id, pull_comp, clift_comp
```

(`SplitFib` is only used implicitly — the D2SFib class inlines its own fiberwise version —
but define it anyway: it is cheap, it is in the user's spec, and it documents the duality.)

Derived API for `SplitOpfib` (all `noncomputable` where they use `desc`):

```lean
/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift. -/
noncomputable def factor (φ : D.Hom f x y) : transp f x ⟶ y        -- in D.Fiber a'
@[simp] olift_factor : olift f x ≫ᵈ (factor φ : D.Hom (𝟙 a') _ _) = D.castHom (by simp) φ
factor_uniq
@[simp] factor_olift : factor (olift f x) = 𝟙 (transp f x)
factor_castHom, factor_comp :
  factor (φ ≫ᵈ ψ) = eqToHom (transp_comp f g x) ≫ transpMap g (factor φ) ≫ factor ψ
  -- an equation in D.Fiber a''; note eqToHom, not a raw cast

/-- The hom-equivalence defining opfibrations. -/
noncomputable def homEquiv : D.Hom f x y ≃ (transp f x ⟶ y)   -- Fiber a' homs

/-- Transport of vertical morphisms; then the fiber-transport functor. -/
noncomputable def transpMap (f : a ⟶ a') (β : x ⟶ y /- Fiber a -/) :
    transp f x ⟶ transp f y := factor (D.castHom (by simp) (β ≫ᵈ olift f y))
noncomputable def transpFunctor (f : a ⟶ a') : D.Fiber a ⥤ D.Fiber a'
@[simp] transpFunctor_id : transpFunctor (𝟙 a) = 𝟭-up-to… -- state as:
  transpMap_id  : transpMap (𝟙 a) β = eqToHom (transp_id x) ≫ β ≫ eqToHom (transp_id y).symm
  transpMap_comp : transpMap (f ≫ g) β = eqToHom … ≫ transpMap g (transpMap f β) ≫ eqToHom …
  transpMap_id_vert : transpMap f (𝟙 x) = 𝟙 _   -- functor law, via factor_uniq
  transpMap_comp_vert : transpMap f (β ≫ γ) = transpMap f β ≫ transpMap f γ
olift_transpMap : olift f x ≫ᵈ transpMap f β = castHom … (β ≫ᵈ olift f y)  -- defining equation
```

Everything here is proved by `factor_uniq` (uniqueness of the universal property) plus the split
axioms — never by unfolding `choose`.

Also define the **chosen opcartesian morphisms of the total category**:

```lean
def totalOlift (f : a ⟶ a') (x : D.Ob a) : (⟨a, x⟩ : D.Total) ⟶ ⟨a', transp f x⟩ :=
  ⟨f, olift f x⟩
@[simp] π_map_totalOlift, totalOlift_id (HEq/eqToHom form), totalOlift_comp,
factorTotal : ∀ (F : (⟨a,x⟩ : D.Total) ⟶ ⟨a', y⟩),
  F = totalOlift F.1 x ≫ (D.ι a').map (factor F.2)   -- every total morphism = chosen lift ≫ vertical
```
With the curried `DoubleDisplayed` design of §5, `totalOlift`/`factorTotal` are *off the critical
path* (their role is played fiberwise by `olift_factor`); keep `totalOlift` (it is cheap and
documents the split structure of `∫B`), and drop `factorTotal` if it resists — the analogue that
*is* load-bearing is `dual_factor` in §4.3.

### 4.3 `Nfib/Displayed/DualOp.lean` — the dual opfibration

```lean
/-- Fiberwise opposite of a split opfibration: same objects; a morphism over `f : a ⟶ a'`
from `x` to `y` is a vertical morphism `y ⟶ transp f x`. Corresponds to the Grothendieck
construction of `a ↦ B(a)ᵒᵖ` in the paper. -/
noncomputable def dualOp (B : Displayed A) [SplitOpfib B] : Displayed A where
  Ob := B.Ob
  Hom {a a'} f x y := (y ⟶ B.transp f x : B.Fiber a')
  id x := eqToHom (B.transp_id x).symm
  comp {f g} φ ψ := ψ ≫ B.transpMap g φ ≫ eqToHom (B.transp_comp f g x).symm
```
Axioms: pure `eqToHom` + `transpMap_*` calculations inside fiber categories (this is strategy
§2.1(3) paying off; the `HEq` axioms here reduce, after `subst` of nothing — base morphism
equalities like `𝟙 ≫ f = f` — to `Fiber` equations closed by `simp [transpMap_id, …]`).
Note `dualOp` is `noncomputable` only because `transpMap` is; that is fine.

Key helpers for later files (with `@[simp]` lemmas for `π`, composition, and the analogue of
`factorTotal`):

```lean
def dualHoriz (α : a ⟶ a') (b : B.Ob a) :
    (⟨a, b⟩ : B.dualOp.Total) ⟶ ⟨a', B.transp α b⟩ := ⟨α, 𝟙 (B.transp α b)⟩
def dualVert {b b' : B.Fiber a} (β : b ⟶ b') :
    (⟨a, b'⟩ : B.dualOp.Total) ⟶ ⟨a, b⟩ := ⟨𝟙 a, β ≫ eqToHom (B.transp_id b').symm⟩
    -- second component must land in `B.dualOp.Hom (𝟙 a) b' b = (b ⟶ B.transp (𝟙 a) b')`
-- note contravariance: dualVert reverses vertical morphisms
lemma dual_factor : (⟨α, β⟩ : (⟨a,b⟩ : B.dualOp.Total) ⟶ ⟨a',b'⟩) =
    dualHoriz α b ≫ dualVert β        -- check: β : b' ⟶ transp α b is vertical
lemma dualVert_comp, dualHoriz_comp_dualVert_swap :
    dualVert (B.transpMap α β) ≫ dualHoriz α b = dualHoriz α b' ≫ dualVert β  -- for β : b ⟶ b'
    -- (the interchange in ∫(Bᵈᵒ); direction-check this against dual_factor when proving)
```

*(Optional, skip unless trivial: `instance : SplitOpfib B.dualOp`. Not needed for the theorem.)*

**Gate:** `lake build` clean; no `sorry`.

---

## 5. M3/M4 — Doubly displayed categories; sigma. Files `Nfib/Displayed/Double.lean`, `Nfib/Displayed/Sigma.lean`

**Design (user's item 2):** a displayed category over the displayed category `B` — the chain
`C → B → A` — is itself *displayed*: its objects are indexed by `B`'s displayed objects and its
homs by `B`'s displayed morphisms. This is a genuine new curried structure (not `Displayed
B.Total`):

```lean
structure DoubleDisplayed (B : Displayed A) where
  Ob : {a : A} → B.Ob a → Type u₃
  Hom : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} →
    B.Hom f b b' → Ob b → Ob b' → Type v₃
  id : {a : A} → {b : B.Ob a} → (c : Ob b) → Hom (B.id b) c c
  comp : {a a' a'' : A} → {f : a ⟶ a'} → {f' : a' ⟶ a''} →
    {b : B.Ob a} → {b' : B.Ob a'} → {b'' : B.Ob a''} →
    {g : B.Hom f b b'} → {g' : B.Hom f' b' b''} →
    {c : Ob b} → {c' : Ob b'} → {c'' : Ob b''} →
    Hom g c c' → Hom g' c' c'' → Hom (g ≫ᵈ g') c c''
  id_comp : ∀ … (θ : Hom g c c'), HEq (comp (id c) θ) θ
  comp_id : ∀ … (θ : Hom g c c'), HEq (comp θ (id c')) θ
  assoc : ∀ …, HEq (comp (comp θ θ') θ'') (comp θ (comp θ' θ''))
```

Scoped notation `θ ≫ᵈᵈ θ'` for `DoubleDisplayed.comp`. Note the coherence fields are `HEq`s
lying over `B`'s *own* `HEq` coherences (`comp (id c) θ` lies over `B.id b ≫ᵈ g`, `θ` over `g`,
related by `B.id_comp` — itself a `HEq`); this is why §2.1 insists on `HEq` throughout.

**Cast + bridge API**, mirroring §3's but one level up — the base datum is now a displayed
morphism, so the cast transports along an `Eq` of base morphisms *and* a `HEq` of `B`-morphisms:

```lean
def DoubleDisplayed.castHom (C : DoubleDisplayed B) {f f' : a ⟶ a'} {b : B.Ob a}
    {b' : B.Ob a'} {g : B.Hom f b b'} {g' : B.Hom f' b b'}
    (hf : f = f') (hg : HEq g g') {c c'} : C.Hom g c c' → C.Hom g' c c'
    -- by cases hf; rewrite hg to Eq; by cases
```
with the full set of bridge lemmas from §3 mirrored (`castHom_rfl`, `castHom_castHom`,
`castHom_heq`, `heq_iff_castHom_eq`, `comp_castHom`/`castHom_comp`, `heq_comp` congruence).
Build this API *completely* before starting M5 — it is the load-bearing wall.

**Fiber categories** (recall `B.Fiber a`-homs are definitionally `B.Hom (𝟙 a)`):

```lean
def DoubleDisplayed.Fiber (C : DoubleDisplayed B) {a : A} (b : B.Ob a) : Type u₃ := C.Ob b
instance : Category.{v₃} (C.Fiber b) where
  Hom c c' := C.Hom (B.id b) c c'
  id c := C.id c
  comp θ θ' := C.castHom (by simp) (B.id_comp (B.id b)) (θ ≫ᵈᵈ θ')
```
plus `@[simp]` unfolding lemmas as in §3.

**Opcartesianness at the double level** (only the opcartesian version is needed; the fiberwise
*cartesian* condition of a D2SFib is stated directly as an `∃!` field in §6.1):

```lean
def DoubleDisplayed.IsOpcartesian {C : DoubleDisplayed B} {f : a ⟶ a'} {b b'}
    {g : B.Hom f b b'} {c c'} (θ : C.Hom g c c') : Prop :=
  ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} (g' : B.Hom f' b' b'')
    (c'' : C.Ob b'') (χ : C.Hom (g ≫ᵈ g') c c''),
    ∃! ψ : C.Hom g' c' c'', θ ≫ᵈᵈ ψ = χ
```
with `desc` / `desc_fac` / `hom_ext` exactly as in §4.1 (noncomputable via `ExistsUnique.choose`).

**Vertical functors** (the morphisms underlying D2SFib morphisms; over `B` on the nose):

```lean
structure DoubleDisplayed.VertFunctor (C D : DoubleDisplayed B) where
  obj : {a : A} → {b : B.Ob a} → C.Ob b → D.Ob b
  map : {a a' : A} → {f : a ⟶ a'} → {b b'} → {g : B.Hom f b b'} → {c : C.Ob b} →
    {c' : C.Ob b'} → C.Hom g c c' → D.Hom g (obj c) (obj c')
  map_id : ∀ …, map (C.id c) = D.id (obj c)
  map_comp : ∀ …, map (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ'
```
(No casts: the base `B`-morphisms agree on the nose — the payoff of vertical functors.) Define
`VertFunctor.id`, `VertFunctor.comp`, an `@[ext]` lemma (`obj` equality fiberwise by `funext`,
then `map` by `HEq`/`subst`), and the fiber restriction
`VertFunctor.fiber (F) (b : B.Ob a) : C.Fiber b ⥤ D.Fiber b`.

**Sigma** (`Nfib/Displayed/Sigma.lean`): collapses the chain `C → B → A` to `ΣBC → A`; its
`Total` is the "associated category" of the chain:

```lean
def DoubleDisplayed.sigma (C : DoubleDisplayed B) : Displayed A where
  Ob a := Σ b : B.Ob a, C.Ob b
  Hom {a a'} f x y := Σ g : B.Hom f x.1 y.1, C.Hom g x.2 y.2
  id x := ⟨B.id x.1, C.id x.2⟩
  comp F G := ⟨F.1 ≫ᵈ G.1, F.2 ≫ᵈᵈ G.2⟩
  -- axioms: nested Sigma-style HEq congruence, from the HEq axioms of B and C
```

*(Optional sanity, skip if it drags: `uncurry : DoubleDisplayed B → Displayed B.Total` — the
other possible encoding — with `(C.uncurry).Total`-vs-`(C.sigma).Total` compatibility. Nothing
downstream depends on it.)*

**Gate:** `lake build` clean.

---

## 6. M5 — D2SFibs and their category. Files `Nfib/D2SFib/Basic.lean`, `Nfib/D2SFib/Category.lean`

Fix `(B : Displayed.{v₂, u₂} A) [SplitOpfib B]` for the rest of the plan.

### 6.1 The class (adapting Def. `def:d2sfib`)

`D2SFib` is a *class on* a doubly displayed category — data-carrying, exactly like `SplitOpfib`
is a class on a `Displayed A`. (The category of D2SFibs is then built from bundled objects in
§6.3.) Because the class carries data, never have two instances for the same `C` in scope.

```lean
class D2SFib {B : Displayed A} [SplitOpfib B] (C : DoubleDisplayed.{v₃, u₃} B) where
  /- (1) local split fibration: chosen cartesian lifts of *vertical* morphisms
     (`B.Hom (𝟙 a) b b'`, definitionally the homs of `B.Fiber a`),
     cartesian among morphisms of the same fiber. -/
  pull : {a : A} → {b b' : B.Ob a} → (β : B.Hom (𝟙 a) b b') → C.Ob b' → C.Ob b
  pullLift : ∀ {a} {b b'} (β : B.Hom (𝟙 a) b b') (c : C.Ob b'), C.Hom β (pull β c) c
  pullLift_cartesian : ∀ {a} {b b' b₀ : B.Ob a} (β : B.Hom (𝟙 a) b b') (c : C.Ob b')
    (β₀ : B.Hom (𝟙 a) b₀ b) (c₀ : C.Ob b₀) (χ : C.Hom (β₀ ≫ᵈ β) c₀ c),
    ∃! ξ : C.Hom β₀ c₀ (pull β c), ξ ≫ᵈᵈ pullLift β c = χ
    -- cast-free: both sides lie over `β₀ ≫ᵈ β : B.Hom (𝟙 a ≫ 𝟙 a) b₀ b'`
  pull_id : ∀ {a} {b : B.Ob a} (c : C.Ob b), pull (B.id b) c = c
  pullLift_id : ∀ …, HEq (pullLift (B.id b) c) (C.id c)
  pull_comp : ∀ {a} {b b' b'' : B.Ob a} (β : (b : B.Fiber a) ⟶ b') (γ : b' ⟶ b'') (c),
    pull (β ≫ γ) c = pull β (pull γ c)     -- `β ≫ γ` = Fiber-composition (vertical)
  pullLift_comp : ∀ …, HEq (pullLift (β ≫ γ) c) (pullLift β (pull γ c) ≫ᵈᵈ pullLift γ c)
  /- (2)+(3) split opfibration over A, with lifts typed over the chosen lifts of B.
     Paper's axiom (3) is absorbed by the type of `pushLift`. -/
  push : {a a' : A} → (α : a ⟶ a') → {b : B.Ob a} → C.Ob b → C.Ob (B.transp α b)
  pushLift : ∀ {a a'} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b),
    C.Hom (B.olift α b) c (push α c)
  pushLift_opcartesian : ∀ …, DoubleDisplayed.IsOpcartesian (pushLift α c)
    -- opcartesian over `B`: factors against arbitrary `g' : B.Hom γ (B.transp α b) b''`;
    -- see the note below
  push_id : ∀ {a b} (c : C.Ob b), HEq (push (𝟙 a) c) c
    -- endpoints differ by `B.transp_id`, hence HEq of *objects*; accompany with the
    -- rewritten-Eq form `push_id' : push (𝟙 a) c = (B.transp_id b) ▸ … c`
    -- if `HEq` of objects proves awkward downstream — pick ONE canonical form and stick to it
  pushLift_id : ∀ …, HEq (pushLift (𝟙 a) c) (C.id c)
  push_comp : ∀ {a a' a''} (α : a ⟶ a') (α' : a' ⟶ a'') {b} (c : C.Ob b),
    HEq (push (α ≫ α') c) (push α' (push α c))       -- endpoints differ by transp_comp
  pushLift_comp : ∀ …, HEq (pushLift (α ≫ α') c) (pushLift α c ≫ᵈᵈ pushLift α' (push α c))
  /- (4) strict push/pull interchange -/
  push_pull : ∀ {a a'} (α : a ⟶ a') {b b' : B.Ob a} (β : B.Hom (𝟙 a) b b') (c : C.Ob b'),
    push α (pull β c) = pull (B.transpMap α β) (push α c)
  pushLift_pullLift : ∀ …,
    HEq (pullLift β c ≫ᵈᵈ pushLift α c)
        (pushLift α (pull β c) ≫ᵈᵈ
          push_pull-adjusted (pullLift (B.transpMap α β) (push α c)))
```

Notes for the executor:

- `push_pull-adjusted` above is shorthand: the right-hand composite only typechecks after
  transporting `pushLift α (pull β c)`'s codomain along `push_pull`. No new transport helper is
  needed — the two objects live in *the same type* `C.Ob (B.transp α b)`, and `push_pull` is an
  `Eq` there, so plain rewriting works: state the field as
  ```lean
  pushLift_pullLift : HEq (pullLift β c ≫ᵈᵈ pushLift α c)
    ((push_pull α β c ▸ pushLift α (pull β c) :
        C.Hom (B.olift α b) (pull β c) (pull (B.transpMap α β) (push α c))) ≫ᵈᵈ
      pullLift (B.transpMap α β) (push α c))
  ```
  or, better, avoid `▸` entirely by stating it as: for every `δ` with
  `HEq δ (pushLift α (pull β c))` of the appropriate type, `HEq (pullLift β c ≫ᵈᵈ pushLift α c)
  (δ ≫ᵈᵈ pullLift …)`. The executor may reshape this field freely **as long as it says: the two
  ways around the pull/push square are heterogeneously equal, given `push_pull`.** The outer base
  `B`-morphisms match heterogeneously by `olift_transpMap` (that is exactly the paper's remark
  that `β ≫ olift = olift ≫ B(α)β`).
- **Why `pushLift_opcartesian` is opcartesianness over `B`:** the paper requires opcartesianness
  over `A` of the composite `π_A ∘ q`. Given that `B`'s own chosen lifts are opcartesian, letting
  the factorization test range over arbitrary displayed morphisms `g' : B.Hom γ (B.transp α b) b''`
  is equivalent to the paper's over-`A` condition: every `B`-morphism over `α ≫ γ` out of `b`
  factors as `B.olift α b ≫ᵈ g'` up to `castHom` (that is `olift_opcartesian` + `factor`). Record
  this equivalence as a lemma:
  `theorem sigma_opcartesian (C : DoubleDisplayed B) [D2SFib C] … :
  Displayed.IsOpcartesian (D := C.sigma) ⟨B.olift α b, pushLift α c⟩` — this both validates the
  definition against the paper and
  exercises `sigma`. (Prove it; it is a short UP-chase. If it exceeds ~a day of effort, leave it
  as the one permitted `sorry` outside the main line and move on — it is a sanity check, not a
  dependency.)

### 6.2 Derived structure (still `Basic.lean`)

Work under `variable {C : DoubleDisplayed B} [D2SFib C]` with `open D2SFib` — fiber categories
are just `C.Fiber b` from §5, no extra definition needed. All by universal properties +
splitness ("uniqueness beats computation": to show two verticals are equal, show both solve the
same UP problem — do **not** unfold `choose`):

```lean
noncomputable def pushMap (α : a ⟶ a') : (c ⟶ c') → (push α c ⟶ push α c')  -- Fiber homs
noncomputable def pushFunctor (α : a ⟶ a') (b : B.Ob a) :
    C.Fiber b ⥤ C.Fiber (B.transp α b)
noncomputable def pullMap (β : B.Hom (𝟙 a) b b') : (c ⟶ c') → (pull β c ⟶ pull β c')
noncomputable def pullFunctor (β : B.Hom (𝟙 a) b b') : C.Fiber b' ⥤ C.Fiber b
-- functor laws, plus the split laws in eqToHom form:
pushFunctor_id / pushFunctor_comp / pullFunctor_id / pullFunctor_comp
  -- stated as `Functor.ext`-friendly object/hom equations with eqToHom, mirroring transpMap_id/comp
/-- Lemma `d2sfib:lemma` of the paper: interchange on morphisms. -/
theorem pushMap_pullMap (α) (β) (f : c ⟶ c') :
    pushMap α (pullMap β f) = eqToHom (push_pull …) ≫ pullMap (B.transpMap α β) (pushMap α f)
      ≫ eqToHom (push_pull …).symm
/-- The two-step hom equivalence (paper: hom(α_!c, β*c') ≅ hom(c, c')). -/
noncomputable def d2sHomEquiv (α : a ⟶ a') (g : B.Hom α b b')
    (c : C.Ob b) (c' : C.Ob b') :
    C.Hom g c c' ≃ (push α c ⟶ pull (B.factor g) c')
    -- the RHS is a hom in `C.Fiber (B.transp α b)`: note `B.factor g : B.transp α b ⟶ b'`
    -- is vertical, so `pull (B.factor g) c' : C.Ob (B.transp α b)`, matching `push α c`
```
built by composing the opcartesian descent equivalence (from `pushLift_opcartesian` + the
factorization `HEq g (B.olift α b ≫ᵈ B.factor g)`, i.e. `olift_factor`) with the cartesian lift
equivalence (from `pullLift_cartesian`). This single lemma powers the whole of M9's counit
isomorphism; invest in making its `simp` interface good
(`d2sHomEquiv_apply_comp`-style lemmas for how it interacts with `≫ᵈᵈ`, `pullLift`, `pushLift`).

### 6.3 Morphisms and the category (`Nfib/D2SFib/Category.lean`)

Adapting the paper's dependent 2-sided cartesian functors, in split form (preserving *chosen*
lifts on the nose — required for the equivalence with strict natural transformations):

```lean
structure D2SFibHom (C C' : DoubleDisplayed B) [D2SFib C] [D2SFib C'] extends
    DoubleDisplayed.VertFunctor C C' where
  obj_pull : ∀ …, obj (pull β c) = pull β (obj c)
  map_pullLift : ∀ …, HEq (map (pullLift β c)) (pullLift β (obj c))
  obj_push : ∀ …, obj (push α c) = push α (obj c)
  map_pushLift : ∀ …, HEq (map (pushLift α c)) (pushLift α (obj c))

/-- Bundled D2SFibs: the objects of the category `D2SFib(A,B)`. Mathlib `Cat`-style
(carrier + instance field); cf. `CategoryTheory.Cat` / `CategoryTheory.Bundled`. -/
structure D2SFibCat (B : Displayed A) [SplitOpfib B] where
  C : DoubleDisplayed.{v₃, u₃} B
  [str : D2SFib C]

attribute [instance] D2SFibCat.str

instance : Category (D2SFibCat B) where
  Hom E E' := D2SFibHom E.C E'.C
  -- id/comp of D2SFibHom; @[ext] lemma on D2SFibHom (via VertFunctor's) first
```
The preservation fields compose and the identity satisfies them trivially; the `Category` laws
reduce to `VertFunctor`'s ext lemma. Note (for M7): `D2SFibHom.fiberFunctor : C.Fiber b ⥤ C'.Fiber b`
(restriction of `F.fiber`), and lemmas: it commutes with `pushFunctor`/`pullFunctor` **on the
nose** (`Functor.ext` with `eqToHom`-free object part, thanks to `obj_pull`/`obj_push`; hom parts
by UP-uniqueness from `map_pullLift`/`map_pushLift`).

**Gate:** `lake build` clean; no `sorry` (except possibly `sigma_opcartesian`, see above).

---

## 7. M6 — Statement of the main theorem. File `Nfib/D2SFib/Equivalence.lean` (skeleton)

```lean
/-- **Main theorem** (displayed adaptation of Proposition `prop:d2sfibequiv`):
functors from the total category of the dual opfibration of `B` to `Cat` are
equivalent to dependent 2-sided fibrations over `B`. -/
noncomputable def d2sfibEquivalence (B : Displayed.{v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₃, u₃} B := sorry
```

Pin the universes exactly as shown: the fibers `E.C.Fiber b` of an `E : D2SFibCat.{v₃,u₃} B` are categories
with objects in `Type u₃` and homs in `Type v₃`, i.e. objects of `Cat.{v₃, u₃}`. Both sides are
categories via mathlib's `Functor.category` and M5's instance respectively. **This milestone is
just: the statement elaborates.** Commit here (`git add -A && git commit`) — this is the
checkpoint the user asked for as item 4; everything after strengthens it from statement to proof.

---

## 8. M7 — `Ψ`: from D2SFibs to functors. File `Nfib/D2SFib/ToFunctor.lean`

Adapting §"From fibrations to functors":

```lean
noncomputable def D2SFib.toFunctorObj (C : DoubleDisplayed B) [D2SFib C] :
    B.dualOp.Total ⥤ Cat.{v₃, u₃} where
  obj x := Cat.of (C.Fiber x.2)
  map {x x'} F :=            -- F = ⟨α, β⟩ with β : x'.2 ⟶ B.transp α x.2 vertical
    pushFunctor α x.2 ⋙ pullFunctor β  -- : Fiber b ⥤ Fiber (B.transp α b) ⥤ Fiber b' ✓
  map_id / map_comp := by …  -- equalities of functors in Cat: `Functor.ext`;
                             -- object parts from pull_id/pull_comp/push_id/push_comp +
                             -- dualOp's comp formula; hom parts from pushMap_pullMap
                             -- (the interchange lemma) and pull/pushFunctor_id/comp
```

`map_comp` is the paper's pasted-square diagram; in Lean it is: unfold `dualOp.comp`
(`ψ ≫ transpMap g φ ≫ eqToHom …`), then `pullFunctor_comp` + interchange + `eqToHom` simp.
Budget real time here; it is the first place all the M2/M5 simp lemmas must actually fire.
If `Functor.ext` produces unmanageable `eqToHom` goals, prove the hom-part equalities by
UP-uniqueness (both sides are the unique solution of one descent problem).

```lean
noncomputable def D2SFib.toFunctorMap {E E' : D2SFibCat B} (Φ : E ⟶ E') :
    toFunctorObj E.C ⟶ toFunctorObj E'.C
  -- components: Cat-morphisms `D2SFibHom.fiberFunctor`; naturality: the on-the-nose
  -- commutation lemmas from §6.3
noncomputable def D2SFib.toFunctor : D2SFibCat B ⥤ (B.dualOp.Total ⥤ Cat.{v₃, u₃})
  -- obj E := toFunctorObj E.C
  -- functoriality: components compose on the nose; `NatTrans.ext` + `Functor.ext` (objects equal defeq)
```

**Gate:** `lake build`; only remaining `sorry` is `d2sfibEquivalence`.

---

## 9. M8 — `Φ`: the D2S Grothendieck construction. File `Nfib/D2SFib/Grothendieck.lean`

Adapting Def. `def:D2SGC` and the proposition after it.

### 9.1 The displayed category

```lean
def D2SGC (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : DoubleDisplayed B where
  Ob {a} b := F.obj ⟨a, b⟩
  Hom {a a'} {α} {b} {b'} (g : B.Hom α b b') c c' :=
    (F.map (B.dualHoriz α b)).obj c ⟶ (F.map (B.dualVert (B.factor g))).obj c'
      -- a hom in the category F.obj ⟨a', B.transp α b⟩; cf. the paper's
      -- hom_{C(a', B(α)b)}(C(α,id)c, C(id,β)c')
  id x := eqToHom … ≫ 𝟙-ish …         -- use: dualHoriz (𝟙 a) b and dualVert (factor (B.id b))
                                       -- are BOTH propositionally 𝟙 ⟨a,b⟩ in ∫(Bᵈᵒ)
                                       -- (via olift_id / factor lemmas); so both F.map's are
                                       -- propositionally 𝟭, and `id` is an eqToHom conjugate of 𝟙 c.
                                       -- Concretely: eqToHom h₁ ≫ eqToHom h₂ where
                                       -- h₁ : (F.map (dualHoriz (𝟙 a) b)).obj c = c, etc.
  comp {…} θ θ' :=   -- θ over `g : B.Hom α b b'`, θ' over `g' : B.Hom α' b' b''`; the composite
                     -- lies over `g ≫ᵈ g'`, whose `factor` is computed by `factor_comp` (§4.2);
                     -- follow Def. `def:D2SGC`:
    eqToHom … ≫ (F.map (B.dualHoriz α' _)).map θ ≫ eqToHom …
      ≫ (F.map (B.dualVert _)).map θ' ≫ eqToHom …
```
This is the paper's `γ ≔ C(α',id)θ ≫ C(id, B(α')β)θ'` with three `eqToHom`s mediating the
propositional equalities of `F.map`-composites (all obtained from `F.map_comp`/`F.map_id`
applied to `dual_factor`, `dualHoriz_comp_dualVert_swap`, `factor_comp`, `olift_comp`).

**Recommended technique** for the axioms (`id_comp`, `comp_id`, `assoc` as `HEq`s): first prove
a *reindexing lemma* packaging "apply `F` to an equality of morphisms in `∫(Bᵈᵒ)`":
```lean
lemma F_obj_congr {u v : x ⟶ y} (h : u = v) (c) : (F.map u).obj c = (F.map v).obj c
lemma F_map_conj {u v} (h : u = v) (θ) :
    (F.map u).map θ = eqToHom … ≫ (F.map v).map θ ≫ eqToHom …
```
and then all three axioms are `simp [eqToHom_trans, eqToHom_map, Functor.map_comp, …]`-driven
computations *inside one fiber category of `F`*, after substituting the base equalities. Assoc
is the hardest single proof in the project after M9's unit; the corresponding paper content is
the `assocggc` figure. If stuck: write the two sides as `F.map u₁ ≫ … ` chains, and prove the
underlying `∫(Bᵈᵒ)`-morphism equality first (a `Total.hom_ext` computation in `dualOp`), then
conjugate with `F_map_conj`.

### 9.2 The D2SFib instance and functoriality (paper's proposition, items 1–4)

```lean
noncomputable instance D2SGC.instD2SFib (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) :
    D2SFib (D2SGC F) where
  pull β c := (F.map (B.dualVert β)).obj c          -- paper: (a, b, C(id,β)c)
  pullLift β c := eqToHom-conjugated 𝟙               -- paper: (id, β, id)
  push α c := (F.map (B.dualHoriz α b)).obj c        -- paper: (a', B(α)b, C(α,id)c)
  pushLift α c := eqToHom-conjugated 𝟙               -- paper: (α, id, id)
  …
```
The UP fields: a factorization against `pullLift`/`pushLift` is, after unfolding, precisely "a
morphism in a fiber of `F`", so both `∃!` fields are proved by exhibiting the composite with the
inverse `eqToHom`s (existence) and cancelling `eqToHom`s (uniqueness) — the paper's items 1 and 2.
Splitness fields: from `F.map_id`/`F.map_comp` + the `dualHoriz`/`dualVert` composition lemmas.
`push_pull` and `pushLift_pullLift`: the paper's item 4 — both sides are `F.map` of *equal*
`∫(Bᵈᵒ)`-morphisms (`dualHoriz_comp_dualVert_swap`), applied to `c`.

Then, on morphisms (natural transformations `κ : F ⟶ F'`), following the paper:

```lean
/-- Bundled form: the object of `D2SFibCat B` carried by the construction. -/
noncomputable def D2SGCFib (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : D2SFibCat B := ⟨D2SGC F⟩
noncomputable def D2SGCMap (κ : F ⟶ F') : D2SGCFib F ⟶ D2SGCFib F'
  -- VertFunctor: obj := (κ.app ⟨a,b⟩).obj, map := naturality-square-conjugated (κ.app _).map
  -- preservation of pull/push: κ's naturality at dualVert/dualHoriz, applied to objects
noncomputable def D2SGCFunctor : (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ⥤ D2SFibCat B
```

**Gate:** `lake build`; only remaining `sorry` is `d2sfibEquivalence`.

---

## 10. M9 — The equivalence. Finish `Nfib/D2SFib/Equivalence.lean`

Adapting §"The equivalence". Build `Equivalence.mk D2SGCFunctor.toFunctor`-style… concretely:

```lean
noncomputable def d2sfibEquivalence … : (B.dualOp.Total ⥤ Cat.{v₃,u₃}) ≌ D2SFibCat B :=
  Equivalence.mk (D2SGCFunctor B) (D2SFib.toFunctor B) unitIso counitIso
```

**Counit (`Φ ∘ Ψ ≅ 𝟭` on D2SFibs; the paper's `F`/`G` pair).** For `E : D2SFibCat B`, the object
part of `D2SGCFib (toFunctorObj E.C)` at `b` is *definitionally* `E.C.Ob b` (fibers of
`toFunctorObj` are `E.C.Fiber b` whose carrier is `E.C.Ob b`). Hom-sets differ: over
`g : B.Hom α b b'` they are `(pushFunctor α b ⋙ pullFunctor (𝟙 _)).obj c ⟶ …` versus
`E.C.Hom g c c'`.
The bridge is exactly `d2sHomEquiv` (§6.2) composed with `eqToHom`s absorbing
`pullFunctor (𝟙 _)`-style units. Construct:

- `counitComponent (E : D2SFibCat B) : D2SGCFib (toFunctorObj E.C) ≅ E` in `D2SFibCat B`:
  hom and inv are `D2SFibHom`s whose `VertFunctor.obj` is the identity function and whose `map` is
  `d2sHomEquiv.symm` (resp. `d2sHomEquiv`) suitably `eqToHom`-adjusted; `map_comp` is the
  paper's big pasted diagram for `F` — prove it with `d2sHomEquiv`'s `simp` interface and
  UP-uniqueness, not by diagram chasing composites manually. Both `hom ≫ inv = 𝟙` proofs come
  free from `Equiv` round-trips + the `@[ext]` lemma.
- **Naturality of the counit in `E`** (glossed as "immediate" in the paper — it is not, in Lean):
  for `Φ : E ⟶ E'`, both composites have identity object parts, so `D2SFibHom`-ext reduces to a
  `map`-equality, provable by UP-uniqueness: both sides are the unique solution to the same
  descent problem, using `map_pullLift`/`map_pushLift` of `Φ`. Expect this to take a couple of
  focused sessions.

**Unit (`𝟭 ≅ Ψ ∘ Φ` on functor categories; the paper's `ξ`).** For `F : B.dualOp.Total ⥤ Cat`,
component at `⟨a,b⟩`: an iso in `Cat` between `F.obj ⟨a,b⟩` and the fiber of `D2SGC F` at
`⟨a,b⟩`. Objects agree definitionally; a fiber hom `c ⟶ c'` of `D2SGC F` is
`(F.map (dualHoriz (𝟙 a) b)).obj c ⟶ (F.map (dualVert (factor (B.olift (𝟙 a) b)))).obj c'`, and
both of those functors are propositionally `𝟭` — so the component iso is "identity on objects,
`eqToHom`-conjugation on homs". Package this once as a general lemma:

```lean
def Cat.isoOfEqToHom {C D : Cat} (hobj : ∀ …) (hhom : …) : C ≅ D
-- or reuse: build the iso from two explicit functors with Functor.ext round-trip proofs
```
Naturality in `⟨a,b⟩` = the paper's `C(α,β) = C(id,β) ∘ C(α,id)` = `F.map_comp` at
`dual_factor`, modulo `eqToHom`. Naturality of the whole unit in `F` is a `NatTrans.ext` +
componentwise `Functor.ext` computation with `κ.naturality`.

If `Equivalence.mk`'s triangle-law obligations (it derives them via `adjointifyη` — check the
mathlib API: `Equivalence.mk` takes only unit and counit isos and adjusts them) cause trouble,
that is fine — `Equivalence.mk` in mathlib does **not** require the triangle law; it fixes the
unit automatically. Do not hand-prove the triangle identities.

**Gate (final):** `lake build` clean, zero `sorry` in the project, and
`#print axioms Nfib.d2sfibEquivalence` reports nothing beyond `propext`, `Classical.choice`,
`Quot.sound`.

---

## 11. Working practices for the executor

- **Use the `lean4` skill/tooling** (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`,
  local search) rather than blind edit-and-build loops; build single files with
  `lake build Nfib.Displayed.Basic` etc. for fast iteration. The first `lake build` will compile
  the mathlib cache — run `lake exe cache get` first if `.lake` lacks built oleans.
- **Uniqueness beats computation.** Any equality between morphisms produced by `desc`/`factor`/
  `pullLift_cartesian` should be proved by showing both sides solve the same factorization
  problem. Never `unfold` a `choose`.
- **Keep a per-file `simp` discipline**: every construction ships its `@[simp]` unfolding and
  interaction lemmas *in the same file*, before the next file starts consuming it. If a proof in
  file *n+1* needs a 10-line `conv` dance, the missing lemma belongs in file *n*.
- **`subst` early.** In any `HEq` goal, immediately `subst` all object/base equalities in
  context; goals that remain heterogeneous after all possible `subst`s indicate a missing
  `castHom`/`eqToHom` reformulation upstream — fix the statement, don't push through.
- **Commit at every milestone gate** (plain `git commit` on `master`; the repo is not yet
  pushed anywhere).
- If a *statement shape* given in this plan does not elaborate as written (implicit-argument
  or universe issues), you are free to adjust the shape — the invariants that must survive are
  the ones spelled out in prose next to each definition and the dictionary of §1. Note any such
  deviation in a `DEVIATIONS.md`.

## 12. Risk register (where the time will actually go)

1. **`HEq`/cast plumbing (M1–M3).** Mitigated by the bridge API + fiber-`eqToHom` strategy of
   §2.1. If `Fiber`'s `Category` instance leaks `castHom`s into `simp`-normal forms, add
   `@[simp]` unfolding lemmas until goals state themselves in fiber-category vocabulary. The
   doubly displayed layer adds one wrinkle: `DoubleDisplayed.castHom` transports along a `HEq`
   of base *displayed* morphisms rather than a plain `Eq` — mirror the entire bridge API at that
   level (§5) before starting M5, or the D2SFib proofs will stall.
2. **`D2SGC` associativity (M8)** and **counit `map_comp` + naturality (M9)** — the two
   heaviest proofs. Both are scheduled after all supporting `simp` interfaces exist; both have a
   designated fallback technique (prove the base `∫(Bᵈᵒ)` equality first, then conjugate /
   UP-uniqueness).
3. **Equalities of functors into `Cat` (M7–M9).** Unavoidable given split/strict statements;
   contained via `Functor.ext` + `eqToHom` simp set. If a specific `Functor.ext` hom-goal
   stalls, restate the two functors' `map`s as solutions of one UP and apply uniqueness.
4. **Universe issues in the main statement (M6).** Resolved by fixing `Cat.{v₃, u₃}` against
   `DoubleDisplayed.{v₃, u₃}` fibers; if `Cat.of (C.Fiber b)` fails to elaborate at those universes,
   check that `Fiber` is a `def` (not `abbrev`) carrying its own `Category` instance with exact
   universes `Category.{v₃} (Fiber …)`.
