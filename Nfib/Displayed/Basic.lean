import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Displayed categories

This file defines `Nfib.Displayed A`, a category displayed over a base category `A`, following the
standard fibrational notion: objects are indexed by objects of `A`, and morphisms lying over
`f : a ⟶ a'` form their own type `Hom f x y`.

A displayed hom-type depends on the base morphism it lies over, so the coherence laws relate
morphisms of *different* types (`𝟙ᵈ x ≫ᵈ φ` lies over `𝟙 a ≫ f`, while `φ` lies over `f`).
Rather than state them with `HEq`, we split the definition in two, exactly as mathlib splits
`CategoryTheory.CategoryStruct` off from `CategoryTheory.Category`:

* `DisplayedStruct` carries only the data (`Ob`, `Hom`, `id`, `comp`);
* that data already supports two cast operators — `DisplayedStruct.castHom`, transporting a
  displayed morphism along an equality of base morphisms, and `DisplayedStruct.castOb`,
  transporting one along equalities of its endpoints. Their equalities are discharged by
  `cat_disch` by default, so `D.castHom φ` and `D.castOb φ` usually suffice;
* `Displayed extends DisplayedStruct` then states the laws as honest equalities, by casting the
  left-hand side into the right-hand side's type — and, being equalities, they are `simp` lemmas.

We provide:

* the structures `DisplayedStruct` and `Displayed`, and scoped notation `𝟙ᵈ x` / `φ ≫ᵈ ψ` for the
  displayed identity and displayed composition (the `ᵈ`-decorated analogues of `𝟙` and `≫`);
* the `castHom` and `castOb` APIs, together with small bridges converting between `HEq` and
  cast-`Eq` (including `HEq` restatements `id_comp_heq`, `comp_id_heq`, `assoc_heq` of the laws);
* the fiber category `Displayed.Fiber D a` (an honest mathlib `Category`);
* the total category `Displayed.Total D` with projection `π` and fiber inclusions `ι`.

## Guidelines for `simp` lemmas

A displayed hom-type `D.Hom f x y` can vary in two independent ways: in the base morphism `f`
(mediated by `castHom`) and in the endpoints `x`, `y` (mediated by `castOb`). The `simp` set here
is organised around two rules.

1. **Generalise the category-level `simp` set to the displayed case.** Whenever mathlib marks a
   `Category` lemma `@[simp]`, its displayed counterpart should be `@[simp]` too. This is why the
   laws `Displayed.id_comp`, `Displayed.comp_id` and `Displayed.assoc` are `simp` lemmas, matching
   `Category.id_comp`, `Category.comp_id` and `Category.assoc`.

2. **Push casts outwards.** When an operation has a cast in only one of its components, the
   normal form moves that cast as far out as possible, so that a term becomes a single outermost
   cast applied to a cast-free body. `DisplayedStruct.castHom_comp` and
   `DisplayedStruct.comp_castHom` are the archetypes: both rewrite a composite with one cast factor
   into `D.castHom (φ ≫ᵈ ψ)`; `DisplayedStruct.castOb_comp` and `DisplayedStruct.comp_castOb` do
   the same for the endpoint casts. Nested casts collapse via `castHom_castHom` / `castOb_castOb`,
   and a cast along a reflexive equation disappears via `castHom_self` / `castOb_self`, so this
   normal form is reached without accumulating casts.

   When both kinds of cast are present, `DisplayedStruct.castOb_castHom` fixes the order:
   `castHom` outermost, so the normal form is `D.castHom (D.castOb φ _ _) _`.

This is milestone **M1** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]

/-- The *data* of a category displayed over `A`: objects over each `a : A`, morphisms lying over
each base morphism `f : a ⟶ a'`, displayed identities and displayed composition — but none of the
coherence laws.

This stands to `Displayed` as `CategoryTheory.CategoryStruct` stands to
`CategoryTheory.Category`. Splitting it off is what lets the laws of `Displayed` be stated as
equalities: the cast operator `DisplayedStruct.castHom` needs only this data, and is therefore
available while the fields of `Displayed` are being declared. -/
structure DisplayedStruct (A : Type u₁) [Category.{v₁} A] where
  /-- The type of objects lying over `a : A`. -/
  Ob : A → Type u₂
  /-- The type of displayed morphisms lying over `f : a ⟶ a'`. -/
  Hom : {a a' : A} → (a ⟶ a') → Ob a → Ob a' → Type v₂
  /-- The displayed identity over `𝟙 a`. -/
  id : {a : A} → (x : Ob a) → Hom (𝟙 a) x x
  /-- Displayed composition, lying over `f ≫ g`. -/
  comp : {a a' a'' : A} → {f : a ⟶ a'} → {g : a' ⟶ a''} → {x : Ob a} → {y : Ob a'} →
    {z : Ob a''} → Hom f x y → Hom g y z → Hom (f ≫ g) x z

namespace Displayed

/-- Notation for the displayed identity morphism, mirroring `𝟙` for categories. -/
scoped notation "𝟙ᵈ" => Nfib.DisplayedStruct.id _

/-- Notation for displayed composition, mirroring `≫` for categories. -/
scoped notation:80 φ:81 " ≫ᵈ " ψ:80 => Nfib.DisplayedStruct.comp _ φ ψ

/-- Notation for a displayed hom-type: `x ⟶[f] y` is the type of displayed morphisms from `x` to
`y` lying over the base morphism `f`. -/
scoped notation:10 x " ⟶[" f "] " y => Nfib.DisplayedStruct.Hom _ f x y

end Displayed

namespace DisplayedStruct

open scoped Displayed

variable (D : DisplayedStruct A)

section CastHom

variable {a a' a'' : A}

/-- Transport a displayed morphism along an equality of base morphisms.

The equality is the *last* argument and carries a `by cat_disch` default, so at a call site where
the target base morphism is determined by the expected type it can simply be omitted: write
`D.castHom φ` and let `cat_disch` produce the proof. -/
def castHom {f g : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (h : f = g := by cat_disch) : x ⟶[g] y :=
  match g, h with
  | _, rfl => φ

@[simp]
theorem castHom_rfl {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.castHom φ rfl = φ := rfl

@[simp]
theorem castHom_castHom {f g k : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (h₁ : f = g) (h₂ : g = k) : D.castHom (D.castHom φ h₁) h₂ = D.castHom φ (h₁.trans h₂) := by
  cases h₁; cases h₂; rfl

theorem castHom_heq {f g : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) (h : f = g) :
    D.castHom φ h ≍ φ := by cases h; rfl

@[simp]
theorem castHom_self {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) (h : f = f) :
    D.castHom φ h = φ := eq_of_heq (D.castHom_heq φ h)

theorem heq_iff_castHom_eq {f g : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    {ψ : x ⟶[g] y} (h : f = g) : φ ≍ ψ ↔ D.castHom φ h = ψ := by
  cases h; exact heq_iff_eq

theorem castHom_eq_iff_heq {f g : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    {ψ : x ⟶[g] y} (h : f = g) : D.castHom φ h = ψ ↔ φ ≍ ψ :=
  (D.heq_iff_castHom_eq h).symm

@[simp]
theorem castHom_comp {f f' : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (h : f = f') (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    (D.castHom φ h) ≫ᵈ ψ = D.castHom (φ ≫ᵈ ψ) := by cases h; rfl

@[simp]
theorem comp_castHom {f : a ⟶ a'} {g g' : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (h : g = g') (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    φ ≫ᵈ (D.castHom ψ h) = D.castHom (φ ≫ᵈ ψ) := by cases h; rfl

/-- Congruence for displayed composition: base equalities plus `HEq`s of the factors give a `HEq`
of composites (endpoints may differ). -/
theorem heq_comp {f f' : a ⟶ a'} {g g' : a' ⟶ a''} {x x' : D.Ob a} {y y' : D.Ob a'}
    {z z' : D.Ob a''} (hf : f = f') (hg : g = g') (hx : x = x') (hy : y = y') (hz : z = z')
    {φ : x ⟶[f] y} {φ' : x' ⟶[f'] y'} {ψ : y ⟶[g] z} {ψ' : y' ⟶[g'] z'}
    (hφ : φ ≍ φ') (hψ : ψ ≍ ψ') : φ ≫ᵈ ψ ≍ φ' ≫ᵈ ψ' := by
  subst hf hg hx hy hz
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hψ
  rfl

end CastHom

section CastOb

variable {a a' a'' : A}

/-- Transport a displayed morphism along equalities of its *endpoints*.

This is the companion of `castHom`, which transports along an equality of the *base* morphism.
Together they cover the two ways a displayed hom-type can vary. As for `castHom`, both equalities
default to `cat_disch`. -/
def castOb {f : a ⟶ a'} {x x' : D.Ob a} {y y' : D.Ob a'} (φ : x ⟶[f] y)
    (hx : x = x' := by cat_disch) (hy : y = y' := by cat_disch) : x' ⟶[f] y' :=
  match x', hx, y', hy with
  | _, rfl, _, rfl => φ

@[simp]
theorem castOb_rfl {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.castOb φ rfl rfl = φ := rfl

theorem castOb_heq {f : a ⟶ a'} {x x' : D.Ob a} {y y' : D.Ob a'} (φ : x ⟶[f] y) (hx : x = x')
    (hy : y = y') : D.castOb φ hx hy ≍ φ := by cases hx; cases hy; rfl

@[simp]
theorem castOb_self {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) (hx : x = x)
    (hy : y = y) : D.castOb φ hx hy = φ := eq_of_heq (D.castOb_heq φ hx hy)

@[simp]
theorem castOb_castOb {f : a ⟶ a'} {x x' x'' : D.Ob a} {y y' y'' : D.Ob a'} (φ : x ⟶[f] y)
    (hx : x = x') (hy : y = y') (hx' : x' = x'') (hy' : y' = y'') :
    D.castOb (D.castOb φ hx hy) hx' hy' = D.castOb φ (hx.trans hx') (hy.trans hy') := by
  cases hx; cases hy; cases hx'; cases hy'; rfl

theorem heq_iff_castOb_eq {f : a ⟶ a'} {x x' : D.Ob a} {y y' : D.Ob a'} {φ : x ⟶[f] y}
    {ψ : x' ⟶[f] y'} (hx : x = x') (hy : y = y') : φ ≍ ψ ↔ D.castOb φ hx hy = ψ := by
  cases hx; cases hy; exact heq_iff_eq

theorem castOb_eq_iff_heq {f : a ⟶ a'} {x x' : D.Ob a} {y y' : D.Ob a'} {φ : x ⟶[f] y}
    {ψ : x' ⟶[f] y'} (hx : x = x') (hy : y = y') : D.castOb φ hx hy = ψ ↔ φ ≍ ψ :=
  (D.heq_iff_castOb_eq hx hy).symm

/-- `castHom` and `castOb` commute. The normal form keeps `castHom` outermost, so that a fully
transported morphism reads `castHom (castOb φ …) …`. -/
@[simp]
theorem castOb_castHom {f g : a ⟶ a'} {x x' : D.Ob a} {y y' : D.Ob a'} (φ : x ⟶[f] y)
    (h : f = g) (hx : x = x') (hy : y = y') :
    D.castOb (D.castHom φ h) hx hy = D.castHom (D.castOb φ hx hy) h := by
  cases h; cases hx; cases hy; rfl

/-- Pushing a `castOb` on the domain out of a composite. -/
@[simp]
theorem castOb_comp {f : a ⟶ a'} {g : a' ⟶ a''} {x x' : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (φ : x ⟶[f] y) (ψ : y ⟶[g] z) (hx : x = x') :
    (D.castOb φ hx rfl) ≫ᵈ ψ = D.castOb (φ ≫ᵈ ψ) hx rfl := by cases hx; rfl

/-- Pushing a `castOb` on the codomain out of a composite. -/
@[simp]
theorem comp_castOb {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'} {z z' : D.Ob a''}
    (φ : x ⟶[f] y) (ψ : y ⟶[g] z) (hz : z = z') :
    φ ≫ᵈ (D.castOb ψ rfl hz) = D.castOb (φ ≫ᵈ ψ) rfl hz := by cases hz; rfl

/-- Moving a `castOb` across the composition point. Deliberately *not* a `simp` lemma: it rewrites
in both directions. -/
theorem castOb_comp_castOb {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y y' : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y' ⟶[g] z) (hy : y = y') :
    (D.castOb φ rfl hy) ≫ᵈ ψ = φ ≫ᵈ (D.castOb ψ hy.symm rfl) := by cases hy; rfl

/-- Congruence for displayed composition in `castOb` form: this is the `Eq`-valued replacement for
`heq_comp` when only the *objects* vary. -/
theorem castOb_comp_castOb_eq {f : a ⟶ a'} {g : a' ⟶ a''} {x x' : D.Ob a} {y y' : D.Ob a'}
    {z z' : D.Ob a''} (φ : x ⟶[f] y) (ψ : y' ⟶[g] z) (hx : x = x') (hy : y = y')
    (hz : z = z') :
    (D.castOb φ hx hy) ≫ᵈ (D.castOb ψ rfl hz) = D.castOb (φ ≫ᵈ D.castOb ψ hy.symm rfl) hx hz := by
  cases hx; cases hy; cases hz; rfl

end CastOb

end DisplayedStruct

open scoped Displayed in
/-- A category displayed over `A`: objects over each `a : A`, and morphisms lying over each base
morphism `f : a ⟶ a'`.

The coherence laws are ordinary equalities. Both sides of each law lie over base morphisms that are
*equal but not syntactically identical* (e.g. `𝟙ᵈ x ≫ᵈ φ` lies over `𝟙 a ≫ f` whereas `φ` lies over
`f`), so the left-hand side is transported into the right-hand side's type with
`DisplayedStruct.castHom`. See `Displayed.id_comp_heq`, `Displayed.comp_id_heq` and
`Displayed.assoc_heq` for the `HEq` restatements. -/
structure Displayed (A : Type u₁) [Category.{v₁} A] extends
    DisplayedStruct.{v₁, u₁, v₂, u₂} A where
  -- The fields below spell the displayed identity as the bare field `id` rather than `𝟙ᵈ`: the
  -- `𝟙ᵈ` notation leaves the underlying `DisplayedStruct` to be inferred, which the elaborator
  -- cannot yet do from inside the declaration of `Displayed` itself.
  /-- Left unit law: casting `𝟙ᵈ x ≫ᵈ φ` along `𝟙 a ≫ f = f` gives back `φ`. -/
  id_comp : ∀ {a a' : A} {f : a ⟶ a'} {x : Ob a} {y : Ob a'} (φ : Hom f x y),
    toDisplayedStruct.castHom (id x ≫ᵈ φ) = φ
  /-- Right unit law: casting `φ ≫ᵈ 𝟙ᵈ y` along `f ≫ 𝟙 a' = f` gives back `φ`. -/
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {x : Ob a} {y : Ob a'} (φ : Hom f x y),
    toDisplayedStruct.castHom (φ ≫ᵈ id y) = φ
  /-- Associativity: casting `(φ ≫ᵈ ψ) ≫ᵈ χ` along `(f ≫ g) ≫ h = f ≫ g ≫ h` gives
  `φ ≫ᵈ (ψ ≫ᵈ χ)`. -/
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {h : a'' ⟶ a'''}
    {x : Ob a} {y : Ob a'} {z : Ob a''} {w : Ob a'''}
    (φ : Hom f x y) (ψ : Hom g y z) (χ : Hom h z w),
    toDisplayedStruct.castHom ((φ ≫ᵈ ψ) ≫ᵈ χ) = φ ≫ᵈ (ψ ≫ᵈ χ)

namespace Displayed

-- The laws are `simp` lemmas. Their left-hand sides are headed by `castHom`, whose equality
-- argument is matched up to proof irrelevance, so they fire for *any* proof of the relevant base
-- equation, not just the one written in the field.
attribute [simp] Displayed.id_comp Displayed.comp_id Displayed.assoc

variable (D : Displayed A)

section HEqAxioms

variable {a a' a'' a''' : A}

/-- `HEq` form of the left unit law. -/
theorem id_comp_heq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    𝟙ᵈ x ≫ᵈ φ ≍ φ :=
  (D.castHom_eq_iff_heq _).mp (D.id_comp φ)

/-- `HEq` form of the right unit law. -/
theorem comp_id_heq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    φ ≫ᵈ 𝟙ᵈ y ≍ φ :=
  (D.castHom_eq_iff_heq _).mp (D.comp_id φ)

/-- `HEq` form of associativity. -/
theorem assoc_heq {f : a ⟶ a'} {g : a' ⟶ a''} {h : a'' ⟶ a'''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} {w : D.Ob a'''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) (χ : z ⟶[h] w) :
    (φ ≫ᵈ ψ) ≫ᵈ χ ≍ φ ≫ᵈ (ψ ≫ᵈ χ) :=
  (D.castHom_eq_iff_heq _).mp (D.assoc φ ψ χ)

/-- The left unit law with the cast on the right-hand side. This is the `simp`-normal form: it
rewrites a composite into a single morphism. -/
@[simp]
theorem id_comp' {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    𝟙ᵈ x ≫ᵈ φ = D.castHom φ :=
  eq_of_heq ((D.id_comp_heq φ).trans (D.castHom_heq φ (Category.id_comp f).symm).symm)

/-- The right unit law with the cast on the right-hand side. This is the `simp`-normal form: it
rewrites a composite into a single morphism. -/
@[simp]
theorem comp_id' {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    φ ≫ᵈ 𝟙ᵈ y = D.castHom φ :=
  eq_of_heq ((D.comp_id_heq φ).trans (D.castHom_heq φ (Category.comp_id f).symm).symm)

/-- Associativity with the cast on the right-hand side. -/
@[simp]
theorem assoc' {f : a ⟶ a'} {g : a' ⟶ a''} {h : a'' ⟶ a'''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} {w : D.Ob a'''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) (χ : z ⟶[h] w) :
    (φ ≫ᵈ ψ) ≫ᵈ χ = D.castHom (φ ≫ᵈ (ψ ≫ᵈ χ)) :=
  eq_of_heq ((D.assoc_heq φ ψ χ).trans (D.castHom_heq _ (Category.assoc f g h).symm).symm)

end HEqAxioms

section Fiber

/-- The fiber of `D` over `a`: objects lying over `a`, with vertical morphisms (over `𝟙 a`). -/
def Fiber (D : Displayed A) (a : A) : Type u₂ := D.Ob a

/-- The fiber over `a` is a category, with vertical composition given by `castHom`-adjusted
displayed composition. -/
instance (a : A) : Category.{v₂} (D.Fiber a) where
  Hom x y := (x ⟶[𝟙 a] y)
  id x := 𝟙ᵈ x
  comp φ ψ := D.castHom (φ ≫ᵈ ψ)

/-- Unfolding lemma for fiber morphisms. -/
theorem Fiber.hom_def (a : A) (x y : D.Fiber a) : (x ⟶ y) = (x ⟶[𝟙 a] y) := rfl

/-- Unfolding lemma for the fiber identity. Not a global `@[simp]` lemma: rewriting `𝟙 x` to
`𝟙ᵈ x` blocks the category's own `id_comp`/`comp_id` simp lemmas from firing. -/
theorem Fiber.id_def (a : A) (x : D.Fiber a) : 𝟙 x = 𝟙ᵈ x := rfl

/-- Unfolding lemma for fiber composition. Deliberately *not* a global `@[simp]` lemma: unfolding
`≫` into `castHom` obscures proofs that are better done in fiber-category (`eqToHom`) vocabulary.
Apply it explicitly with `simp only [Fiber.comp_def]` when the displayed composite is wanted. -/
theorem Fiber.comp_def {a : A} {x y z : D.Fiber a} (φ : x ⟶ y) (ψ : y ⟶ z) :
    φ ≫ ψ = D.castHom (φ ≫ᵈ ψ) := rfl

end Fiber

section Total

/-- The total category of `D`: pairs `⟨a, x⟩` with `a : A` and `x : D.Ob a`. -/
def Total (D : Displayed A) := Σ a : A, D.Ob a

/-- An object of the total category. Because `Total` is a `def`, the anonymous constructor
`⟨a, x⟩` elaborates at the unfolded `Σ`-type and then loses the `Category` instance; `D.tot x`
produces a term whose type is syntactically `D.Total`, so `⟶`, `≫` and `𝟙` all work on it. -/
def tot (D : Displayed A) {a : A} (x : D.Ob a) : D.Total := ⟨a, x⟩

@[simp] theorem tot_fst {a : A} (x : D.Ob a) : (D.tot x).1 = a := rfl
@[simp] theorem tot_snd {a : A} (x : D.Ob a) : (D.tot x).2 = x := rfl

/-- A morphism in the total category of `D`: a base morphism together with a displayed morphism
lying over it. -/
structure Total.Hom {D : Displayed A} (x y : D.Total) where
  /-- The base component. -/
  base : x.1 ⟶ y.1
  /-- The displayed component, lying over `base`. -/
  fiber : x.2 ⟶[base] y.2

/-- Hom-extensionality for the total category. -/
theorem Total.hom_ext {x y : D.Total} {F G : Total.Hom x y} (h₁ : F.base = G.base)
    (h₂ : F.fiber ≍ G.fiber) : F = G := by
  obtain ⟨fb, ff⟩ := F
  obtain ⟨gb, gf⟩ := G
  subst h₁
  obtain rfl := eq_of_heq h₂
  rfl

/-- The total category structure: a morphism `⟨a, x⟩ ⟶ ⟨a', y⟩` is a base morphism `f : a ⟶ a'`
together with a displayed morphism over it. -/
instance : Category D.Total where
  Hom x y := Total.Hom x y
  id x := ⟨𝟙 x.1, 𝟙ᵈ x.2⟩
  comp F G := ⟨F.base ≫ G.base, F.fiber ≫ᵈ G.fiber⟩
  id_comp F := Total.hom_ext D (Category.id_comp F.base) (D.id_comp_heq F.fiber)
  comp_id F := Total.hom_ext D (Category.comp_id F.base) (D.comp_id_heq F.fiber)
  assoc F G H :=
    Total.hom_ext D (Category.assoc F.base G.base H.base) (D.assoc_heq F.fiber G.fiber H.fiber)

@[simp]
theorem Total.id_base (x : D.Total) : (𝟙 x : x ⟶ x).base = 𝟙 x.1 := rfl

@[simp]
theorem Total.id_fiber (x : D.Total) : (𝟙 x : x ⟶ x).fiber = 𝟙ᵈ x.2 := rfl

@[simp]
theorem Total.comp_base {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).base = F.base ≫ G.base := rfl

@[simp]
theorem Total.comp_fiber {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).fiber = F.fiber ≫ᵈ G.fiber := rfl

/-- A morphism of the total category, assembled from a base morphism and a displayed morphism over
it. Unlike the anonymous constructor, its declared result type is syntactically `_ ⟶ _`, which is
what `rw`/`simp`/`@[reassoc]` need. -/
def totalMk (D : Displayed A) {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : D.tot x ⟶ D.tot y := ⟨f, φ⟩

@[simp] theorem totalMk_base {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).base = f := rfl

@[simp] theorem totalMk_fiber {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).fiber = φ := rfl

@[simp] theorem totalMk_comp {a a' a'' : A} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (f : a ⟶ a') (φ : x ⟶[f] y) (g : a' ⟶ a'') (ψ : y ⟶[g] z) :
    D.totalMk f φ ≫ D.totalMk g ψ = D.totalMk (f ≫ g) (φ ≫ᵈ ψ) := rfl

/-- A *vertical* morphism of the total category: the image of a fiber morphism. -/
def totalVert (D : Displayed A) {a : A} {x y : D.Fiber a} (β : x ⟶ y) : D.tot x ⟶ D.tot y :=
  D.totalMk (𝟙 a) β

@[simp] theorem totalVert_base {a : A} {x y : D.Fiber a} (β : x ⟶ y) :
    (D.totalVert β).base = 𝟙 a := rfl

@[simp] theorem totalVert_fiber {a : A} {x y : D.Fiber a} (β : x ⟶ y) :
    (D.totalVert β).fiber = β := rfl

@[simp] theorem totalVert_id {a : A} (x : D.Fiber a) : D.totalVert (𝟙 x) = 𝟙 (D.tot x) := rfl

@[simp] theorem Total.eqToHom_base {x y : D.Total} (h : x = y) :
    (eqToHom h).base = eqToHom (congrArg Sigma.fst h) := by subst h; simp

@[simp] theorem totalVert_comp {a : A} {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.totalVert (β ≫ γ) = D.totalVert β ≫ D.totalVert γ :=
  Total.hom_ext D (by simp) (by
    change β ≫ γ ≍ β ≫ᵈ γ
    simp only [Fiber.comp_def]
    exact D.castHom_heq _ _)

/-- **Total-category bridge.** A `HEq` between displayed morphisms with common endpoints follows
from an equality of the corresponding morphisms of the (honest) total category. This lets one
discharge heterogeneous coherence goals by ordinary `Category` calculations in `D.Total` instead of
by hand-written `heq_comp` chains. -/
theorem heq_of_totalHom_eq {a a' : A} {x : D.Ob a} {y : D.Ob a'} {u v : a ⟶ a'}
    {Φ : x ⟶[u] y} {Ψ : x ⟶[v] y} (h : D.totalMk u Φ = D.totalMk v Ψ) : Φ ≍ Ψ := by
  have h' : (⟨u, Φ⟩ : Total.Hom (D := D) (D.tot x) (D.tot y)) = ⟨v, Ψ⟩ := h
  injection h' with _ h₂

/-- The projection of the total category to the base. -/
def π (D : Displayed A) : D.Total ⥤ A where
  obj x := x.1
  map F := F.base
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem π_obj (x : D.Total) : (D.π).obj x = x.1 := rfl
@[simp] theorem π_map {x y : D.Total} (F : x ⟶ y) : (D.π).map F = F.base := rfl

/-- The inclusion of the fiber over `a` into the total category. -/
def ι (D : Displayed A) (a : A) : D.Fiber a ⥤ D.Total where
  obj x := D.tot x
  map β := D.totalVert β
  map_id _ := rfl
  map_comp _ _ := D.totalVert_comp _ _

@[simp] theorem ι_obj (a : A) (x : D.Fiber a) : (D.ι a).obj x = D.tot x := rfl
@[simp] theorem ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) : (D.ι a).map β = D.totalVert β := rfl

@[simp]
theorem π_map_ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) :
    (D.π).map ((D.ι a).map β) = 𝟙 a := rfl

end Total

end Displayed

end Nfib
