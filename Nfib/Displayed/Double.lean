import Nfib.Displayed.Basic

/-!
# Doubly displayed categories

A *doubly displayed category* over a displayed category `B` (itself displayed over `A`) is a
category displayed over the chain `C → B → A` in a genuinely two-level, curried way: its objects
are indexed by `B`'s displayed objects `b : B.Ob a`, and its morphisms by `B`'s displayed morphisms
`g : B.Hom f b b'`. This is the structure `DoubleDisplayed B` (not `Displayed B.Total`).

A doubly displayed hom-type `C.Hom g c c'` depends on the displayed base morphism `g`, which in
turn lives over a base morphism `f`. Following `Nfib.Displayed`, we split the definition in two so
that the coherence laws can be stated as equalities rather than `HEq`s:

* `DoubleDisplayedStruct` carries only the data (`Ob`, `Hom`, `id`, `comp`);
* `DoubleDisplayedStruct.castHom` transports along an equality `hf : f = f'` of base morphisms
  *together with* an equality `hg : B.castHom g hf = g'` of `B`-morphisms — note that this second
  hypothesis is an honest `Eq`, since `B.castHom g hf` already lives in the type of `g'`. Both
  default to `cat_disch`, and the goals they leave are exactly the `simp` lemmas of
  `Nfib.Displayed`;
* `DoubleDisplayed extends DoubleDisplayedStruct` states the laws as equalities, and they are
  `simp` lemmas.

The `simp`-set conventions are those documented in `Nfib.Displayed.Basic`: generalise the
category-level `simp` set, and push `castHom` outwards (`DoubleDisplayedStruct.castHom_comp`,
`DoubleDisplayedStruct.comp_castHom`, `VertFunctor.map_castHom`).

`HEq` survives only in the congruence lemmas `DoubleDisplayedStruct.heq_comp` and friends, and in
`IsOpcartesian.hom_ext_heq` / `IsCartesian.hom_ext_heq`: those vary the *objects* `b`, `c`, which a
transport along base morphisms cannot express.

We provide:

* the structures `DoubleDisplayedStruct` / `DoubleDisplayed` and notation `𝟙ᵈᵈ c`, `θ ≫ᵈᵈ θ'`;
* the cast operator `DoubleDisplayedStruct.castHom` with its full bridge API;
* the fiber category `DoubleDisplayed.Fiber C b`;
* the double-level `IsOpcartesian` predicate and its `desc` API;
* vertical functors `DoubleDisplayed.VertFunctor`.

This is milestone **M3** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A}

/-- The *data* of a category doubly displayed over `B`: objects over each `b : B.Ob a`, morphisms
over each displayed base morphism `g : B.Hom f b b'`, identities and composition — but none of the
coherence laws. Stands to `DoubleDisplayed` as `DisplayedStruct` stands to `Displayed`. -/
structure DoubleDisplayedStruct (B : Displayed A) where
  /-- Objects lying over `b : B.Ob a`. -/
  Ob : {a : A} → B.Ob a → Type u₃
  /-- Morphisms lying over `g : B.Hom f b b'`. -/
  Hom : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} →
    (b ⟶[f] b') → Ob b → Ob b' → Type v₃
  /-- The identity over `B.id b`. -/
  id : {a : A} → {b : B.Ob a} → (c : Ob b) → Hom (B.id b) c c
  /-- Composition, lying over `g ≫ᵈ g'`. -/
  comp : {a a' a'' : A} → {f : a ⟶ a'} → {f' : a' ⟶ a''} →
    {b : B.Ob a} → {b' : B.Ob a'} → {b'' : B.Ob a''} →
    {g : b ⟶[f] b'} → {g' : b' ⟶[f'] b''} →
    {c : Ob b} → {c' : Ob b'} → {c'' : Ob b''} →
    Hom g c c' → Hom g' c' c'' → Hom (g ≫ᵈ g') c c''

namespace DoubleDisplayed

/-- Notation for the doubly displayed identity. -/
scoped notation "𝟙ᵈᵈ" => Nfib.DoubleDisplayedStruct.id _

/-- Notation for doubly displayed composition. -/
scoped notation:80 θ:81 " ≫ᵈᵈ " θ':80 => Nfib.DoubleDisplayedStruct.comp _ θ θ'

/-- Notation for a doubly displayed hom-type: `c ⟶[[g]] c'` is the type of doubly displayed
morphisms from `c` to `c'` lying over the `B`-morphism `g`. Mirrors `x ⟶[f] y` for `Displayed`. -/
scoped notation:10 c " ⟶[[" g "]] " c' => Nfib.DoubleDisplayedStruct.Hom _ g c c'

end DoubleDisplayed

namespace DoubleDisplayedStruct

open scoped DoubleDisplayed

variable (C : DoubleDisplayedStruct B)

section CastHom

variable {a a' a'' : A}

/-- Transport a doubly displayed morphism along an equality `hf : f = f'` of base morphisms
together with the induced equality `hg : B.castHom g hf = g'` of `B`-morphisms.

Note that `hg` is an honest equation rather than a `HEq`: `B.castHom g hf` already lives in
`B.Hom f' b b'`, the type of `g'`. Both arguments default to `cat_disch`, and the goals they leave
are exactly the displayed `simp` lemmas of `Nfib.Displayed`. -/
def castHom {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {g' : b ⟶[f'] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') (hf : f = f' := by cat_disch)
    (hg : B.castHom g hf = g' := by cat_disch) : c ⟶[[g']] c' :=
  cast (by subst hf; subst hg; rfl) θ

theorem castHom_heq {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') (hf : f = f')
    (hg : B.castHom g hf = g') : C.castHom θ hf hg ≍ θ :=
  cast_heq _ _

@[simp]
theorem castHom_rfl {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {c : C.Ob b}
    {c' : C.Ob b'} (θ : c ⟶[[g]] c') : C.castHom θ rfl rfl = θ :=
  eq_of_heq (C.castHom_heq θ rfl rfl)

@[simp]
theorem castHom_castHom {f f' f'' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {g'' : b ⟶[f''] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c')
    (hf : f = f') (hg : B.castHom g hf = g') (hf' : f' = f'') (hg' : B.castHom g' hf' = g'') :
    C.castHom (C.castHom θ hf hg) hf' hg'
      = C.castHom θ (hf.trans hf') (by subst hf; subst hg; subst hf'; exact hg') :=
  eq_of_heq <| (C.castHom_heq _ _ _).trans <| (C.castHom_heq _ _ _).trans
    (C.castHom_heq _ _ _).symm

@[simp]
theorem castHom_self {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {c : C.Ob b}
    {c' : C.Ob b'} (θ : c ⟶[[g]] c') (hf : f = f) (hg : B.castHom g hf = g) :
    C.castHom θ hf hg = θ :=
  eq_of_heq (C.castHom_heq θ hf hg)

/-- `castHom` as an equivalence of hom-types. -/
def castHomEquiv {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {c : C.Ob b} {c' : C.Ob b'} (hf : f = f') (hg : B.castHom g hf = g') :
    (c ⟶[[g]] c') ≃ (c ⟶[[g']] c') where
  toFun θ := C.castHom θ hf hg
  invFun θ := C.castHom θ hf.symm (by subst hf; subst hg; rfl)
  left_inv _ := eq_of_heq ((C.castHom_heq _ _ _).trans (C.castHom_heq _ _ _))
  right_inv _ := eq_of_heq ((C.castHom_heq _ _ _).trans (C.castHom_heq _ _ _))

@[simp]
theorem castHomEquiv_apply {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {c : C.Ob b} {c' : C.Ob b'} (hf : f = f') (hg : B.castHom g hf = g')
    (θ : c ⟶[[g]] c') : C.castHomEquiv hf hg θ = C.castHom θ hf hg := rfl

theorem heq_iff_castHom_eq {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'} {ψ : c ⟶[[g']] c'}
    (hf : f = f') (hg : B.castHom g hf = g') : θ ≍ ψ ↔ C.castHom θ hf hg = ψ := by
  constructor
  · intro h; exact eq_of_heq ((C.castHom_heq θ hf hg).trans h)
  · intro h; exact (C.castHom_heq θ hf hg).symm.trans (heq_of_eq h)

theorem castHom_eq_iff_heq {f f' : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {g' : b ⟶[f'] b'} {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'} {ψ : c ⟶[[g']] c'}
    (hf : f = f') (hg : B.castHom g hf = g') : C.castHom θ hf hg = ψ ↔ θ ≍ ψ :=
  (C.heq_iff_castHom_eq hf hg).symm

/-- Pushing a `castHom` in the left factor out of a composite. -/
@[simp]
theorem castHom_comp {f f' : a ⟶ a'} {f₀ : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}
    {g : b ⟶[f] b'} {g' : b ⟶[f'] b'} {g₀ : b' ⟶[f₀] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (ψ : c' ⟶[[g₀]] c'') (hf : f = f')
    (hg : B.castHom g hf = g') : (C.castHom θ hf hg) ≫ᵈᵈ ψ = C.castHom (θ ≫ᵈᵈ ψ) := by
  subst hf; subst hg; rfl

/-- Pushing a `castHom` in the right factor out of a composite. -/
@[simp]
theorem comp_castHom {f : a ⟶ a'} {f₀ f₀' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}
    {g : b ⟶[f] b'} {g₀ : b' ⟶[f₀] b''} {g₀' : b' ⟶[f₀'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (ψ : c' ⟶[[g₀]] c'') (hf : f₀ = f₀')
    (hg : B.castHom g₀ hf = g₀') : θ ≫ᵈᵈ (C.castHom ψ hf hg) = C.castHom (θ ≫ᵈᵈ ψ) := by
  subst hf; subst hg; rfl

/-- Congruence for doubly displayed composition: base/object equalities plus `≍`s of the `B`-base
morphisms and of the factors give a `≍` of composites. The heterogeneity here is over *objects*
(`p₁` vs `p₂`), which `castHom` — a transport along base morphisms only — cannot express. -/
theorem heq_comp {f₁ f₂ : a ⟶ a'} {f₁' f₂' : a' ⟶ a''} {b : B.Ob a} {p₁ p₂ : B.Ob a'}
    {b'' : B.Ob a''} {g₁ : b ⟶[f₁] p₁} {g₂ : b ⟶[f₂] p₂} {g₁' : p₁ ⟶[f₁'] b''}
    {g₂' : p₂ ⟶[f₂'] b''} {c : C.Ob b} {d₁ : C.Ob p₁} {d₂ : C.Ob p₂} {c'' : C.Ob b''}
    {θ₁ : c ⟶[[g₁]] d₁} {θ₂ : c ⟶[[g₂]] d₂} {θ₁' : d₁ ⟶[[g₁']] c''} {θ₂' : d₂ ⟶[[g₂']] c''}
    (hf : f₁ = f₂) (hf' : f₁' = f₂') (hp : p₁ = p₂) (hd : d₁ ≍ d₂) (hg : g₁ ≍ g₂) (hg' : g₁' ≍ g₂')
    (hθ : θ₁ ≍ θ₂) (hθ' : θ₁' ≍ θ₂') : θ₁ ≫ᵈᵈ θ₁' ≍ θ₂ ≫ᵈᵈ θ₂' := by
  subst hf hf' hp
  obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hg'
  obtain rfl := eq_of_heq hθ
  obtain rfl := eq_of_heq hθ'
  rfl

/-- Fully general congruence for doubly displayed composition: every datum may vary. -/
theorem heq_comp' {a a' a'' : A} {f₁ f₂ : a ⟶ a'} {f₁' f₂' : a' ⟶ a''} {b₁ b₂ : B.Ob a}
    {p₁ p₂ : B.Ob a'} {q₁ q₂ : B.Ob a''} {g₁ : b₁ ⟶[f₁] p₁} {g₂ : b₂ ⟶[f₂] p₂}
    {g₁' : p₁ ⟶[f₁'] q₁} {g₂' : p₂ ⟶[f₂'] q₂} {c₁ : C.Ob b₁} {c₂ : C.Ob b₂}
    {d₁ : C.Ob p₁} {d₂ : C.Ob p₂} {e₁ : C.Ob q₁} {e₂ : C.Ob q₂}
    {θ₁ : c₁ ⟶[[g₁]] d₁} {θ₂ : c₂ ⟶[[g₂]] d₂} {θ₁' : d₁ ⟶[[g₁']] e₁} {θ₂' : d₂ ⟶[[g₂']] e₂}
    (hf : f₁ = f₂) (hf' : f₁' = f₂') (hb : b₁ = b₂) (hp : p₁ = p₂) (hq : q₁ = q₂)
    (hc : c₁ ≍ c₂) (hd : d₁ ≍ d₂) (he : e₁ ≍ e₂) (hg : g₁ ≍ g₂) (hg' : g₁' ≍ g₂')
    (hθ : θ₁ ≍ θ₂) (hθ' : θ₁' ≍ θ₂') : θ₁ ≫ᵈᵈ θ₁' ≍ θ₂ ≫ᵈᵈ θ₂' := by
  subst hf; subst hf'; subst hb; subst hp; subst hq
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hg'
  obtain rfl := eq_of_heq hθ
  obtain rfl := eq_of_heq hθ'
  rfl

/-- Congruence for composition with a fixed first factor and a fully-varying second factor
(including its codomain). -/
theorem heq_comp_right {a a' a'' : A} {f : a ⟶ a'} {f₁ f₂ : a' ⟶ a''} {b : B.Ob a} {p : B.Ob a'}
    {q₁ q₂ : B.Ob a''} {g : b ⟶[f] p} {g₁ : p ⟶[f₁] q₁} {g₂ : p ⟶[f₂] q₂} {c : C.Ob b}
    {d : C.Ob p} {e₁ : C.Ob q₁} {e₂ : C.Ob q₂} {θ : c ⟶[[g]] d} {ψ₁ : d ⟶[[g₁]] e₁}
    {ψ₂ : d ⟶[[g₂]] e₂} (hf : f₁ = f₂) (hq : q₁ = q₂) (hg : g₁ ≍ g₂) (he : e₁ ≍ e₂)
    (hψ : ψ₁ ≍ ψ₂) : θ ≫ᵈᵈ ψ₁ ≍ θ ≫ᵈᵈ ψ₂ := by
  subst hf hq
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hψ
  rfl

/-- Congruence for composition with a fully-varying first factor (including its domain) and a fixed
second factor. -/
theorem heq_comp_left {a a' a'' : A} {f₁ f₂ : a ⟶ a'} {f' : a' ⟶ a''} {b₁ b₂ : B.Ob a} {p : B.Ob a'}
    {q : B.Ob a''} {g₁ : b₁ ⟶[f₁] p} {g₂ : b₂ ⟶[f₂] p} {g' : p ⟶[f'] q} {c₁ : C.Ob b₁}
    {c₂ : C.Ob b₂} {d : C.Ob p} {e : C.Ob q} {θ₁ : c₁ ⟶[[g₁]] d} {θ₂ : c₂ ⟶[[g₂]] d}
    {ψ : d ⟶[[g']] e} (hf : f₁ = f₂) (hb : b₁ = b₂) (hg : g₁ ≍ g₂) (hc : c₁ ≍ c₂) (hθ : θ₁ ≍ θ₂) :
    θ₁ ≫ᵈᵈ ψ ≍ θ₂ ≫ᵈᵈ ψ := by
  subst hf hb
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hθ
  rfl

end CastHom

section EqToHom

variable {a a' a'' : A}

/-- Transport a doubly displayed *object* along an equality of the `B`-object it lies over.

This one really is a transport: an equality of `B`-objects changes the *type* `C.Ob b`, and no
morphism can stand in for that. -/
def castObj {b b' : B.Ob a} (c : C.Ob b) (hb : b = b' := by cat_disch) : C.Ob b' :=
  match b', hb with
  | _, rfl => c

@[simp]
theorem castObj_rfl {b : B.Ob a} (c : C.Ob b) : C.castObj c rfl = c := rfl

theorem castObj_heq {b b' : B.Ob a} (c : C.Ob b) (hb : b = b') : C.castObj c hb ≍ c := by
  cases hb; rfl

@[simp]
theorem castObj_self {b : B.Ob a} (c : C.Ob b) (hb : b = b) : C.castObj c hb = c :=
  eq_of_heq (C.castObj_heq c hb)

@[simp]
theorem castObj_castObj {b b' b'' : B.Ob a} (c : C.Ob b) (hb : b = b') (hb' : b' = b'') :
    C.castObj (C.castObj c hb) hb' = C.castObj c (hb.trans hb') := by cases hb; cases hb'; rfl

theorem heq_iff_castObj_eq {b b' : B.Ob a} {c : C.Ob b} {d : C.Ob b'} (hb : b = b') :
    c ≍ d ↔ C.castObj c hb = d := by cases hb; exact heq_iff_eq

theorem castObj_eq_iff_heq {b b' : B.Ob a} {c : C.Ob b} {d : C.Ob b'} (hb : b = b') :
    C.castObj c hb = d ↔ c ≍ d := (C.heq_iff_castObj_eq hb).symm

/-- The doubly displayed morphism induced by an equality of objects lying over a common `b`.

This is the `eqToHom` of the fiber over `b`, but with its type stated syntactically as a doubly
displayed hom-type. It replaces a transport along an equality of endpoints: rather than moving a
morphism, it supplies the connecting morphism, so that endpoint discrepancies are absorbed by
*composition* in the usual `eqToHom`-conjugation idiom. -/
def eqToHom {b : B.Ob a} {c c' : C.Ob b} (h : c = c') : c ⟶[[B.id b]] c' :=
  match c', h with
  | _, rfl => C.id c

@[simp]
theorem eqToHom_refl {b : B.Ob a} (c : C.Ob b) : C.eqToHom (rfl : c = c) = 𝟙ᵈᵈ c := rfl

theorem eqToHom_heq_id {b : B.Ob a} {c c' : C.Ob b} (h : c = c') : C.eqToHom h ≍ 𝟙ᵈᵈ c := by
  cases h; rfl

theorem eqToHom_heq_id_cod {b : B.Ob a} {c c' : C.Ob b} (h : c = c') : C.eqToHom h ≍ 𝟙ᵈᵈ c' := by
  cases h; rfl

/-- The doubly displayed morphism induced by an equality of the *`B`-objects* the endpoints lie
over: it lies over `B`'s own vertical `eqToHom`, and its codomain is `castObj`.

This is the `eqToHom`-style replacement for a transport along the `B`-base. -/
def eqToHomBase {b b' : B.Ob a} (c : C.Ob b) (hb : b = b') :
    c ⟶[[CategoryTheory.eqToHom (C := B.Fiber a) hb]] C.castObj c hb :=
  match b', hb with
  | _, rfl => 𝟙ᵈᵈ c

@[simp]
theorem eqToHomBase_refl {b : B.Ob a} (c : C.Ob b) : C.eqToHomBase c rfl = 𝟙ᵈᵈ c := rfl

theorem eqToHomBase_heq_id {b b' : B.Ob a} (c : C.Ob b) (hb : b = b') :
    C.eqToHomBase c hb ≍ 𝟙ᵈᵈ c := by cases hb; rfl

end EqToHom

end DoubleDisplayedStruct

open scoped DoubleDisplayed in
/-- A category doubly displayed over `B`: objects over each `b : B.Ob a`, morphisms over each
displayed base morphism `g : B.Hom f b b'`.

As for `Displayed`, the coherence laws are equalities: the left-hand side is transported into the
right-hand side's type by `DoubleDisplayedStruct.castHom`, whose two proof obligations are filled
in by `cat_disch` — they are precisely the corresponding laws of `B`. -/
structure DoubleDisplayed (B : Displayed A) extends
    DoubleDisplayedStruct.{v₁, u₁, v₂, u₂, v₃, u₃} B where
  /-- Left unit law: casting `𝟙ᵈᵈ c ≫ᵈᵈ θ` along `𝟙 a ≫ f = f` and `B.id b ≫ᵈ g = g` gives `θ`. -/
  id_comp : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'),
    toDoubleDisplayedStruct.castHom (comp (id c) θ) = θ
  /-- Right unit law: casting `θ ≫ᵈᵈ 𝟙ᵈᵈ c'` along `f ≫ 𝟙 a' = f` and `g ≫ᵈ B.id b' = g` gives
  `θ`. -/
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'),
    toDoubleDisplayedStruct.castHom (comp θ (id c')) = θ
  /-- Associativity. -/
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {f'' : a'' ⟶ a'''}
    {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''} {b''' : B.Ob a'''}
    {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {g'' : b'' ⟶[f''] b'''}
    {c : Ob b} {c' : Ob b'} {c'' : Ob b''} {c''' : Ob b'''}
    (θ : Hom g c c') (θ' : Hom g' c' c'') (θ'' : Hom g'' c'' c'''),
    toDoubleDisplayedStruct.castHom (comp (comp θ θ') θ'') = comp θ (comp θ' θ'')

namespace DoubleDisplayed

attribute [simp] DoubleDisplayed.id_comp DoubleDisplayed.comp_id DoubleDisplayed.assoc

variable (C : DoubleDisplayed B)

section HEqAxioms

variable {a a' a'' a''' : A}

/-- `HEq` form of the left unit law. -/
theorem id_comp_heq {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : 𝟙ᵈᵈ c ≫ᵈᵈ θ ≍ θ :=
  (C.castHom_eq_iff_heq _ _).mp (C.id_comp θ)

/-- `HEq` form of the right unit law. -/
theorem comp_id_heq {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : θ ≫ᵈᵈ 𝟙ᵈᵈ c' ≍ θ :=
  (C.castHom_eq_iff_heq _ _).mp (C.comp_id θ)

/-- `HEq` form of associativity. -/
theorem assoc_heq {f : a ⟶ a'} {f' : a' ⟶ a''} {f'' : a'' ⟶ a'''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} {b''' : B.Ob a'''} {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''}
    {g'' : b'' ⟶[f''] b'''} {c : C.Ob b} {c' : C.Ob b'} {c'' : C.Ob b''} {c''' : C.Ob b'''}
    (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') (θ'' : c'' ⟶[[g'']] c''') :
    (θ ≫ᵈᵈ θ') ≫ᵈᵈ θ'' ≍ θ ≫ᵈᵈ (θ' ≫ᵈᵈ θ'') :=
  (C.castHom_eq_iff_heq _ _).mp (C.assoc θ θ' θ'')

/-- The left unit law with the cast on the right-hand side. -/
@[simp]
theorem id_comp' {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : 𝟙ᵈᵈ c ≫ᵈᵈ θ = C.castHom θ :=
  eq_of_heq ((C.id_comp_heq θ).trans (C.castHom_heq θ _ _).symm)

/-- The right unit law with the cast on the right-hand side. -/
@[simp]
theorem comp_id' {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : θ ≫ᵈᵈ 𝟙ᵈᵈ c' = C.castHom θ :=
  eq_of_heq ((C.comp_id_heq θ).trans (C.castHom_heq θ _ _).symm)

/-- Associativity with the cast on the right-hand side. -/
@[simp]
theorem assoc' {f : a ⟶ a'} {f' : a' ⟶ a''} {f'' : a'' ⟶ a'''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} {b''' : B.Ob a'''} {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''}
    {g'' : b'' ⟶[f''] b'''} {c : C.Ob b} {c' : C.Ob b'} {c'' : C.Ob b''} {c''' : C.Ob b'''}
    (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c'') (θ'' : c'' ⟶[[g'']] c''') :
    (θ ≫ᵈᵈ θ') ≫ᵈᵈ θ'' = C.castHom (θ ≫ᵈᵈ (θ' ≫ᵈᵈ θ'')) :=
  eq_of_heq ((C.assoc_heq θ θ' θ'').trans (C.castHom_heq _ _ _).symm)

/-- Precomposing with an `eqToHom` does not change a morphism, heterogeneously. The prime
distinguishes this from `CategoryTheory.eqToHom_comp_heq`, which downstream files use unqualified
while also having `DoubleDisplayed` open. -/
theorem eqToHom_comp_heq' {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c d : C.Ob b} {c' : C.Ob b'} (h : c = d) (θ : d ⟶[[g]] c') :
    C.eqToHom h ≫ᵈᵈ θ ≍ θ := by cases h; exact C.id_comp_heq θ

/-- Postcomposing with an `eqToHom` does not change a morphism, heterogeneously. Primed for the
same reason as `eqToHom_comp_heq'`. -/
theorem comp_eqToHom_heq' {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' d' : C.Ob b'} (θ : c ⟶[[g]] c') (h : c' = d') :
    θ ≫ᵈᵈ C.eqToHom h ≍ θ := by cases h; exact C.comp_id_heq θ

/-- Postcomposing with an `eqToHomBase` does not change a morphism, heterogeneously. -/
theorem comp_eqToHomBase_heq {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' b₂' : B.Ob a'}
    {g : b ⟶[f] b'} {c : C.Ob b} (c' : C.Ob b') (hb : b' = b₂') (θ : c ⟶[[g]] c') :
    θ ≫ᵈᵈ C.eqToHomBase c' hb ≍ θ := by cases hb; exact C.comp_id_heq θ

end HEqAxioms

section Fiber

/-- The fiber of `C` over `b : B.Ob a`: doubly displayed objects over `b`, with vertical morphisms
(over `B.id b`). -/
def Fiber (C : DoubleDisplayed B) {a : A} (b : B.Ob a) : Type u₃ := C.Ob b

/-- The fiber over `b` is a category, with composition given by `castHom`-adjusted doubly displayed
composition. -/
instance {a : A} (b : B.Ob a) : Category.{v₃} (C.Fiber b) where
  Hom c c' := (c ⟶[[B.id b]] c')
  id c := 𝟙ᵈᵈ c
  comp θ θ' := C.castHom (θ ≫ᵈᵈ θ')

/-- Unfolding lemma for fiber morphisms. -/
theorem Fiber.hom_def {a : A} (b : B.Ob a) (c c' : C.Fiber b) :
    (c ⟶ c') = (c ⟶[[B.id b]] c') := rfl

/-- Unfolding lemma for the fiber identity. Not a global `@[simp]` lemma (cf. `Displayed`). -/
theorem Fiber.id_def {a : A} (b : B.Ob a) (c : C.Fiber b) : 𝟙 c = 𝟙ᵈᵈ c := rfl

/-- Unfolding lemma for fiber composition. Not a global `@[simp]` lemma (cf. `Displayed`). -/
theorem Fiber.comp_def {a : A} {b : B.Ob a} {c c' c'' : C.Fiber b} (θ : c ⟶ c') (θ' : c' ⟶ c'') :
    θ ≫ θ' = C.castHom (θ ≫ᵈᵈ θ') := rfl

end Fiber

section Opcartesian

/-- `θ : c ⟶[g] c'` is *opcartesian* at the double level: every doubly displayed map out of `c`
over `g ≫ᵈ g'` factors uniquely through `θ` over `g'`. -/
def IsOpcartesian {C : DoubleDisplayed B} {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'}
    {g : b ⟶[f] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : Prop :=
  ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} (g' : b' ⟶[f'] b'')
    (c'' : C.Ob b'') (χ : c ⟶[[g ≫ᵈ g']] c''),
    ∃! ψ : c' ⟶[[g']] c'', θ ≫ᵈᵈ ψ = χ

namespace IsOpcartesian

variable {C} {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
  {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'}

/-- The unique factorization of `χ` through an opcartesian `θ`. -/
noncomputable def desc (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    (g' : b' ⟶[f'] b'') {c'' : C.Ob b''} (χ : c ⟶[[g ≫ᵈ g']] c'') : c' ⟶[[g']] c'' :=
  (H g' c'' χ).choose

@[simp]
theorem desc_fac (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    (g' : b' ⟶[f'] b'') {c'' : C.Ob b''} (χ : c ⟶[[g ≫ᵈ g']] c'') :
    θ ≫ᵈᵈ H.desc g' χ = χ :=
  (H g' c'' χ).choose_spec.1

/-- Any factorization of `χ` through `θ` agrees with `desc`. -/
theorem desc_uniq (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    {g' : b' ⟶[f'] b''} {c'' : C.Ob b''} {χ : c ⟶[[g ≫ᵈ g']] c''}
    (ψ : c' ⟶[[g']] c'') (hψ : θ ≫ᵈᵈ ψ = χ) : ψ = H.desc g' χ :=
  (H g' c'' χ).choose_spec.2 ψ hψ

/-- Two maps out of `c'` that agree after precomposition with an opcartesian `θ` are equal. -/
theorem hom_ext (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    {g' : b' ⟶[f'] b''} {c'' : C.Ob b''} {ψ ψ' : c' ⟶[[g']] c''}
    (h : θ ≫ᵈᵈ ψ = θ ≫ᵈᵈ ψ') : ψ = ψ' :=
  (H.desc_uniq ψ rfl).trans (H.desc_uniq ψ' h.symm).symm

/-- Heterogeneous uniqueness: two morphisms out of the codomains of heterogeneously-equal
opcartesian morphisms `θ ≍ θ₂` that agree (heterogeneously) after precomposition are themselves
heterogeneously equal. -/
theorem hom_ext_heq {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' p : B.Ob a'} {g : b ⟶[f] b'}
    {g₂ : b ⟶[f] p} {c : C.Ob b} {c' : C.Ob b'} {c'₂ : C.Ob p}
    {θ : c ⟶[[g]] c'} {θ₂ : c ⟶[[g₂]] c'₂} (H : IsOpcartesian θ)
    {a'' : A} {f' : a' ⟶ a''} {q q₂ : B.Ob a''} {g' : b' ⟶[f'] q} {g'₂ : p ⟶[f'] q₂}
    {d : C.Ob q} {d₂ : C.Ob q₂} {ψ : c' ⟶[[g']] d} {ψ' : c'₂ ⟶[[g'₂]] d₂}
    (hb : b' = p) (hg : g ≍ g₂) (hc' : c' ≍ c'₂) (hθ : θ ≍ θ₂)
    (hq : q = q₂) (hg' : g' ≍ g'₂) (hd : d ≍ d₂)
    (hcomp : θ ≫ᵈᵈ ψ ≍ θ₂ ≫ᵈᵈ ψ') : ψ ≍ ψ' := by
  subst hb
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hc'
  obtain rfl := eq_of_heq hθ
  subst hq
  obtain rfl := eq_of_heq hg'
  obtain rfl := eq_of_heq hd
  exact heq_of_eq (H.hom_ext (eq_of_heq hcomp))

end IsOpcartesian

/-- `θ : c ⟶[g] c'` is *cartesian* at the double level, among vertical morphisms (over `𝟙 a`):
every doubly displayed map into `c'` over `g₀ ≫ᵈ g` factors uniquely through `θ` over `g₀`. -/
def IsCartesian {C : DoubleDisplayed B} {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'}
    {s : C.Ob b} {t : C.Ob b'} (θ : s ⟶[[g]] t) : Prop :=
  ∀ {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) (s₀ : C.Ob b₀) (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t),
    ∃! ξ : s₀ ⟶[[g₀]] s, ξ ≫ᵈᵈ θ = χ

namespace IsCartesian

variable {C} {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'} {s : C.Ob b} {t : C.Ob b'}
  {θ : s ⟶[[g]] t}

/-- The unique factorization of `χ` through a cartesian `θ`. -/
noncomputable def lift (H : IsCartesian θ) {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀}
    (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t) : s₀ ⟶[[g₀]] s :=
  (H g₀ s₀ χ).choose

@[simp]
theorem lift_fac (H : IsCartesian θ) {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀}
    (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t) : H.lift g₀ χ ≫ᵈᵈ θ = χ :=
  (H g₀ s₀ χ).choose_spec.1

/-- Any factorization of `χ` through `θ` agrees with `lift`. -/
theorem lift_uniq (H : IsCartesian θ) {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀}
    {χ : s₀ ⟶[[g₀ ≫ᵈ g]] t} (ξ : s₀ ⟶[[g₀]] s) (hξ : ξ ≫ᵈᵈ θ = χ) : ξ = H.lift g₀ χ :=
  (H g₀ s₀ χ).choose_spec.2 ξ hξ

/-- Two maps into `s` that agree after postcomposition with a cartesian `θ` are equal. -/
theorem hom_ext (H : IsCartesian θ) {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀}
    {ξ ξ' : s₀ ⟶[[g₀]] s} (h : ξ ≫ᵈᵈ θ = ξ' ≫ᵈᵈ θ) : ξ = ξ' :=
  (H.lift_uniq ξ rfl).trans (H.lift_uniq ξ' h.symm).symm

/-- Heterogeneous uniqueness for cartesian morphisms `θ ≍ θ₂`, allowing the second morphism (and
the test morphism) to lie over a different base morphism (via `hf`/`hf₀`). -/
theorem hom_ext_heq {a : A} {f₂ f₀₂ : a ⟶ a} {b b' p : B.Ob a} {g : b ⟶[𝟙 a] b'}
    {g₂ : p ⟶[f₂] b'} {s : C.Ob b} {s₂ : C.Ob p} {t : C.Ob b'} {θ : s ⟶[[g]] t}
    {θ₂ : s₂ ⟶[[g₂]] t} (H : IsCartesian θ) {b₀ q : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b}
    {g₀₂ : q ⟶[f₀₂] p} {u : C.Ob b₀} {u₂ : C.Ob q} {ξ : u ⟶[[g₀]] s} {ξ' : u₂ ⟶[[g₀₂]] s₂}
    (hf : (𝟙 a : a ⟶ a) = f₂) (hf₀ : (𝟙 a : a ⟶ a) = f₀₂)
    (hb : b = p) (hg : g ≍ g₂) (hs : s ≍ s₂) (hθ : θ ≍ θ₂)
    (hb₀ : b₀ = q) (hg₀ : g₀ ≍ g₀₂) (hu : u ≍ u₂)
    (hcomp : ξ ≫ᵈᵈ θ ≍ ξ' ≫ᵈᵈ θ₂) : ξ ≍ ξ' := by
  subst hf hf₀ hb
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hθ
  subst hb₀
  obtain rfl := eq_of_heq hg₀
  obtain rfl := eq_of_heq hu
  exact heq_of_eq (H.hom_ext (eq_of_heq hcomp))

end IsCartesian

end Opcartesian

section VertFunctor

/-- A *vertical functor* between doubly displayed categories over `B`: it acts over `B` on the
nose (no base transport), so no casts appear in its functoriality laws. -/
structure VertFunctor (C D : DoubleDisplayed B) where
  /-- The action on objects, fiberwise over `B`. -/
  obj : {a : A} → {b : B.Ob a} → C.Ob b → D.Ob b
  /-- The action on morphisms, over the same `B`-morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} → {g : b ⟶[f] b'} →
    {c : C.Ob b} → {c' : C.Ob b'} → (c ⟶[[g]] c') → ((obj c) ⟶[[g]] (obj c'))
  /-- Preserves identities. -/
  map_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), map (C.id c) = D.id (obj c)
  /-- Preserves composition. -/
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c''),
    map (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ'

namespace VertFunctor

/-- A vertical functor commutes with `castHom`: this is the "push `castHom` outwards" normal form
for `map`. -/
@[simp]
theorem map_castHom {C D : DoubleDisplayed B} (F : VertFunctor C D) {a a' : A} {f f' : a ⟶ a'}
    {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {g' : b ⟶[f'] b'} {c : C.Ob b}
    {c' : C.Ob b'} (θ : c ⟶[[g]] c') (hf : f = f') (hg : B.castHom g hf = g') :
    F.map (C.castHom θ hf hg) = D.castHom (F.map θ) hf hg := by
  subst hf; subst hg; rfl

/-- `map` is a congruence for heterogeneous equality of morphisms (allowing the endpoints and the
`B`-base to vary). -/
theorem map_heq {C D : DoubleDisplayed B} (F : VertFunctor C D) {a a' : A} {f f' : a ⟶ a'}
    {b b₂ : B.Ob a} {b' b'₂ : B.Ob a'} {g : b ⟶[f] b'} {g' : b₂ ⟶[f'] b'₂}
    {c : C.Ob b} {c' : C.Ob b'} {c₂ : C.Ob b₂} {c'₂ : C.Ob b'₂}
    {θ : c ⟶[[g]] c'} {θ' : c₂ ⟶[[g']] c'₂}
    (hb : b = b₂) (hb' : b' = b'₂) (hf : f = f') (hg : g ≍ g') (hc : c ≍ c₂) (hc' : c' ≍ c'₂)
    (h : θ ≍ θ') : F.map θ ≍ F.map θ' := by
  subst hb hb' hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hc'
  obtain rfl := eq_of_heq h
  rfl

/-- Extensionality: two vertical functors agreeing on objects (pointwise) and morphisms (up to
`≍`) are equal. -/
theorem ext {C D : DoubleDisplayed B} {F G : VertFunctor C D}
    (hobj : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), F.obj c = G.obj c)
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
      {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c'), F.map θ ≍ G.map θ) : F = G := by
  obtain ⟨Fo, Fm, _, _⟩ := F
  obtain ⟨Go, Gm, _, _⟩ := G
  have ho : @Fo = @Go := by funext a b c; exact hobj c
  subst ho
  have hm : @Fm = @Gm := by funext a a' f b b' g c c' θ; exact eq_of_heq (hmap θ)
  subst hm
  rfl

/-- The identity vertical functor. -/
def id (C : DoubleDisplayed B) : VertFunctor C C where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of vertical functors. -/
def comp {C D E : DoubleDisplayed B} (F : VertFunctor C D) (G : VertFunctor D E) :
    VertFunctor C E where
  obj c := G.obj (F.obj c)
  map θ := G.map (F.map θ)
  map_id c := by rw [F.map_id, G.map_id]
  map_comp θ θ' := by rw [F.map_comp, G.map_comp]

@[simp] theorem id_obj (C : DoubleDisplayed B) {a : A} {b : B.Ob a} (c : C.Ob b) :
    (VertFunctor.id C).obj c = c := rfl

@[simp] theorem comp_obj {C D E : DoubleDisplayed B} (F : VertFunctor C D) (G : VertFunctor D E)
    {a : A} {b : B.Ob a} (c : C.Ob b) : (F.comp G).obj c = G.obj (F.obj c) := rfl

/-- Vertical functors preserving the fiber over `b` restrict to ordinary functors on fibers. -/
def fiber {C D : DoubleDisplayed B} (F : VertFunctor C D) {a : A} (b : B.Ob a) :
    C.Fiber b ⥤ D.Fiber b where
  obj c := F.obj c
  map θ := F.map θ
  map_id c := F.map_id c
  map_comp θ θ' := by
    change F.map (C.castHom _ _ _) = D.castHom _ _ _
    rw [F.map_castHom, F.map_comp]

@[simp] theorem fiber_obj {C D : DoubleDisplayed B} (F : VertFunctor C D) {a : A} (b : B.Ob a)
    (c : C.Fiber b) : (F.fiber b).obj c = F.obj c := rfl

@[simp] theorem fiber_map {C D : DoubleDisplayed B} (F : VertFunctor C D) {a : A} {b : B.Ob a}
    {c c' : C.Fiber b} (θ : c ⟶ c') : (F.fiber b).map θ = F.map θ := rfl

end VertFunctor

end VertFunctor

end DoubleDisplayed

end Nfib
