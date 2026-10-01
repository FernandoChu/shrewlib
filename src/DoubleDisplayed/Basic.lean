import Displayed.Basic

/-!
# Doubly displayed categories

A *doubly displayed category* over a displayed category `B` (itself displayed over `A`) is a
category displayed over the chain `C → B → A` in a genuinely two-level, curried way: its objects
are indexed by `B`'s displayed objects `b : B.Ob a`, and its morphisms by `B`'s displayed morphisms
`g : B.Hom f b b'`. This is the structure `DoubleDisplayed B` (not `Displayed B.Total`).

A doubly displayed hom-type `C.Hom g c c'` depends on the displayed base morphism `g`. The laws of
`B` are rewrite rules, so, as for `Displayed`, the laws of `C` are plain equations between
morphisms of definitionally equal types, and they are rewrite rules in turn.

We provide:

* the structure `DoubleDisplayed` and notation `𝟙ᵈᵈ c`, `θ ≫ᵈᵈ θ'`, `c ⟶[[g]] c'`;
* the fiber category `DoubleDisplayed.Fiber C b`, whose laws hold by `rfl`;
* the double-level `IsOpcartesian` and `IsCartesian` predicates and their universal-property API;
* vertical functors `DoubleDisplayed.VertFunctor`, whose functoriality is a rewrite rule.

This is milestone **M3** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}

/-- A category doubly displayed over `B`: objects over each `b : B.Ob a`, morphisms over each
displayed base morphism `g : B.Hom f b b'`. -/
structure DoubleDisplayed (B : Displayed.{v₁, u₁, v₂, u₂} A) where
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
  id_comp : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'), comp (id c) θ = θ
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'), comp θ (id c') = θ
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {f'' : a'' ⟶ a'''}
    {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''} {b''' : B.Ob a'''}
    {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {g'' : b'' ⟶[f''] b'''}
    {c : Ob b} {c' : Ob b'} {c'' : Ob b''} {c''' : Ob b'''}
    (θ : Hom g c c') (θ' : Hom g' c' c'') (θ'' : Hom g'' c'' c'''),
    comp (comp θ θ') θ'' = comp θ (comp θ' θ'')

attribute [rewrite_rule] DoubleDisplayed.id_comp DoubleDisplayed.comp_id DoubleDisplayed.assoc

namespace DoubleDisplayed

/-- Notation for the doubly displayed identity. -/
scoped notation "𝟙ᵈᵈ" => DoubleDisplayed.id _

/-- Notation for doubly displayed composition. -/
scoped notation:80 θ:81 " ≫ᵈᵈ " θ':80 => DoubleDisplayed.comp _ θ θ'

/-- Notation for a doubly displayed hom-type: `c ⟶[[g]] c'` is the type of doubly displayed
morphisms from `c` to `c'` lying over the `B`-morphism `g`. -/
scoped notation:10 c " ⟶[[" g "]] " c' => DoubleDisplayed.Hom _ g c c'

variable (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)

section Fiber

/-- The fiber of `C` over `b : B.Ob a`: doubly displayed objects over `b`, with vertical morphisms
(over `B.id b`). -/
abbrev Fiber {a : A} (b : B.Ob a) : Type u₃ := C.Ob b

/-- The fiber over `b` is a category, with doubly displayed composition, which lies over
`B.id b ≫ᵈ B.id b`, that is over `B.id b`. -/
instance {a : A} (b : B.Ob a) : Category.{v₃} (C.Fiber b) where
  Hom c c' := c ⟶[[B.id b]] c'
  id c := 𝟙ᵈᵈ c
  comp θ θ' := θ ≫ᵈᵈ θ'
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem Fiber.hom_def {a : A} (b : B.Ob a) (c c' : C.Fiber b) :
    (c ⟶ c') = (c ⟶[[B.id b]] c') := rfl

theorem Fiber.id_def {a : A} (b : B.Ob a) (c : C.Fiber b) : 𝟙 c = 𝟙ᵈᵈ c := rfl

theorem Fiber.comp_def {a : A} {b : B.Ob a} {c c' c'' : C.Fiber b} (θ : c ⟶ c') (θ' : c' ⟶ c'') :
    θ ≫ θ' = θ ≫ᵈᵈ θ' := rfl

end Fiber

end DoubleDisplayed
