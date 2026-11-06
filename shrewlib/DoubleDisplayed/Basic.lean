import Displayed.Displayed.Basic

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
* vertical functors `DoubleDisplayed.VertFunctor`, whose functoriality is a rewrite rule.

The double-level `IsOpcartesian` and `IsCartesian` structures are in
`DoubleDisplayed/Cartesian.lean` and the total displayed category in `DoubleDisplayed/Total.lean`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

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
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'), comp (id c) θ = θ := by intros; rfl
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : Ob b} {c' : Ob b'} (θ : Hom g c c'), comp θ (id c') = θ := by intros; rfl
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {f'' : a'' ⟶ a'''}
    {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''} {b''' : B.Ob a'''}
    {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {g'' : b'' ⟶[f''] b'''}
    {c : Ob b} {c' : Ob b'} {c'' : Ob b''} {c''' : Ob b'''}
    (θ : Hom g c c') (θ' : Hom g' c' c'') (θ'' : Hom g'' c'' c'''),
    comp (comp θ θ') θ'' = comp θ (comp θ' θ'') := by intros; rfl

attribute [rewrite_rule] DoubleDisplayed.id_comp DoubleDisplayed.comp_id DoubleDisplayed.assoc

namespace DoubleDisplayed

/-- Notation for the doubly displayed identity. -/
scoped notation "𝟙ᵈᵈ" => DoubleDisplayed.id _

/-- Notation for doubly displayed composition. -/
scoped notation:80 θ:81 " ≫ᵈᵈ " θ':80 => DoubleDisplayed.comp _ θ θ'

/-- Notation for a doubly displayed hom-type: `c ⟶[[g]] c'` is the type of doubly displayed
morphisms from `c` to `c'` lying over the `B`-morphism `g`. -/
scoped notation:10 c " ⟶[[" g "]] " c' => DoubleDisplayed.Hom _ g c c'

/-- Doubly displayed categories are determined by their objects, morphisms, identities and
composition, compared heterogeneously since their types depend on the objects and morphisms. (The
kernel can reject an `rfl` between two doubly displayed categories that it accepts on each
component.) -/
theorem ext_heq {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (hOb : @C.Ob = @D.Ob)
    (hHom : @C.Hom ≍ @D.Hom) (hid : @C.id ≍ @D.id) (hcomp : @C.comp ≍ @D.comp) : C = D := by
  obtain ⟨Ob, Hom, id, comp, _, _, _⟩ := C
  obtain ⟨Ob', Hom', id', comp', _, _, _⟩ := D
  -- Restated on the fields, so that the substitutions do not go through projections of `mk`,
  -- which the rules on `DoubleDisplayed.comp` and `DoubleDisplayed.id` would rewrite.
  change @Ob = @Ob' at hOb
  subst hOb
  change @Hom ≍ @Hom' at hHom
  obtain rfl := eq_of_heq hHom
  change @id ≍ @id' at hid
  obtain rfl := eq_of_heq hid
  change @comp ≍ @comp' at hcomp
  obtain rfl := eq_of_heq hcomp
  rfl

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

section VertFunctor

/-- A *vertical functor* between doubly displayed categories over `B`: it acts over `B` on the
nose. -/
structure VertFunctor (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)
    (D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B) where
  /-- The action on objects, fiberwise over `B`. -/
  obj : {a : A} → {b : B.Ob a} → C.Ob b → D.Ob b
  /-- The action on morphisms, over the same `B`-morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} → {g : b ⟶[f] b'} →
    {c : C.Ob b} → {c' : C.Ob b'} → (c ⟶[[g]] c') → ((obj c) ⟶[[g]] (obj c'))
  /-- Preserves identities. -/
  map_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), map (C.id c) = D.id (obj c) := by intros; rfl
  /-- Preserves composition. -/
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c''),
    map (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ' := by intros; rfl

attribute [rewrite_rule] VertFunctor.map_id VertFunctor.map_comp

namespace VertFunctor

/-- Extensionality: two vertical functors agreeing on objects (pointwise) and morphisms (up to
`≍`, since their types involve the actions on objects) are equal. -/
theorem ext {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
    {D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B} {F G : VertFunctor C D}
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
def id (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) : VertFunctor C C where
  obj c := c
  map θ := θ

/-- Composition of vertical functors. -/
def comp {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
    {D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B}
    {E : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₅, u₅} B}
    (F : VertFunctor C D)
    (G : VertFunctor D E) : VertFunctor C E where
  obj c := G.obj (F.obj c)
  map θ := G.map (F.map θ)

/-- Vertical functors restrict to ordinary functors on fibers. -/
def fiber {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
    {D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B} (F : VertFunctor C D) {a : A}
    (b : B.Ob a) : C.Fiber b ⥤ D.Fiber b where
  obj c := F.obj c
  map θ := F.map θ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem fiber_obj {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
    {D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B} (F : VertFunctor C D)
    {a : A} (b : B.Ob a) (c : C.Fiber b) : (F.fiber b).obj c = F.obj c := rfl

@[simp] theorem fiber_map {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
    {D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₄, u₄} B} (F : VertFunctor C D)
    {a : A} {b : B.Ob a} {c c' : C.Fiber b} (θ : c ⟶ c') : (F.fiber b).map θ = F.map θ := rfl

end VertFunctor

end VertFunctor


end DoubleDisplayed
