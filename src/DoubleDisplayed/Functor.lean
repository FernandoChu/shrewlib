import DoubleDisplayed.Basic

/-!
# Vertical functors between doubly displayed categories

The analogue of `Displayed/Functor.lean` one level up: functors between categories doubly
displayed over `B` acting over `B` on the nose, whose functoriality is a rewrite rule, with
identities, composites and their restrictions to fibers.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

namespace DoubleDisplayed

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}
  (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)

section VertFunctor

/-- A *vertical functor* between doubly displayed categories over `B`: it acts over `B` on the
nose. -/
structure VertFunctor (C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
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

attribute [rewrite_rule] VertFunctor.map_id VertFunctor.map_comp

namespace VertFunctor

/-- Extensionality: two vertical functors agreeing on objects (pointwise) and morphisms (up to
`≍`, since their types involve the actions on objects) are equal. -/
theorem ext {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} {F G : VertFunctor C D}
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
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of vertical functors. -/
def comp {C D E : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (F : VertFunctor C D)
    (G : VertFunctor D E) : VertFunctor C E where
  obj c := G.obj (F.obj c)
  map θ := G.map (F.map θ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Vertical functors restrict to ordinary functors on fibers. -/
def fiber {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (F : VertFunctor C D) {a : A}
    (b : B.Ob a) : C.Fiber b ⥤ D.Fiber b where
  obj c := F.obj c
  map θ := F.map θ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem fiber_obj {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (F : VertFunctor C D)
    {a : A} (b : B.Ob a) (c : C.Fiber b) : (F.fiber b).obj c = F.obj c := rfl

@[simp] theorem fiber_map {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (F : VertFunctor C D)
    {a : A} {b : B.Ob a} {c c' : C.Fiber b} (θ : c ⟶ c') : (F.fiber b).map θ = F.map θ := rfl

end VertFunctor

end VertFunctor

end DoubleDisplayed
