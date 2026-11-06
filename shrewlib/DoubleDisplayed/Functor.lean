import DoubleDisplayed.Basic

/-!
# Doubly displayed functors

For a displayed functor `H : DispFunctor u B B'` over `u : A ⥤ A'`, a *doubly displayed functor*
`DDFunctor H C C'` from `C : DoubleDisplayed B` to `C' : DoubleDisplayed B'` sends objects over
`b` to objects over `H b`, and morphisms over `g` to morphisms over `H g`. As for `DispFunctor`,
its laws are stated with the functor laws of `H` as rules, so that `H (B.id b)` is `B'.id (H b)`
and `H (g ≫ᵈ g')` is `H g ≫ᵈ H g'`, and they are rules too.

The vertical functors `VertFunctor C D` of `DoubleDisplayed/Basic.lean` are the doubly displayed
functors over the identity of `B`, up to unfolding `DispFunctor.id B`.

A category `C'` doubly displayed over `B'` reindexes along `H` to `C'.reindex H` over `B`, whose
objects over `b` are those of `C'` over `H b`, and whose morphisms over `g` are those of `C'` over
`H g`. Its laws hold by `rfl`, by the functor laws of `H`, and `C'.reindexLift H` is the doubly
displayed functor over `H` that is the identity on objects and morphisms.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ v₇ u₇ v₈ u₈ v₉ u₉

open CategoryTheory Displayed

open scoped Displayed

namespace DoubleDisplayed

open scoped DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₂, u₂} A}
  {A' : Type u₄} [Category.{v₄} A'] {B' : Displayed.{v₅, u₅} A'}

/-- A doubly displayed functor over a displayed functor `H` from `B` to `B'`: objects over `b` go
to objects over `H b`, and morphisms over `g` to morphisms over `H g`. -/
structure DDFunctor {u : A ⥤ A'} (H : DispFunctor u B B')
    (C : DoubleDisplayed.{v₃, u₃} B)
    (C' : DoubleDisplayed.{v₆, u₆} B') where
  /-- The action on objects. -/
  obj : {a : A} → {b : B.Ob a} → C.Ob b → C'.Ob (H.obj b)
  /-- The action on morphisms, over the image of the `B`-morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} → {g : b ⟶[f] b'} →
    {c : C.Ob b} → {c' : C.Ob b'} → (c ⟶[[g]] c') → (obj c ⟶[[H.map g]] obj c')
  map_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), map (C.id c) = C'.id (obj c) := by intros; rfl
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} {g : b ⟶[f] b'} {g' : b' ⟶[f'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : c ⟶[[g]] c') (θ' : c' ⟶[[g']] c''),
    map (θ ≫ᵈᵈ θ') = map θ ≫ᵈᵈ map θ' := by intros; rfl

attribute [rewrite_rule] DDFunctor.map_id DDFunctor.map_comp

namespace DDFunctor

variable {u : A ⥤ A'} {H : DispFunctor u B B'} {C : DoubleDisplayed.{v₃, u₃} B}
  {C' : DoubleDisplayed.{v₆, u₆} B'}

/-- Doubly displayed functors are determined by their actions on objects and morphisms. -/
theorem ext {F G : DDFunctor H C C'}
    (hobj : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), F.obj c = G.obj c)
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
      {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c'), F.map θ ≍ G.map θ) : F = G := by
  obtain ⟨Fo, Fm, _, _⟩ := F
  obtain ⟨Go, Gm, _, _⟩ := G
  obtain rfl : @Fo = @Go := by funext a b c; exact hobj c
  obtain rfl : @Fm = @Gm := by funext a a' f b b' g c c' θ; exact eq_of_heq (hmap θ)
  rfl

/-- The identity doubly displayed functor, over the identity displayed functor. -/
protected def id (C : DoubleDisplayed.{v₃, u₃} B) :
    DDFunctor (DispFunctor.id B) C C where
  obj c := c
  map θ := θ

/-- Composition of doubly displayed functors, over the composite displayed functor. -/
def comp {A'' : Type u₇} [Category.{v₇} A''] {B'' : Displayed.{v₈, u₈} A''} {u' : A' ⥤ A''}
    {H' : DispFunctor u' B' B''} {C'' : DoubleDisplayed.{v₉, u₉} B''}
    (F : DDFunctor H C C') (G : DDFunctor H' C' C'') : DDFunctor (H.comp H') C C'' where
  obj c := G.obj (F.obj c)
  map θ := G.map (F.map θ)

/-- A doubly displayed functor restricts to functors between the fibers. -/
def fiber (F : DDFunctor H C C') {a : A} (b : B.Ob a) : C.Fiber b ⥤ C'.Fiber (H.obj b) where
  obj c := F.obj c
  map θ := F.map θ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem fiber_obj (F : DDFunctor H C C') {a : A} (b : B.Ob a) (c : C.Fiber b) :
    (F.fiber b).obj c = F.obj c := rfl

@[simp] theorem fiber_map (F : DDFunctor H C C') {a : A} {b : B.Ob a} {c c' : C.Fiber b}
    (θ : c ⟶ c') : (F.fiber b).map θ = F.map θ := rfl

end DDFunctor

/-! ## Reindexing -/

section Reindex

variable {u : A ⥤ A'}

/-- **The reindexing of `C'` along `H`**: objects over `b` are the objects of `C'` over `H b`, and
morphisms over `g` are the morphisms of `C'` over `H g`. -/
def reindex (C' : DoubleDisplayed.{v₆, u₆} B') (H : DispFunctor u B B') :
    DoubleDisplayed.{v₆, u₆} B where
  Ob b := C'.Ob (H.obj b)
  Hom g c c' := C'.Hom (H.map g) c c'
  id c := C'.id c
  comp θ θ' := C'.comp θ θ'

/-- The doubly displayed functor over `H` from the reindexing of `C'` along `H` to `C'`: the
identity on objects and morphisms. -/
def reindexLift (C' : DoubleDisplayed.{v₆, u₆} B') (H : DispFunctor u B B') :
    DDFunctor H (C'.reindex H) C' where
  obj c := c
  map θ := θ

end Reindex

end DoubleDisplayed
