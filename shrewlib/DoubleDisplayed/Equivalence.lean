import DoubleDisplayed.Functor
import Mathlib.CategoryTheory.Iso

/-!
# Vertical natural transformations and equivalences of doubly displayed categories

The analogues one level up of the vertical natural transformations of
`Displayed/Displayed/Basic.lean` and the equivalences of `Displayed/Displayed/Equivalence.lean`,
for categories doubly displayed over `B`:

* vertical natural transformations `VertNatTrans F G` between vertical functors, with components
  over the identities of `B`, natural with respect to morphisms over arbitrary morphisms of `B`;
  they make `VertFunctor C D` a category, whose isomorphisms are the vertical natural isomorphisms
  (`VertNatIso.app`, `VertNatIso.ofComponents`);
* equivalences over `B` (`VertEquivalence C D`): vertical functors both ways, with a unit and a
  counit that are vertical natural isomorphisms.

The laws of the category of vertical functors hold by `rfl`, since composites of vertical functors
unfold to the composites of their actions.

All of these reindex along a displayed functor `H : B ⟶ B'` (`VertFunctor.reindex`,
`VertNatIso.reindex`, `VertEquivalence.reindex`), acting on the reindexings `C.reindex H` as on `C`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

open CategoryTheory Displayed

open scoped Displayed

namespace DoubleDisplayed

open scoped DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}
  {C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}

/-- A vertical natural transformation between vertical functors: its components lie over the
identities of `B`, and it is natural with respect to morphisms over arbitrary morphisms of `B`. -/
@[ext]
structure VertNatTrans (F G : VertFunctor C D) where
  /-- The components. -/
  app : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), F.obj c ⟶[[B.id b]] G.obj c
  naturality : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c'), F.map θ ≫ᵈᵈ app c' = app c ≫ᵈᵈ G.map θ

namespace VertNatTrans

/-- The identity vertical natural transformation. -/
protected def id (F : VertFunctor C D) : VertNatTrans F F where
  app c := 𝟙ᵈᵈ (F.obj c)
  naturality _ := rfl

/-- Vertical composition of vertical natural transformations. -/
def vcomp {F G H : VertFunctor C D} (η : VertNatTrans F G) (θ : VertNatTrans G H) :
    VertNatTrans F H where
  app c := η.app c ≫ᵈᵈ θ.app c
  naturality {_ _ _ _ _ _ c c'} φ :=
    ((congrArg (· ≫ᵈᵈ θ.app c') (η.naturality φ)).trans
      (congrArg (η.app c ≫ᵈᵈ ·) (θ.naturality φ)) :)

end VertNatTrans

/-- Vertical functors and vertical natural transformations form a category. -/
instance VertFunctor.category : Category (VertFunctor C D) where
  Hom F G := VertNatTrans F G
  id F := VertNatTrans.id F
  comp η θ := VertNatTrans.vcomp η θ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace VertNatTrans

variable {F G H : VertFunctor C D}

@[ext]
theorem ext' {η θ : F ⟶ G} (h : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), η.app c = θ.app c) :
    η = θ :=
  VertNatTrans.ext (by funext a b c; exact h c)

@[simp] theorem id_app {a : A} {b : B.Ob a} (c : C.Ob b) :
    VertNatTrans.app (𝟙 F) c = 𝟙ᵈᵈ (F.obj c) := rfl

@[simp] theorem comp_app (η : F ⟶ G) (θ : G ⟶ H) {a : A} {b : B.Ob a} (c : C.Ob b) :
    VertNatTrans.app (η ≫ θ) c = η.app c ≫ᵈᵈ θ.app c := rfl

end VertNatTrans

namespace VertNatIso

variable {F G : VertFunctor C D} (η : F ≅ G)

/-- The component of a vertical natural isomorphism, an isomorphism of the fiber. -/
@[simps]
def app {a : A} {b : B.Ob a} (c : C.Ob b) : (F.obj c : D.Fiber b) ≅ G.obj c where
  hom := η.hom.app c
  inv := η.inv.app c
  hom_inv_id := congrArg (fun t => VertNatTrans.app t c) η.hom_inv_id
  inv_hom_id := congrArg (fun t => VertNatTrans.app t c) η.inv_hom_id

/-- A vertical natural isomorphism from isomorphisms of the fibers, natural in morphisms over
arbitrary morphisms of `B`. -/
def ofComponents (app : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), (F.obj c : D.Fiber b) ≅ G.obj c)
    (naturality : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
      {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c'),
      F.map θ ≫ᵈᵈ (app c').hom = (app c).hom ≫ᵈᵈ G.map θ) : F ≅ G where
  hom := ⟨fun c => (app c).hom, naturality⟩
  inv :=
    { app := fun c => (app c).inv
      naturality := fun {_ _ _ _ _ _ c c'} θ =>
        ((congrArg (· ≫ᵈᵈ (G.map θ ≫ᵈᵈ (app c').inv)) (app c).inv_hom_id).symm.trans
          ((congrArg (fun t => (app c).inv ≫ᵈᵈ (t ≫ᵈᵈ (app c').inv)) (naturality θ)).symm.trans
            (congrArg (fun t => (app c).inv ≫ᵈᵈ (F.map θ ≫ᵈᵈ t)) (app c').hom_inv_id)) :) }
  hom_inv_id := VertNatTrans.ext' fun c => (app c).hom_inv_id
  inv_hom_id := VertNatTrans.ext' fun c => (app c).inv_hom_id

end VertNatIso

/-- **An equivalence over `B`** of doubly displayed categories: vertical functors both ways, with
a unit and a counit that are vertical natural isomorphisms. -/
structure VertEquivalence (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)
    (D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  /-- The functor. -/
  functor : VertFunctor C D
  /-- The inverse functor. -/
  inverse : VertFunctor D C
  /-- The unit. -/
  unitIso : VertFunctor.id C ≅ functor.comp inverse
  /-- The counit. -/
  counitIso : inverse.comp functor ≅ VertFunctor.id D

/-! ## Reindexing -/

section Reindex

variable {A' : Type u₄} [Category.{v₄} A'] {B' : Displayed.{v₄, u₄, v₅, u₅} A'} {u : A ⥤ A'}
  (H : DispFunctor u B B') {C' D' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₃, u₃} B'}

/-- A vertical functor over `B'`, reindexed along `H`: the same actions on objects and
morphisms. -/
def VertFunctor.reindex (F : VertFunctor C' D') : VertFunctor (C'.reindex H) (D'.reindex H) where
  obj c := F.obj c
  map θ := F.map θ
  map_id _ := rfl
  map_comp _ _ := rfl

theorem VertFunctor.reindex_comp {E' : DoubleDisplayed.{v₄, u₄, v₅, u₅, v₃, u₃} B'}
    (F : VertFunctor C' D') (G : VertFunctor D' E') :
    (F.comp G).reindex H = (F.reindex H).comp (G.reindex H) := rfl

theorem VertFunctor.reindex_id : (VertFunctor.id C').reindex H = VertFunctor.id (C'.reindex H) :=
  rfl

/-- A vertical natural isomorphism over `B'`, reindexed along `H`: the same components. -/
def VertNatIso.reindex {F G : VertFunctor C' D'} (η : F ≅ G) : F.reindex H ≅ G.reindex H :=
  VertNatIso.ofComponents
    (fun c =>
      { hom := η.hom.app c
        inv := η.inv.app c
        hom_inv_id := (VertNatIso.app η c).hom_inv_id
        inv_hom_id := (VertNatIso.app η c).inv_hom_id })
    (fun θ => η.hom.naturality θ)

/-- **An equivalence over `B'`, reindexed along `H`**, an equivalence over `B` of the
reindexings. -/
def VertEquivalence.reindex (e : VertEquivalence C' D') :
    VertEquivalence (C'.reindex H) (D'.reindex H) where
  functor := e.functor.reindex H
  inverse := e.inverse.reindex H
  unitIso := VertNatIso.reindex H e.unitIso
  counitIso := VertNatIso.reindex H e.counitIso

end Reindex

end DoubleDisplayed
