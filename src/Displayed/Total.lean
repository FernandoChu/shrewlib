import Displayed.Equivalence
import Mathlib.CategoryTheory.Equivalence

/-!
# The total category of a displayed category

The total category `D.Total` of `D : Displayed A` has as objects pairs `⟨a, x⟩` of `a : A` and
`x : D.Ob a`, and as morphisms pairs of a base morphism and a displayed morphism over it. Its laws
are those of `A` and `D`, which hold definitionally. The projection `π : D.Total ⥤ A` forgets the
displayed component, and `ι a : D.Fiber a ⥤ D.Total` includes the fiber over `a`.

Vertical functors and natural transformations induce functors and natural transformations between
total categories over `A` (`VertFunctor.totalFunctor`), and a vertical equivalence induces an
equivalence of total categories whose functors commute with the projections to `A`
(`VertEquivalence.total`).

`DoubleDisplayed/Total.lean` is the analogue one level up.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] (D : Displayed.{v₁, u₁, v₂, u₂} A)

section Total

/-- The total category of `D`: pairs `⟨a, x⟩` with `a : A` and `x : D.Ob a`. -/
def Total (D : Displayed.{v₁, u₁, v₂, u₂} A) := Σ a : A, D.Ob a

/-- An object of the total category. Its type is syntactically `D.Total`, so that `⟶`, `≫` and
`𝟙` elaborate on it. -/
def tot {a : A} (x : D.Ob a) : D.Total := ⟨a, x⟩

@[simp] theorem tot_fst {a : A} (x : D.Ob a) : (D.tot x).1 = a := rfl
@[simp] theorem tot_snd {a : A} (x : D.Ob a) : (D.tot x).2 = x := rfl

/-- A morphism in the total category of `D`: a base morphism together with a displayed morphism
lying over it. -/
structure Total.Hom {D : Displayed.{v₁, u₁, v₂, u₂} A} (x y : D.Total) where
  /-- The base component. -/
  base : x.1 ⟶ y.1
  /-- The displayed component, lying over `base`. -/
  fiber : x.2 ⟶[base] y.2

/-- The total category: its laws are those of `A` and `D`, which hold definitionally. -/
instance : Category D.Total where
  Hom x y := Total.Hom x y
  id x := ⟨𝟙 x.1, 𝟙ᵈ x.2⟩
  comp F G := ⟨F.base ≫ G.base, F.fiber ≫ᵈ G.fiber⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem Total.id_base (x : D.Total) : (𝟙 x : x ⟶ x).base = 𝟙 x.1 := rfl

@[simp] theorem Total.id_fiber (x : D.Total) : (𝟙 x : x ⟶ x).fiber = 𝟙ᵈ x.2 := rfl

@[simp] theorem Total.comp_base {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).base = F.base ≫ G.base := rfl

@[simp] theorem Total.comp_fiber {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).fiber = F.fiber ≫ᵈ G.fiber := rfl

/-- A morphism of the total category, assembled from a base morphism and a displayed morphism over
it. Unlike the anonymous constructor, its type is syntactically `_ ⟶ _`. -/
def totalMk {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a') (φ : x ⟶[f] y) :
    D.tot x ⟶ D.tot y := ⟨f, φ⟩

@[simp] theorem totalMk_base {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).base = f := rfl

@[simp] theorem totalMk_fiber {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).fiber = φ := rfl

theorem totalMk_comp {a a' a'' : A} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (f : a ⟶ a') (φ : x ⟶[f] y) (g : a' ⟶ a'') (ψ : y ⟶[g] z) :
    D.totalMk f φ ≫ D.totalMk g ψ = D.totalMk (f ≫ g) (φ ≫ᵈ ψ) := rfl

/-- A *vertical* morphism of the total category: the image of a fiber morphism. -/
def totalVert {a : A} {x y : D.Fiber a} (β : x ⟶ y) : D.tot x ⟶ D.tot y := D.totalMk (𝟙 a) β

theorem totalVert_id {a : A} (x : D.Fiber a) : D.totalVert (𝟙 x) = 𝟙 (D.tot x) := rfl

theorem totalVert_comp {a : A} {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.totalVert (β ≫ γ) = D.totalVert β ≫ D.totalVert γ := rfl

/-- The projection of the total category to the base. -/
def π : D.Total ⥤ A where
  obj x := x.1
  map F := F.base
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem π_obj (x : D.Total) : D.π.obj x = x.1 := rfl
@[simp] theorem π_map {x y : D.Total} (F : x ⟶ y) : D.π.map F = F.base := rfl

/-- The inclusion of the fiber over `a` into the total category. -/
def ι (a : A) : D.Fiber a ⥤ D.Total where
  obj x := D.tot x
  map β := D.totalVert β
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem ι_obj (a : A) (x : D.Fiber a) : (D.ι a).obj x = D.tot x := rfl
@[simp] theorem ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) : (D.ι a).map β = D.totalVert β := rfl

theorem π_map_ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) :
    D.π.map ((D.ι a).map β) = 𝟙 a := rfl

end Total


/-! ## Total functors -/

section Functors

variable {D} {E : Displayed.{v₁, u₁, v₃, u₃} A}

/-- The functor between total categories induced by a vertical functor. -/
def VertFunctor.total (F : VertFunctor D E) : D.Total ⥤ E.Total where
  obj X := ⟨X.1, F.obj X.2⟩
  map g := ⟨g.base, F.map g.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor induced by a vertical functor lies over `A`, strictly. -/
theorem VertFunctor.total_comp_π (F : VertFunctor D E) : F.total ⋙ E.π = D.π :=
  rfl

/-- The natural transformation between total functors induced by a vertical natural
transformation. Its components lie over identities. -/
def VertNatTrans.total {F G : VertFunctor D E} (η : F ⟶ G) : F.total ⟶ G.total where
  app X := ⟨𝟙 X.1, η.app X.2⟩
  naturality {X Y} g := (congrArg (Total.Hom.mk (x := F.total.obj X) (y := G.total.obj Y) g.base)
    (η.naturality g.fiber) :)

/-- Passing to total categories, as a functor. -/
@[simps]
def VertFunctor.totalFunctor : VertFunctor D E ⥤ (D.Total ⥤ E.Total) where
  obj F := F.total
  map η := VertNatTrans.total η
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The natural isomorphism between total functors induced by a vertical natural isomorphism. -/
def VertNatIso.total {F G : VertFunctor D E} (η : F ≅ G) : F.total ≅ G.total :=
  VertFunctor.totalFunctor.mapIso η

/-- The components of `VertNatIso.total` are vertical: they lie over identities. -/
theorem VertNatIso.π_map_total_hom {F G : VertFunctor D E} (η : F ≅ G) (X : D.Total) :
    E.π.map ((VertNatIso.total η).hom.app X) = 𝟙 X.1 :=
  rfl

/-- **A vertical equivalence induces an equivalence of the total categories over `A`**: its
functors commute with the projections to `A` (`VertEquivalence.total_functor_comp_π`), and the
components of its unit and counit lie over identities. -/
def VertEquivalence.total (e : VertEquivalence D E) : D.Total ≌ E.Total :=
  CategoryTheory.Equivalence.mk e.functor.total e.inverse.total (VertNatIso.total e.unitIso)
    (VertNatIso.total e.counitIso)

theorem VertEquivalence.total_functor_comp_π (e : VertEquivalence D E) :
    e.total.functor ⋙ E.π = D.π :=
  rfl

theorem VertEquivalence.total_inverse_comp_π (e : VertEquivalence D E) :
    e.total.inverse ⋙ D.π = E.π :=
  rfl

end Functors

end Displayed
