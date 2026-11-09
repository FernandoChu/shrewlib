import Displayed.Displayed.Total
import Displayed.Displayed.DisplayedCat

/-!
# Sections of a displayed category

A *section* of a displayed category `D` over `A` (`D.Section`) is an object `obj a` of `D` over each
object `a` of `A`, and a morphism `map f : obj a ⟶[f] obj a'` over each morphism `f`, compatible
with identities and composites. It is a functor `S.total : A ⥤ D.Total` over `A`, with
`S.total ⋙ D.π = 𝟭 A` by `rfl`.

Conversely, a functor `s : A ⥤ D.Total` over `A`, `s ⋙ D.π = 𝟭 A`, is a section
(`Section.ofFunctor`): the first component of `s.obj a` is `a` only propositionally, so the second
component, and those of the images of morphisms, are transported along these equalities
(`Section.castHom`). These are inverse (`Section.equivFunctor`): a section is recovered with the
same components, since the transports are then along `rfl`, and a functor up to the transports.

The sections of `D` form a category (`Section.category`), whose morphisms are the vertical natural
transformations (`Section.Hom`): a vertical morphism `S.obj a ⟶[𝟙 a] T.obj a` over each `a`,
natural in `a`. They reindex along `u : A ⟶ B` to sections of `DisplayedCat.pull u D`
(`Section.pull`).
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A]

/-- A section of `D`: an object over each object, and a morphism over each morphism, compatible
with identities and composites. -/
structure Section (D : Displayed.{v₂, u₂} A) where
  /-- The object over `a`. -/
  obj : ∀ a : A, D.Ob a
  /-- The morphism over `f`. -/
  map : ∀ {a a' : A} (f : a ⟶ a'), obj a ⟶[f] obj a'
  map_id : ∀ a : A, map (𝟙 a) = 𝟙ᵈ (obj a) := by intros; rfl
  map_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a''), map (f ≫ g) = map f ≫ᵈ map g := by
    intros; rfl

namespace Section

variable {D : Displayed.{v₂, u₂} A}

/-- Sections are equal if their objects are, and their morphisms heterogeneously. -/
theorem ext {S T : D.Section} (hobj : ∀ a, S.obj a = T.obj a)
    (hmap : ∀ {a a' : A} (f : a ⟶ a'), S.map f ≍ T.map f) : S = T := by
  obtain ⟨obj, map, _, _⟩ := S
  obtain ⟨obj', map', _, _⟩ := T
  obtain rfl : obj = obj' := funext hobj
  obtain rfl : @map = @map' := by
    funext a a' f
    exact eq_of_heq (hmap f)
  rfl

/-- The functor `A ⥤ D.Total` of a section. -/
def total (S : D.Section) : A ⥤ D.Total where
  obj a := D.tot (S.obj a)
  map f := D.totalMk f (S.map f)
  map_id a := congrArg (D.totalMk (𝟙 a)) (S.map_id a)
  map_comp f g := congrArg (D.totalMk (f ≫ g)) (S.map_comp f g)

/-- The functor of a section lies over `A`. -/
theorem total_comp_π (S : D.Section) : S.total ⋙ D.π = 𝟭 A :=
  rfl

/-- The transport of the fibre component of a morphism `F : x ⟶ y` of the total category, along
equalities of the first components of `x` and `y` with `a` and `a'`, to a morphism over `f`. -/
def castHom {a a' : A} {x y : D.Total} (hx : x.1 = a) (hy : y.1 = a') (F : x ⟶ y)
    {f : a ⟶ a'} (hf : F.base ≍ f) :
    (cast (congrArg D.Ob hx) x.2 : D.Ob a) ⟶[f] (cast (congrArg D.Ob hy) y.2 : D.Ob a') := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at hx hy
  subst hx hy
  obtain rfl := eq_of_heq hf
  exact F.fiber

theorem castHom_heq {a a' : A} {x y : D.Total} (hx : x.1 = a) (hy : y.1 = a') (F : x ⟶ y)
    {f : a ⟶ a'} (hf : F.base ≍ f) : castHom hx hy F hf ≍ F.fiber := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at hx hy
  subst hx hy
  obtain rfl := eq_of_heq hf
  rfl

/-- The objects transported along equalities of their bases are heterogeneously equal to them. -/
theorem cast_ob_heq {a b : A} (h : a = b) (x : D.Ob a) : (cast (congrArg D.Ob h) x : D.Ob b) ≍ x :=
  cast_heq _ _

/-- Identities over heterogeneously equal objects are heterogeneously equal. -/
theorem id_hcongr {a b : A} (h : a = b) {x : D.Ob a} {y : D.Ob b} (hxy : x ≍ y) :
    (𝟙ᵈ x) ≍ (𝟙ᵈ y) := by
  subst h
  obtain rfl := eq_of_heq hxy
  rfl

/-- Composites of heterogeneously equal morphisms are heterogeneously equal. -/
theorem comp_hcongr {a a' a'' b b' b'' : A} (ha : a = b) (ha' : a' = b') (ha'' : a'' = b'')
    {f : a ⟶ a'} {g : a' ⟶ a''} {f' : b ⟶ b'} {g' : b' ⟶ b''} (hf : f ≍ f') (hg : g ≍ g')
    {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''} {x' : D.Ob b} {y' : D.Ob b'} {z' : D.Ob b''}
    (hx : x ≍ x') (hy : y ≍ y') (hz : z ≍ z') {φ : x ⟶[f] y} {ψ : y ⟶[g] z} {φ' : x' ⟶[f'] y'}
    {ψ' : y' ⟶[g'] z'} (hφ : φ ≍ φ') (hψ : ψ ≍ ψ') : (φ ≫ᵈ ψ) ≍ (φ' ≫ᵈ ψ') := by
  subst ha ha' ha''
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hψ
  rfl

/-- The fibre components of equal morphisms of the total category are heterogeneously equal. -/
theorem fiber_heq_of_eq {x y : D.Total} {F G : x ⟶ y} (h : F = G) : F.fiber ≍ G.fiber := by
  subst h
  rfl

variable (s : A ⥤ D.Total)

/-- The first components of the values of a functor over `A` are the objects of `A`. -/
theorem fst_obj (h : s ⋙ D.π = 𝟭 A) (a : A) : (s.obj a).1 = a :=
  Functor.congr_obj h a

/-- The base components of the values of a functor over `A` are the morphisms of `A`. -/
theorem base_map (h : s ⋙ D.π = 𝟭 A) {a a' : A} (f : a ⟶ a') : (s.map f).base ≍ f :=
  Functor.hcongr_hom h f

/-- **The section of a functor over `A`**: its values, transported along the equalities of their
first components with the objects of `A`. -/
def ofFunctor (h : s ⋙ D.π = 𝟭 A) : D.Section where
  obj a := cast (congrArg D.Ob (fst_obj s h a)) (s.obj a).2
  map f := castHom (fst_obj s h _) (fst_obj s h _) (s.map f) (base_map s h f)
  map_id a := eq_of_heq ((castHom_heq _ _ _ _).trans ((fiber_heq_of_eq (s.map_id a)).trans
    (id_hcongr (fst_obj s h a) (cast_ob_heq (fst_obj s h a) _).symm)))
  map_comp f g := eq_of_heq ((castHom_heq _ _ _ _).trans ((fiber_heq_of_eq (s.map_comp f g)).trans
    (comp_hcongr (fst_obj s h _) (fst_obj s h _) (fst_obj s h _) (base_map s h f)
      (base_map s h g) (cast_ob_heq (fst_obj s h _) _).symm (cast_ob_heq (fst_obj s h _) _).symm
      (cast_ob_heq (fst_obj s h _) _).symm
      (castHom_heq _ _ _ _).symm (castHom_heq _ _ _ _).symm)))

/-- The functor of the section of a functor over `A` is that functor. -/
theorem total_ofFunctor (h : s ⋙ D.π = 𝟭 A) : (ofFunctor s h).total = s :=
  Functor.hext (fun a => Sigma.ext (fst_obj s h a).symm (cast_ob_heq (fst_obj s h a) _))
    fun a a' f => Total.Hom.hext (Sigma.ext (fst_obj s h a).symm (cast_ob_heq (fst_obj s h a) _))
      (Sigma.ext (fst_obj s h a').symm (cast_ob_heq (fst_obj s h a') _)) (base_map s h f).symm
      (castHom_heq (fst_obj s h a) (fst_obj s h a') (s.map f) (base_map s h f))

end Section

/-- The section of the functor of a section is that section: the transports are along `rfl`. -/
theorem Section.ofFunctor_total {D : Displayed.{v₂, u₂} A} (S : D.Section) :
    Section.ofFunctor S.total (S.total_comp_π) = S :=
  Section.ext (fun _ => rfl) fun f =>
    Section.castHom_heq (Section.fst_obj S.total S.total_comp_π _)
      (Section.fst_obj S.total S.total_comp_π _) (S.total.map f)
      (Section.base_map S.total S.total_comp_π f)

/-- **The sections of `D` are the functors into its total category over `A`.** -/
def Section.equivFunctor (D : Displayed.{v₂, u₂} A) :
    D.Section ≃ {s : A ⥤ D.Total // s ⋙ D.π = 𝟭 A} where
  toFun S := ⟨S.total, S.total_comp_π⟩
  invFun s := Section.ofFunctor s.1 s.2
  left_inv S := Section.ofFunctor_total S
  right_inv s := Subtype.ext (Section.total_ofFunctor s.1 s.2)

/-! ## The category of sections -/

/-- A vertical natural transformation between sections: a vertical morphism over each object,
natural in it. -/
structure Section.Hom {D : Displayed.{v₂, u₂} A} (S T : D.Section) where
  /-- The component over `a`. -/
  app : ∀ a : A, S.obj a ⟶[𝟙 a] T.obj a
  naturality : ∀ {a a' : A} (f : a ⟶ a'), S.map f ≫ᵈ app a' = app a ≫ᵈ T.map f

theorem Section.Hom.ext {D : Displayed.{v₂, u₂} A} {S T : D.Section} {α β : Section.Hom S T}
    (h : ∀ a, α.app a = β.app a) : α = β := by
  obtain ⟨app, _⟩ := α
  obtain ⟨app', _⟩ := β
  obtain rfl : app = app' := funext h
  rfl

/-- **The category of sections**, with the vertical natural transformations. -/
instance Section.category (D : Displayed.{v₂, u₂} A) : Category D.Section where
  Hom S T := Section.Hom S T
  id S := ⟨fun a => 𝟙ᵈ (S.obj a), fun _ => rfl⟩
  comp α β := ⟨fun a => α.app a ≫ᵈ β.app a, fun f =>
    (congrArg (· ≫ᵈ β.app _) (α.naturality f)).trans (congrArg (α.app _ ≫ᵈ ·) (β.naturality f))⟩
  id_comp _ := Section.Hom.ext fun _ => rfl
  comp_id _ := Section.Hom.ext fun _ => rfl
  assoc _ _ _ := Section.Hom.ext fun _ => rfl

/-! ## Reindexing -/

/-- The reindexing of a section of `D` along `u : A ⟶ B`, a section of `DisplayedCat.pull u D`. -/
def Section.pull {A B : Cat.{v₁, u₁}} (u : A ⟶ B) {D : Displayed.{v₂, u₂} B} (S : D.Section) :
    (DisplayedCat.pull u D).Section where
  obj a := S.obj (u.toFunctor.obj a)
  map f := S.map (u.toFunctor.map f)
  map_id a := S.map_id (u.toFunctor.obj a)
  map_comp f g := S.map_comp (u.toFunctor.map f) (u.toFunctor.map g)

end Displayed
