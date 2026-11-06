import Displayed.Displayed.Codomain
import Profunctor
import Rules.Bicategory
import Rules.Functor
import Displayed.Fibration.Basic

/-!
# Lax normal functors into profunctors, `LaxNormalCat`

`LaxNormalCat` is the straightened counterpart of `DisplayedCat`
(`Displayed/Displayed/DisplayedCat.lean`): by Bénabou's correspondence, a category displayed over
`A` is a lax normal functor from `A` to the bicategory of profunctors, and the straightening
equivalence `LaxNormalCat ≃ DisplayedCat` of this folder makes this precise. It plays the role that
`ICatLax`, the functors into `Cat`, plays for (op)fibrations.

A lax normal functor `F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat` gives, for each
`f : c ⟶ c'`, a profunctor `prof F f : F.obj ⟨c⟩ ⇸ F.obj ⟨c'⟩`, and its composition
constraint acts on elements as `mul : prof F f x y → prof F g y z → prof F (f ≫ g) x z`. With the
rules of `Rules.Bicategory`, `prof F (𝟙 c) x y` is `x ⟶ y` on the nose, and `mul` satisfies the unit
and associativity laws (`id_mul`, `mul_id`, `mul_assoc`). On elements over identities, it is the
composition of the fibers (`mul_eq_comp`) and their actions on the profunctors (`lmap_eq_mul`,
`rmap_eq_mul`). So a lax normal functor is determined by its categories, its elements and `mul`
(`LaxNormal.ext`).

Over a small category `A`, the objects of `LaxNormalCat` are the lax normal functors
`F : StrictlyUnitaryLaxFunctor (LocallyDiscrete A) ProfCat` (`LaxNormal A`). A morphism over
`u : A ⟶ B` from `F` to `G : LaxNormal B` is a lax transformation from `F` to `G` restricted along
`u`, whose components are the representable profunctors of functors
`F.obj ⟨a⟩ ⥤ G.obj ⟨u a⟩`. By Yoneda, such a transformation amounts to (`ReprHom`)

* the component functors, recorded by their action `obj` on objects, and
* maps `map : prof F f x y → prof G (u f) (obj x) (obj y)` (the 2-cells of the transformation,
  evaluated at identities),

such that `map` preserves the units (`map_id`: by normality `prof F (𝟙 a) x y` is `x ⟶ y`, so
this is also the action of the component functors on morphisms) and the composition constraints
(`map_mul`). Naturality of `map` in `x` and `y` follows from `map_mul`, since the actions of
`prof F (𝟙 a)` on `prof F f` are instances of the composition constraint.

`LaxNormalCat` is a category displayed over `Cat`, with laws holding by `rfl` (`map_id` and
`map_mul` are rewrite rules). Mathlib's `Functor.map_id` and `Functor.map_comp` are rules too, so
the pullback `pullback u G` of `G` along `u` satisfies
`pullback (v ⋙ u) G = pullback v (pullback u G)` by `rfl`. The morphism `pullback u G ⟶[u] G` given
by identities is cartesian, and these lifts make `LaxNormalCat` a split fibration (a `SplitFib`
instance).
-/

universe v₁ u₁ u

namespace Displayed.Straightening

open CategoryTheory Bicategory Displayed Profunctor

open scoped Displayed

/-! ## Lax normal functors into `ProfCat`, on elements -/

/-- Lax normal functors from `A` to the bicategory of categories and profunctors. -/
abbrev LaxNormal (A : Cat.{u, u}) : Type (u + 1) :=
  StrictlyUnitaryLaxFunctor (LocallyDiscrete A) ProfCat.{u}

section LaxNormal

variable {C : Type u₁} [Category.{v₁} C]
  {F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}}

/-- The profunctor `F.map f : F.obj ⟨c⟩ ⇸ F.obj ⟨c'⟩`. -/
abbrev prof (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) {c c' : C}
    (f : c ⟶ c') : F.obj ⟨c⟩ ⇸ F.obj ⟨c'⟩ :=
  F.map f.toLoc

/-- Normality: the elements of `prof F (𝟙 c)` are the morphisms of `F.obj ⟨c⟩`, definitionally. -/
theorem prof_id_obj (c : C) (x y : F.obj ⟨c⟩) : (prof F (𝟙 c)).obj x y = (x ⟶ y) :=
  rfl

/-- The composition constraint `F.mapComp f g` of `F`, on the class of `(u, v)`. -/
abbrev mul {c c' c'' : C} {f : c ⟶ c'} {g : c' ⟶ c''} {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    {z : F.obj ⟨c''⟩} (u : (prof F f).obj x y) (v : (prof F g).obj y z) :
    (prof F (f ≫ g)).obj x z :=
  Profunctor.Hom.app (F.mapComp f.toLoc g.toLoc) x z (CompObj.mk y u v)

theorem id_mul {c c' : C} (f : c ⟶ c') {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    (v : (prof F f).obj x y) : mul (f := 𝟙 c) (𝟙 x) v = v :=
  (congrArg (fun η => Profunctor.Hom.app η x y v) (F.map₂_leftUnitor f.toLoc)).symm

theorem mul_id {c c' : C} (f : c ⟶ c') {x : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩}
    (u : (prof F f).obj x y) : mul (g := 𝟙 c') u (𝟙 y) = u :=
  (congrArg (fun η => Profunctor.Hom.app η x y u) (F.map₂_rightUnitor f.toLoc)).symm

theorem mul_assoc {c₀ c₁ c₂ c₃ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₂ ⟶ c₃)
    {x : F.obj ⟨c₀⟩} {y : F.obj ⟨c₁⟩} {z : F.obj ⟨c₂⟩} {w : F.obj ⟨c₃⟩}
    (u : (prof F f).obj x y) (v : (prof F g).obj y z) (t : (prof F h).obj z w) :
    mul (mul u v) t = mul u (mul v t) := by
  have e := congrArg
    (fun η => Profunctor.Hom.app η x w
      (CompObj.mk (P := Profunctor.comp (F.map f.toLoc) (F.map g.toLoc)) (Q := F.map h.toLoc) z
        (CompObj.mk y u v) t))
    (F.map₂_associator f.toLoc g.toLoc h.toLoc)
  exact e

/-- On the fibre over `c`, `μ` is the composition of `F c`. -/
theorem mul_eq_comp {c : C} {x y z : F.obj ⟨c⟩} (h : x ⟶ y) (h' : y ⟶ z) :
    mul (f := 𝟙 c) (g := 𝟙 c) h h' = h ≫ h' := by
  -- Writing `h` as `hom.lmap h (𝟙 y)`, which holds by the category rules, lets the naturality
  -- rule of `μ` move `h` out of the coend.
  let μ := F.mapComp (𝟙 c).toLoc (𝟙 c).toLoc
  let P := Profunctor.comp (prof F (𝟙 c)) (prof F (𝟙 c))
  have s₁ : mul (f := 𝟙 c) (g := 𝟙 c) h h' =
      Profunctor.Hom.app μ x z (P.lmap h (CompObj.mk y (𝟙 y) h')) :=
    congrArg (Profunctor.Hom.app μ x z)
      (show CompObj.mk y h h' = P.lmap h (CompObj.mk y (𝟙 y) h') from rfl)
  have s₂ : Profunctor.Hom.app μ x z (P.lmap h (CompObj.mk y (𝟙 y) h')) =
      (prof F (𝟙 c)).lmap h (mul (f := 𝟙 c) (𝟙 y) h') := rfl
  exact s₁.trans (s₂.trans (congrArg ((prof F (𝟙 c)).lmap h) (id_mul (𝟙 c) h')))

/-- The action of `F c` on `prof F f` on the left is the composition constraint, as for
`mul_eq_comp`. -/
theorem lmap_eq_mul {c c' : C} (f : c ⟶ c') {x x' : F.obj ⟨c⟩} {y : F.obj ⟨c'⟩} (h : x' ⟶ x)
    (v : (prof F f).obj x y) : (prof F f).lmap h v = mul (f := 𝟙 c) h v := by
  let μ := F.mapComp (𝟙 c).toLoc f.toLoc
  let P := Profunctor.comp (prof F (𝟙 c)) (prof F f)
  have s₁ : mul (f := 𝟙 c) h v = Profunctor.Hom.app μ x' y (P.lmap h (CompObj.mk x (𝟙 x) v)) :=
    congrArg (Profunctor.Hom.app μ x' y)
      (show CompObj.mk x h v = P.lmap h (CompObj.mk x (𝟙 x) v) from rfl)
  have s₂ : Profunctor.Hom.app μ x' y (P.lmap h (CompObj.mk x (𝟙 x) v)) =
      (prof F f).lmap h (mul (f := 𝟙 c) (𝟙 x) v) := rfl
  exact (s₁.trans (s₂.trans (congrArg ((prof F f).lmap h) (id_mul f v)))).symm

/-- The action of `F c'` on `prof F f` on the right is the composition constraint. -/
theorem rmap_eq_mul {c c' : C} (f : c ⟶ c') {x : F.obj ⟨c⟩} {y y' : F.obj ⟨c'⟩} (h : y ⟶ y')
    (u : (prof F f).obj x y) : (prof F f).rmap h u = mul (g := 𝟙 c') u h := by
  let μ := F.mapComp f.toLoc (𝟙 c').toLoc
  let P := Profunctor.comp (prof F f) (prof F (𝟙 c'))
  have s₁ : mul (g := 𝟙 c') u h = Profunctor.Hom.app μ x y' (P.rmap h (CompObj.mk y u (𝟙 y))) :=
    congrArg (Profunctor.Hom.app μ x y')
      (show CompObj.mk y u h = P.rmap h (CompObj.mk y u (𝟙 y)) from rfl)
  have s₂ : Profunctor.Hom.app μ x y' (P.rmap h (CompObj.mk y u (𝟙 y))) =
      (prof F f).rmap h (mul (g := 𝟙 c') u (𝟙 y)) := rfl
  exact (s₁.trans (s₂.trans (congrArg ((prof F f).rmap h) (mul_id f u)))).symm

end LaxNormal

/-- **Lax normal functors are determined by their elements**: the categories `F.obj a`, the
elements of the profunctors `F.map f` with their actions, and the composition constraints on
elements. The data are compared on heterogeneously equal arguments, as their types are only equal
once the categories `F.obj a` are. The 2-cells and units are determined by the structure: the
2-cells of `LocallyDiscrete A` are identities, and `F` is strictly unitary. -/
theorem LaxNormal.ext {A : Cat.{u, u}} {F G : LaxNormal A} (hobj : ∀ a, F.obj a = G.obj a)
    (hprof : ∀ {a b : LocallyDiscrete A} (f : a ⟶ b) {x : F.obj a} {x' : G.obj a} {y : F.obj b}
      {y' : G.obj b}, x ≍ x' → y ≍ y' → (F.map f).obj x y = (G.map f).obj x' y')
    (hlmap : ∀ {a b : LocallyDiscrete A} (f : a ⟶ b) {x₁ x₂ : F.obj a} {x₁' x₂' : G.obj a}
      {y : F.obj b} {y' : G.obj b} (k : x₂ ⟶ x₁) (k' : x₂' ⟶ x₁') (s : (F.map f).obj x₁ y)
      (s' : (G.map f).obj x₁' y'), x₁ ≍ x₁' → x₂ ≍ x₂' → y ≍ y' → k ≍ k' → s ≍ s' →
        (F.map f).lmap k s ≍ (G.map f).lmap k' s')
    (hrmap : ∀ {a b : LocallyDiscrete A} (f : a ⟶ b) {x : F.obj a} {x' : G.obj a}
      {y₁ y₂ : F.obj b} {y₁' y₂' : G.obj b} (k : y₁ ⟶ y₂) (k' : y₁' ⟶ y₂')
      (s : (F.map f).obj x y₁) (s' : (G.map f).obj x' y₁'), x ≍ x' → y₁ ≍ y₁' → y₂ ≍ y₂' →
        k ≍ k' → s ≍ s' → (F.map f).rmap k s ≍ (G.map f).rmap k' s')
    (hmul : ∀ {a b c : LocallyDiscrete A} (f : a ⟶ b) (g : b ⟶ c) {x : F.obj a} {x' : G.obj a}
      {y : F.obj b} {y' : G.obj b} {z : F.obj c} {z' : G.obj c} (s : (F.map f).obj x y)
      (s' : (G.map f).obj x' y') (t : (F.map g).obj y z) (t' : (G.map g).obj y' z'),
      x ≍ x' → y ≍ y' → z ≍ z' → s ≍ s' → t ≍ t' →
        (F.mapComp f g).app x z (CompObj.mk y s t) ≍
          (G.mapComp f g).app x' z' (CompObj.mk y' s' t')) :
    F = G := by
  obtain ⟨⟨⟨⟨⟨obj, map⟩, map₂⟩, map₂_id, _⟩, mapId, mapComp, _, _, _, _, _⟩, _, mapId_eq⟩ := F
  obtain ⟨⟨⟨⟨⟨obj', map'⟩, map₂'⟩, map₂_id', _⟩, mapId', mapComp', _, _, _, _, _⟩, _,
    mapId_eq'⟩ := G
  obtain rfl : obj = obj' := funext hobj
  obtain rfl : @map = @map' := by
    funext a b f
    exact Profunctor.ext (fun _ _ => hprof f HEq.rfl HEq.rfl)
      (fun k s s' h => hlmap f k k s s' HEq.rfl HEq.rfl HEq.rfl HEq.rfl h)
      (fun k s s' h => hrmap f k k s s' HEq.rfl HEq.rfl HEq.rfl HEq.rfl h)
  obtain rfl : @map₂ = @map₂' := by
    funext a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    exact (map₂_id f).trans (map₂_id' f).symm
  obtain rfl : mapId = mapId' := funext fun a => (mapId_eq a).trans (mapId_eq' a).symm
  obtain rfl : @mapComp = @mapComp' := by
    funext a b c f g
    refine Profunctor.hom_ext fun x z w => ?_
    induction w using CompObj.ind with
    | h y s t => exact eq_of_heq (hmul f g s s t t HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
  rfl

/-! ## Morphisms with representable components -/

/-- A lax transformation from `F` to `G` restricted along `u`, with representable components, as
a map of elements. -/
structure ReprHom {A B : Cat.{u, u}} (u : A ⟶ B) (F : LaxNormal A) (G : LaxNormal B) where
  /-- The component functors `F.obj ⟨a⟩ ⥤ G.obj ⟨u a⟩`, on objects. -/
  obj : {a : A} → F.obj ⟨a⟩ → G.obj ⟨u.toFunctor.obj a⟩
  /-- The 2-cells, on elements. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : F.obj ⟨a⟩} → {y : F.obj ⟨a'⟩} →
    (prof F f).obj x y → (prof G (u.toFunctor.map f)).obj (obj x) (obj y)
  map_id : ∀ {a : A} (x : F.obj ⟨a⟩), map (f := 𝟙 a) (𝟙 x) = 𝟙 (obj x) := by intros; rfl
  map_mul : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : F.obj ⟨a⟩} {y : F.obj ⟨a'⟩}
    {z : F.obj ⟨a''⟩} (s : (prof F f).obj x y) (t : (prof F g).obj y z),
    map (mul s t) = mul (map s) (map t) := by intros; rfl

attribute [rewrite_rule] ReprHom.map_id ReprHom.map_mul

namespace ReprHom

variable {A B : Cat.{u, u}} {u : A ⟶ B} {F : LaxNormal A} {G : LaxNormal B}

theorem ext {φ ψ : ReprHom u F G} (hobj : ∀ (a : A) (x : F.obj ⟨a⟩), φ.obj x = ψ.obj x)
    (hmap : ∀ (a a' : A) (f : a ⟶ a') (x : F.obj ⟨a⟩) (y : F.obj ⟨a'⟩) (s : (prof F f).obj x y),
      HEq (φ.map s) (ψ.map s)) : φ = ψ := by
  obtain ⟨o, m, _, _⟩ := φ
  obtain ⟨o', m', _, _⟩ := ψ
  obtain rfl : @o = @o' := by funext a x; exact hobj a x
  obtain rfl : @m = @m' := by
    funext a a' f x y s; exact eq_of_heq (hmap a a' f x y s)
  rfl

/-- Transformations between equal lax normal functors are heterogeneously equal if they agree on
heterogeneously equal objects and elements. -/
theorem hext {F' : LaxNormal A} {G' : LaxNormal B} (hF : F = F') (hG : G = G') {φ : ReprHom u F G}
    {φ' : ReprHom u F' G'}
    (hobj : ∀ {a : A} (x : F.obj ⟨a⟩) (x' : F'.obj ⟨a⟩), x ≍ x' → φ.obj x ≍ φ'.obj x')
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {x : F.obj ⟨a⟩} {y : F.obj ⟨a'⟩} {x' : F'.obj ⟨a⟩}
      {y' : F'.obj ⟨a'⟩} (s : (prof F f).obj x y) (s' : (prof F' f).obj x' y'), x ≍ x' → y ≍ y' →
        s ≍ s' → φ.map s ≍ φ'.map s') :
    φ ≍ φ' := by
  subst hF hG
  exact heq_of_eq (ext (fun _ x => eq_of_heq (hobj x x HEq.rfl))
    (fun _ _ _ _ _ s => hmap s s HEq.rfl HEq.rfl HEq.rfl))

end ReprHom

/-- `LaxNormalCat`, displayed over `Cat`: the lax normal functors from `A` into profunctors over
`A`, and the transformations with representable components over `u : A ⟶ B`. -/
def LaxNormalCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob := LaxNormal
  Hom := ReprHom
  id _ :=
    { obj := fun x => x
      map := fun s => s }
  comp φ ψ :=
    { obj := fun x => ψ.obj (φ.obj x)
      map := fun s => ψ.map (φ.map s) }

/-! ## Pullbacks and the fibration property -/

/-- The pullback of a lax normal functor along `u : A ⟶ B`. -/
def pullback {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) : LaxNormal A where
  obj a := G.obj ⟨u.toFunctor.obj a.as⟩
  map f := G.map (u.toFunctor.map f.as).toLoc
  -- The 2-cell is built with the constructor of the hom-types of `LocallyDiscrete B`, rather than
  -- as an `eqToHom`, so that by eta it agrees with any 2-cell: `pullback (𝟙 A) G` is then `G` on
  -- the nose.
  map₂ η := G.map₂ ⟨congrArg (fun k => u.toFunctor.map k.as) (LocallyDiscrete.eq_of_hom η)⟩
  map₂_id _ := rfl
  map₂_comp η θ := G.map₂_comp _ _
  mapId _ := 𝟙 _
  mapComp f g := G.mapComp (u.toFunctor.map f.as).toLoc (u.toFunctor.map g.as).toLoc
  mapComp_naturality_left η g := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    exact G.mapComp_naturality_left (𝟙 _) _
  mapComp_naturality_right f _ _ η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    exact G.mapComp_naturality_right _ (𝟙 _)
  map₂_associator f g h :=
    G.map₂_associator (u.toFunctor.map f.as).toLoc (u.toFunctor.map g.as).toLoc
      (u.toFunctor.map h.as).toLoc
  map₂_leftUnitor f := G.map₂_leftUnitor (u.toFunctor.map f.as).toLoc
  map₂_rightUnitor f := G.map₂_rightUnitor (u.toFunctor.map f.as).toLoc
  map_id _ := rfl
  mapId_eq_eqToHom _ := rfl

/-- The cartesian lift of `G` along `u`: identities `pullback u G ⟶[u] G`. -/
def pullbackLift {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) :
    LaxNormalCat.Hom u (pullback u G) G where
  obj x := x
  map s := s

/-- The chosen lift is cartesian: a transformation over `v ≫ u` is its own factorization. -/
def isCartesianPullbackLift {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) :
    IsCartesian (D := LaxNormalCat) (pullbackLift u G) where
  lift _ _ χ := ⟨χ.obj, χ.map, χ.map_id, χ.map_mul⟩
  lift_fac _ _ _ := rfl
  lift_uniq _ hψ := by
    subst hψ
    rfl

/-- **`LaxNormalCat` is a split fibration over `Cat`**, cloven by the pullbacks. Pullback along the
identity and along composites holds on the nose. -/
instance preSplitFibLaxNormalCat : PreSplitFib LaxNormalCat.{u} where
  pull u G := pullback u G
  clift u G := pullbackLift u G
  isCartesianClift u G := isCartesianPullbackLift u G

instance splitFibLaxNormalCat : SplitFib LaxNormalCat.{u} := {}

end Displayed.Straightening
