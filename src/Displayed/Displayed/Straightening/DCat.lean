import Displayed.Displayed.Codomain
import Profunctor
import Rules.Bicategory
import Rules.Functor
import Displayed.Fibration.Basic

/-!
# The category of displayed categories, `DCat = Cat ▷⁻ [−, Cat_Prof]^{lax,normal}`

A lax normal (strictly unitary) functor `F : LocallyDiscrete C ⥤ᴸ ProfCat` gives, for each
`f : c ⟶ c'`, a profunctor `prof F f : F c ⇸ F c'`, and its composition constraint acts on
elements as `mul : prof F f x y → prof F g y z → prof F (f ≫ g) x z`. With the rules of
`Rules.Bicategory`, `prof F (𝟙 c) x y` is `x ⟶ y` on the nose, and `mul` satisfies the unit and
associativity laws (`id_mul`, `mul_id`, `mul_assoc`) and restricts to composition on the fibers
(`mul_eq_comp`).

Over a small category `A`, the objects of `DCat` are the lax normal functors
`F : LocallyDiscrete A ⥤ᴸ ProfCat` (`LaxNormal A`). A morphism over `u : A ⟶ B` from `F` to
`G : LaxNormal B` is a lax transformation `F ⇒ G ∘ u` whose components are representable
profunctors `(h_a)_*`. By Yoneda, such a transformation amounts to (`ReprHom`)

* functors `h_a : F a ⥤ G (u a)`, recorded by their action `obj` on objects, and
* maps `map : F f x y → G (u f) (h x) (h y)` (the 2-cells `F f ⊗ (h_{a'})_* ⟶ (h_a)_* ⊗ G (u f)`
  evaluated at identities),

such that `map` preserves the units (`map_id`: by normality `F (𝟙 a) x y` is `x ⟶ y`, so this is
also the action of `h_a` on morphisms) and the composition constraints (`map_mul`). Naturality of
`map` in `x` and `y` follows from `map_mul`, since the actions of `F (𝟙 a)` on `F f` are
instances of the composition constraint.

`DCat` is a category displayed over `Cat`, with laws holding by `rfl` (`map_id` and `map_mul` are
rewrite rules). Mathlib's `Functor.map_id` and `Functor.map_comp` are rules too, so the pullback
`u^* G` of `G` along `u` (`pullback`) satisfies `(v ⋙ u)^* G ≡ v^* (u^* G)`. The morphism
`u^* G ⟶[u] G` given by identities is cartesian, and these lifts make `DCat` a split fibration
(a `SplitFib` instance).
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

/-- The profunctor `F f : F c ⇸ F c'`. -/
abbrev prof (F : StrictlyUnitaryLaxFunctor (LocallyDiscrete C) ProfCat.{u}) {c c' : C}
    (f : c ⟶ c') : Profunctor (F.obj ⟨c⟩) (F.obj ⟨c'⟩) :=
  F.map f.toLoc

/-- Normality: the elements of `F (𝟙 c)` are the morphisms of `F c`, definitionally. -/
theorem prof_id_obj (c : C) (x y : F.obj ⟨c⟩) : (prof F (𝟙 c)).obj x y = (x ⟶ y) :=
  rfl

/-- The composition constraint of `F`, `μ : F f ⊗ F g ⟶ F (f ≫ g)`, on the class of `(u, v)`. -/
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

end LaxNormal

/-! ## Morphisms with representable components -/

/-- A lax transformation `F ⇒ G ∘ u` with representable components, as a map of elements. -/
structure ReprHom {A B : Cat.{u, u}} (u : A ⟶ B) (F : LaxNormal A) (G : LaxNormal B) where
  /-- The components `h_a : F a ⥤ G (u a)` on objects. -/
  obj : {a : A} → F.obj ⟨a⟩ → G.obj ⟨u.toFunctor.obj a⟩
  /-- The 2-cells, on elements. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : F.obj ⟨a⟩} → {y : F.obj ⟨a'⟩} →
    (prof F f).obj x y → (prof G (u.toFunctor.map f)).obj (obj x) (obj y)
  map_id : ∀ {a : A} (x : F.obj ⟨a⟩), map (f := 𝟙 a) (𝟙 x) = 𝟙 (obj x)
  map_mul : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : F.obj ⟨a⟩} {y : F.obj ⟨a'⟩}
    {z : F.obj ⟨a''⟩} (s : (prof F f).obj x y) (t : (prof F g).obj y z),
    map (mul s t) = mul (map s) (map t)

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

end ReprHom

/-- `DCat`, the category of displayed categories, displayed over `Cat`. -/
def DCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob := LaxNormal
  Hom := ReprHom
  id _ :=
    { obj := fun x => x
      map := fun s => s
      map_id := fun _ => rfl
      map_mul := fun _ _ => rfl }
  comp φ ψ :=
    { obj := fun x => ψ.obj (φ.obj x)
      map := fun s => ψ.map (φ.map s)
      map_id := fun _ => rfl
      map_mul := fun _ _ => rfl }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Pullbacks and the fibration property -/

/-- The pullback `u^* G` of a lax normal functor along `u : A ⟶ B`. -/
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

/-- The cartesian lift of `G` along `u`: identities `u^* G ⟶[u] G`. -/
def pullbackLift {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) :
    DCat.Hom u (pullback u G) G where
  obj x := x
  map s := s
  map_id _ := rfl
  map_mul _ _ := rfl

theorem isCartesian_pullbackLift {A B : Cat.{u, u}} (u : A ⟶ B) (G : LaxNormal B) :
    IsCartesian (D := DCat) (pullbackLift u G) := by
  intro C v H χ
  refine ⟨⟨χ.obj, χ.map, χ.map_id, χ.map_mul⟩, rfl, fun ψ hψ => ?_⟩
  subst hψ
  rfl

/-- **`DCat` is a split fibration over `Cat`**, cloven by the pullbacks. Pullback along the
identity and along composites holds on the nose. -/
instance preSplitFibDCat : PreSplitFib DCat.{u} where
  pull u G := pullback u G
  clift u G := pullbackLift u G
  clift_cartesian u G := isCartesian_pullbackLift u G
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

instance splitFibDCat : SplitFib DCat.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

end Displayed.Straightening
