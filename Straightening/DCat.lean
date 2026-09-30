import Straightening.Arrow
import Unstraightening

/-!
# The category of displayed categories, `DCat = Cat ▷⁻ [−, Cat_Prof]^{lax,normal}`

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
`u^* G ⟶[u] G` given by identities is cartesian, so `DCat` is a fibration (`isFibration_DCat`).
-/

universe u

namespace Straightening

open CategoryTheory Bicategory Nfib Displayed Unstraightening

open scoped Displayed

attribute [rewrite_rule] Functor.map_id Functor.map_comp

/-- Lax normal functors from `A` to the bicategory of categories and profunctors. -/
abbrev LaxNormal (A : Cat.{u, u}) : Type (u + 1) :=
  StrictlyUnitaryLaxFunctor (LocallyDiscrete A) ProfCat.{u}

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
  map₂ η := G.map₂ (eqToHom (congrArg (fun k => (u.toFunctor.map k.as).toLoc)
    (LocallyDiscrete.eq_of_hom η)))
  map₂_id _ := rfl
  map₂_comp η θ := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := LocallyDiscrete.eq_of_hom θ
    rfl
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

/-- **`DCat` is a fibration over `Cat`.** -/
theorem isFibration_DCat : IsFibration DCat.{u} :=
  fun _ _ u G => ⟨pullback u G, pullbackLift u G, isCartesian_pullbackLift u G⟩

end Straightening
