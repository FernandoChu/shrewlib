import Displayed.Displayed.Functor
import Displayed.Displayed.Codomain
import Mathlib.CategoryTheory.Category.Cat

/-!
# The category of displayed categories

`DisplayedCat`, displayed over `Cat`, has the categories displayed over `A` as objects over `A`,
and the displayed functors over `u : A ⟶ B` as morphisms over `u`. Its laws hold by `rfl`.

Taking total categories is a vertical functor `DisplayedCat.total : DisplayedCat ⟶ cod Cat`,
sending `D` to the projection `π : D.Total ⥤ A`:

* It is fully faithful (`DisplayedCat.totalFullyFaithful`): a functor `D.Total ⥤ E.Total` over
  `u` is a lift over `D.π ⋙ u` (`TotalLift`), hence a displayed functor from `D` to `E`.
* Reindexing `DisplayedCat.pull u E` along `u : A ⟶ B` comes with the morphism
  `DisplayedCat.clift u E : pull u E ⟶[u] E`, given by identities. That `total` sends it to a
  cartesian morphism of `cod Cat` is in `Displayed/Fibration/DisplayedCat`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-! ## The category of displayed categories -/

/-- The displayed categories, displayed over `Cat`: a morphism over `u` is a displayed functor
over `u`. -/
def DisplayedCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := Displayed.{u, u, u, u} A
  Hom u D E := DispFunctor u.toFunctor D E
  id D := DispFunctor.id D
  comp H K := H.comp K
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace DisplayedCat

/-! ## Total categories -/

section Total

variable {A B : Cat.{u, u}}

/-- The total category of `D`, with its projection, as an object of `cod Cat`. -/
def totalObj (D : Displayed.{u, u, u, u} A) : (cod Cat.{u, u}).Ob A :=
  ⟨Cat.of D.Total, D.π.toCatHom⟩

/-- The functor between total categories induced by a displayed functor over `u`. -/
def totalMap {u : A ⟶ B} {D : Displayed.{u, u, u, u} A} {E : Displayed.{u, u, u, u} B}
    (H : DispFunctor u.toFunctor D E) : totalObj D ⟶[u] totalObj E :=
  ⟨H.total.toCatHom, rfl⟩

/-- **Taking total categories**, a vertical functor into `cod Cat`. -/
def total : VertFunctor DisplayedCat.{u} (cod Cat.{u, u}) where
  obj D := totalObj D
  map H := totalMap H
  map_id _ := rfl
  map_comp _ _ := rfl

variable {u : A ⟶ B} {D : Displayed.{u, u, u, u} A} {E : Displayed.{u, u, u, u} B}

/-- The inverse of `total` on morphisms: the displayed functor of the lift of a functor
`D.Total ⥤ E.Total` over `u`. -/
def totalPreimage (w : totalObj D ⟶[u] totalObj E) : DispFunctor u.toFunctor D E :=
  (TotalLift.ofFunctor w.1.toFunctor
    (show w.1.toFunctor ⋙ E.π = D.π ⋙ u.toFunctor from
      congrArg Cat.Hom.toFunctor w.2)).toDispFunctor

theorem totalMap_preimage (w : totalObj D ⟶[u] totalObj E) : totalMap (totalPreimage w) = w :=
  CodHom.ext (Cat.Hom.ext
    ((TotalLift.toDispFunctor_total _).trans (TotalLift.functor_ofFunctor _ _)))

theorem totalPreimage_map (H : DispFunctor u.toFunctor D E) : totalPreimage (totalMap H) = H :=
  DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

end Total

/-- **Taking total categories is fully faithful**: functors `D.Total ⥤ E.Total` over `u` are
displayed functors over `u`. -/
def totalFullyFaithful : total.{u}.FullyFaithful where
  preimage w := totalPreimage w
  map_preimage w := totalMap_preimage w
  preimage_map H := totalPreimage_map H

/-! ## Reindexing -/

section Pull

variable {A B : Cat.{u, u}} (u : A ⟶ B) (E : Displayed.{u, u, u, u} B)

/-- The reindexing `pull u E` of `E` along `u : A ⟶ B`: the objects of `E` over `u a`, and the
morphisms of `E` over `u f`. -/
def pull : Displayed.{u, u, u, u} A where
  Ob a := E.Ob (u.toFunctor.obj a)
  Hom f x y := x ⟶[u.toFunctor.map f] y
  id x := 𝟙ᵈ x
  comp {_ _ _ f g x _ z} φ ψ := (φ ≫ᵈ ψ : x ⟶[u.toFunctor.map f ≫ u.toFunctor.map g] z)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The morphism `pull u E ⟶[u] E`, given by identities. -/
def clift : DispFunctor u.toFunctor (pull u E) E where
  obj x := x
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

variable {u E} {Z : Type u₁} [Category.{v₁} Z]

/-- A lift over `v ⋙ u` into `E` is a lift over `v` into `pull u E`. -/
def _root_.Displayed.TotalLift.toPull {v : Z ⥤ A} (s : TotalLift (v ⋙ u.toFunctor) E) :
    TotalLift v (pull u E) :=
  ⟨s.obj, s.map, s.map_id, s.map_comp⟩

/-- Followed by `(pull u E).Total ⥤ E.Total`, the functor of a lift over `v` into `pull u E` is that
of the same lift over `v ⋙ u` into `E`. -/
theorem _root_.Displayed.TotalLift.toPull_functor_comp {v : Z ⥤ A}
    (s : TotalLift (v ⋙ u.toFunctor) E) : s.toPull.functor ⋙ (clift u E).total = s.functor :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- The lift into `pull u E` of a functor `Ψ` over `v`, read off its composite with
`(pull u E).Total ⥤ E.Total`, is that of `Ψ`. -/
theorem _root_.Displayed.TotalLift.toPull_ofFunctor {v : Z ⥤ A} (Ψ : Z ⥤ (pull u E).Total)
    (hΨ : Ψ ⋙ (pull u E).π = v) (h : (Ψ ⋙ (clift u E).total) ⋙ E.π = v ⋙ u.toFunctor) :
    (TotalLift.ofFunctor (Ψ ⋙ (clift u E).total) h).toPull = TotalLift.ofFunctor Ψ hΨ := by
  subst hΨ
  rfl

end Pull

end DisplayedCat

end Displayed
