import Displayed.Displayed.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# The category of displayed categories

`DisplayedCat`, displayed over `Cat`, has the categories displayed over `A` as objects over `A`,
and the displayed functors over `u : A ⟶ B` as morphisms over `u`. Its laws hold by `rfl`.

Reindexing `DisplayedCat.pull u E` along `u : A ⟶ B` is precomposition with `u`, and comes with the
morphism `DisplayedCat.clift u E : pull u E ⟶[u] E`, given by identities. That these make
`DisplayedCat` a split fibration over `Cat` is in `Displayed/Fibration/DisplayedCat`.

The equivalence `DisplayedCat ≃ cod Cat` over `Cat` taking total categories is in
`Displayed/CodCatEquiv`.
-/

universe u

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

end Pull

end DisplayedCat

end Displayed
