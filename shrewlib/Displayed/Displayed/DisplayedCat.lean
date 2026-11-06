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

universe v₂ u₂ v₁ u₁

open CategoryTheory

namespace Displayed

open scoped Displayed

/-! ## The category of displayed categories -/

-- The universes of the displayed categories only occur in the levels of `DisplayedCat` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The displayed categories, displayed over `Cat`: a morphism over `u` is a displayed functor
over `u`. -/
def DisplayedCat : Displayed Cat.{v₁, u₁} where
  Ob A := Displayed.{v₂, u₂} A
  Hom u D E := DispFunctor u.toFunctor D E
  id D := DispFunctor.id D
  comp H K := H.comp K

namespace DisplayedCat

/-! ## Reindexing -/

section Pull

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (E : Displayed.{v₂, u₂} B)

/-- The reindexing `pull u E` of `E` along `u : A ⟶ B`: the objects of `E` over `u a`, and the
morphisms of `E` over `u f`. -/
def pull : Displayed.{v₂, u₂} A where
  Ob a := E.Ob (u.toFunctor.obj a)
  Hom f x y := x ⟶[u.toFunctor.map f] y
  id x := 𝟙ᵈ x
  comp φ ψ := φ ≫ᵈ ψ

/-- The morphism `pull u E ⟶[u] E`, given by identities. -/
def clift : DispFunctor u.toFunctor (pull u E) E where
  obj x := x
  map φ := φ

end Pull

end DisplayedCat

end Displayed
