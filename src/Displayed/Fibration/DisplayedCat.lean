import Displayed.Displayed.DisplayedCat
import Displayed.Fibration.Basic

/-!
# `DisplayedCat` is a split fibration

Reindexing along `u : A ⟶ B`, `DisplayedCat.pull u E`, is precomposition with `u`, with the
morphism `DisplayedCat.clift u E : DisplayedCat.pull u E ⟶[u] E` given by identities. It is
cartesian in `DisplayedCat` (`DisplayedCat.isCartesianClift`): a displayed functor over `w ≫ u`
into `E` is a displayed functor over `w` into `pull u E`, with the same components. Precomposition
is strictly unital and associative, so these lifts make `DisplayedCat` a split fibration over `Cat`
(`DisplayedCat.splitFib`), whose splitting laws hold by `rfl`.

That taking total categories sends these lifts to pullbacks, and the cleavage of `cod Cat`, are in
`Displayed/CodCatEquiv/Fibration`.
-/

universe u

open CategoryTheory

namespace Displayed.DisplayedCat

open scoped Displayed

section Split

variable {A B : Cat.{u, u}} (u : A ⟶ B) (E : Displayed.{u, u, u, u} B)

/-- The chosen lift is cartesian: a displayed functor over `w ≫ u` is its own factorization. -/
def isCartesianClift : IsCartesian (D := DisplayedCat) (clift u E) where
  lift _ _ χ := ⟨χ.obj, χ.map, χ.map_id, χ.map_comp⟩
  lift_fac _ _ _ := rfl
  lift_uniq _ hψ := by
    subst hψ
    rfl

/-- **`DisplayedCat` is a split fibration over `Cat`**, cloven by reindexing. Reindexing along the
identity and along composites holds on the nose. -/
instance preSplitFib : PreSplitFib DisplayedCat.{u} where
  pull u E := pull u E
  clift u E := clift u E
  isCartesianClift u E := isCartesianClift u E
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

instance splitFib : SplitFib DisplayedCat.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

end Split

end Displayed.DisplayedCat
