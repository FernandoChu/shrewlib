import ComprehensionCategory.Map
import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.Discrete
import Displayed.Fibration.CartesianFunctor
import Mathlib.CategoryTheory.Whiskering

/-!
# The discrete model

The *discrete model* is the comprehension category `ISet` over `Cat` whose types in context `Γ`
are the functors `Γ ⥤ Type u`: a morphism over `u : A ⟶ B` from `F` to `G` is a natural
transformation `F ⟶ u ⋙ G`. Reindexing `ISet.pull u G = u ⋙ G` and the identity transformations
make it a split fibration over `Cat`, whose laws hold by `rfl`.

Its comprehension is that of the category model `ICat`, along the embedding of sets into
categories as discrete categories (`discreteFunctor`): `embed : ISet ⟶ ICat` sends `F` to
`F ⋙ discreteFunctor`, and a natural transformation to the lax transformation with the same
components, whose 2-cells are the naturality equations. It preserves the chosen lifts on the nose,
a cartesian functor, so the comprehension functor `embed ⋙ᵥ compr` preserves cartesian morphisms
(`Comprehension.comap`). The extended context `Γ ▹ F` is the category of elements of `F`: its
objects are pairs `(γ, x)` with `x : F γ`, and its morphisms `(γ, x) ⟶ (γ', x')` are the
`f : γ ⟶ γ'` with `F f x = x'`.

The embedding is fully faithful, since a lax transformation between functors into discrete
categories is a natural transformation, so the discrete model is a full split comprehension
category. It is a strict map of comprehension categories from the discrete model to the category
model (`embedComprehensionMap`), since the comprehension functor of the discrete model is
`embed ⋙ᵥ compr` by definition: both axioms hold by `rfl`.
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

open scoped Displayed

/-! ## Indexed sets -/

/-- The indexed sets and natural transformations, displayed over `Cat`: an object over `A` is a
functor `A ⥤ Type u`, and a morphism over `u : A ⟶ B` from `F` to `G` is a natural transformation
`F ⟶ u ⋙ G`. Composition whiskers the second transformation along the first base functor. -/
def ISet : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := A ⥤ Type u
  Hom u F G := F ⟶ u.toFunctor ⋙ G
  id F := 𝟙 F
  comp {_ _ _ u _ _ _ _} α β := α ≫ Functor.whiskerLeft u.toFunctor β
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace ISet

/-- Reindexing `pull u G = u ⋙ G` of `G : B ⥤ Type u` along `u : A ⟶ B`. -/
def pull {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Type u) : A ⥤ Type u :=
  u.toFunctor ⋙ G

/-- The cartesian lift `pull u G ⟶[u] G`: the identity transformation. -/
def clift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Type u) : ISet.Hom u (pull u G) G :=
  𝟙 (u.toFunctor ⋙ G)

/-- The chosen lift is cartesian: a transformation over `g ≫ u` is its own factorization. -/
def isCartesianClift {A B : Cat.{u, u}} (u : A ⟶ B) (G : B ⥤ Type u) :
    IsCartesian (clift u G) where
  lift _ _ χ := χ
  lift_fac _ _ _ := rfl
  lift_uniq _ hψ := hψ

end ISet

/-- **`ISet` is a split fibration over `Cat`**, cloven by reindexing `ISet.pull u G = u ⋙ G`, with
the identity transformations as chosen lifts. -/
instance ISet.preSplitFib : PreSplitFib ISet.{u} where
  pull u G := ISet.pull u G
  clift u G := ISet.clift u G
  isCartesianClift u G := ISet.isCartesianClift u G
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

instance ISet.splitFib : SplitFib ISet.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

/-! ## The embedding into indexed categories -/

/-- The lax transformation of a natural transformation `α : F ⟶ u ⋙ G` between functors into
discrete categories: its components are those of `α`, and its 2-cells the naturality equations. -/
def embedMap {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Type u} {G : B ⥤ Type u}
    (α : F ⟶ u.toFunctor ⋙ G) :
    LaxTrans (F ⋙ discreteFunctor) (u.toFunctor ⋙ G ⋙ discreteFunctor) where
  app a := (discreteMap' (α.app a)).toFunctor
  naturality f x := ⟨⟨(NatTrans.naturality_apply α f x).symm⟩⟩
  naturality_naturality {_ _} _ {_ _} _ := discrete'_hom_ext _ _
  naturality_id _ := discrete'_hom_ext _ _
  naturality_comp _ _ _ := discrete'_hom_ext _ _

/-- **The embedding of indexed sets into indexed categories**, by discrete categories: a vertical
cartesian functor `ISet ⟶ ICat`. -/
def embed : CartesianFunctor (𝟭 Cat.{u, u}) ISet.{u} ICat.{u} where
  toPre :=
    { obj F := F ⋙ discreteFunctor
      map α := embedMap α
      map_id _ := rfl
      map_comp _ _ := rfl
      obj_pull _ _ := rfl }
  map_clift _ _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) fun _ _ =>
    heq_of_eq (discrete'_hom_ext _ _)

/-- **The embedding is fully faithful**: a lax transformation between functors into discrete
categories is a natural transformation. -/
def embedFullyFaithful : VertFunctor.FullyFaithful embed.toDispFunctor where
  preimage β :=
    { app a := TypeCat.ofHom (β.app a).obj
      naturality _ _ f := ConcreteCategory.hom_ext (C := Type u) _ _ fun x =>
        (β.naturality f x).down.down.symm }
  map_preimage _ := rfl
  preimage_map _ := rfl

/-! ## The comprehension structure -/

/-- The comprehension structure of the discrete model: that of the category model, along the
embedding. -/
@[instance_reducible]
instance comprehension : Comprehension ISet.{u} :=
  Comprehension.comap embed.toDispFunctor embed.isCartesianMap

/-- **The discrete model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension ISet.{u} where

@[instance_reducible]
instance fullComprehension : FullComprehension ISet.{u} where
  comprFullyFaithful := embedFullyFaithful.comp comprFullyFaithful

/-- **The embedding is a strict map of comprehension categories** from the discrete model to the
category model, over the identity of `Cat`: the comprehension functor of the discrete model is
`embed ⋙ᵥ compr`, so the comprehension functors commute on the nose. -/
def embedComprehensionMap : StrictComprehensionMap (𝟭 Cat.{u, u}) ISet.{u} ICat.{u} where
  toPre.toDispFunctor := embed.toDispFunctor
  toPre.isCartesianMap := embed.isCartesianMap
  toPre.compr_obj _ := rfl
  compr_map _ := rfl

end ComprehensionCategory.DiscreteModel
