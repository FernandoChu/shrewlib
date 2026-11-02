import ComprehensionCategory.Model.Discrete.Basic

/-!
# The discrete model

In this folder we define the discrete model: the comprehension category `ISet` over `Cat`, whose
types in context `Γ` are the functors `Γ ⥤ Type u`, and whose morphisms over `u` from `F` to `G`
are the natural transformations `F ⟶ u ⋙ G`. Its comprehension is that of the category model,
along the embedding `embed : ISet ⟶ ICat` of sets as discrete categories: the context extension
`Γ ▹ F` is the category of elements of `F`. It is full and split, and the embedding is a strict map
of comprehension categories to the category model.

* `Basic`: `ISet`, its splitting by reindexing, the embedding as a fully faithful vertical cartesian
  functor, the comprehension structure pulled back along it (`Comprehension.comap`), and the
  embedding as a strict map of comprehension categories.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory DiscreteModel Opfibration.Straightening

/-! ## Main results -/

/-- **The discrete model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.DiscreteModel.splitComprehension : SplitComprehension ISet.{u}

recall ComprehensionCategory.DiscreteModel.fullComprehension : FullComprehension ISet.{u}

/-- The embedding of indexed sets into indexed categories, by discrete categories, preserves the
chosen lifts and is fully faithful. -/
recall ComprehensionCategory.DiscreteModel.embed :
    CartesianFunctor (𝟭 Cat.{u, u}) ISet.{u} ICat.{u}

recall ComprehensionCategory.DiscreteModel.embedFullyFaithful :
    VertFunctor.FullyFaithful DiscreteModel.embed.{u}.toDispFunctor

/-- **The embedding is a strict map of comprehension categories** to the category model. -/
recall ComprehensionCategory.DiscreteModel.embedComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ISet.{u} ICat.{u}
