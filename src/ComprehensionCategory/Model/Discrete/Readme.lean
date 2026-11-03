import ComprehensionCategory.Model.Discrete.Basic
import ComprehensionCategory.Model.Discrete.TypeFormers.Sigma

/-!
# The discrete model

In this folder we define the discrete model: the comprehension category `IDisc` over `Cat`
(`Displayed/Discrete/Straightening/IDisc`), whose types in context `Γ` are the functors `Γ ⥤ Cat`
into discrete categories, and whose morphisms are those of the category model. It is the full
sub-comprehension category of the category model on these types: its comprehension is that of the
category model, along the functor `IDisc.forget : IDisc ⟶ ICat` forgetting the discreteness, a
fully faithful cartesian functor. It is full and split, and `IDisc.forget` is a strict map of
comprehension categories to the category model.

It has Σ-types, those of the category model, which take values in discrete categories, and
`IDisc.forget` preserves them strictly, by `rfl`. This is the point of the definition. The functors
into `Type u` would give a model too, embedded into the category model by taking discrete
categories, but this embedding preserves Σ-types only up to isomorphism: the discrete category on
the objects of a fibre has different morphisms from the fibre (`Basic`). Here the types keep their
category structure, and discreteness is a proposition.

* `Basic`: the comprehension structure pulled back along `IDisc.forget` (`Comprehension.comap`),
  and `IDisc.forget` as a strict map of comprehension categories.
* `TypeFormers/Sigma`: Σ-types, those of the category model, and their strict preservation.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory DiscreteModel Opfibration.Straightening
  Displayed.Discrete.Straightening

/-! ## Main results -/

/-- **The discrete model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.DiscreteModel.splitComprehension : SplitComprehension IDisc.{u}

recall ComprehensionCategory.DiscreteModel.fullComprehension : FullComprehension IDisc.{u}

/-- **The discrete model has Σ-types.** -/
recall ComprehensionCategory.DiscreteModel.hasSigma : HasSigma IDisc.{u}

/-- **Forgetting the discreteness is a strict map of comprehension categories** to the category
model. -/
recall ComprehensionCategory.DiscreteModel.forgetComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u} ICat.{u}

/-- **It preserves Σ-types strictly.** -/
recall ComprehensionCategory.DiscreteModel.forgetComprehensionMap_preservesSigma :
    forgetComprehensionMap.{u}.PreservesSigma

/-- The Σ-types of the discrete model are those of the category model, on the nose. -/
example {Γ : Cat.{u, u}} (A : IDisc.{u}.Ty Γ) (B : IDisc.{u}.Ty (Γ ▹ A)) :
    IDisc.forget.toDispFunctor.obj (Σ[A] B) = ICat.sigma A.toFunctor B.toFunctor :=
  rfl
