import ComprehensionCategory.Model.OverCat.Discrete.Basic
import ComprehensionCategory.Model.OverCat.Discrete.OpFunctor
import ComprehensionCategory.Model.OverCat.Discrete.Small
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Sigma
import ComprehensionCategory.Model.OverCat.Discrete.TypeFormers.Unit

/-!
# The discrete model

In this folder we define the discrete model: the comprehension category `IDisc` over `Cat`
(`Displayed/Discrete/Straightening/IDisc`), whose types in context `Γ` are the functors `Γ ⥤ Cat`
into discrete categories, and whose morphisms are those of the category model. It is the full
sub-comprehension category of the category model on these types: its comprehension is that of the
category model, along the functor `IDisc.forget : IDisc ⟶ ICatLax` forgetting the discreteness, a
fully faithful cartesian functor. It is full and split.

It has Σ-types and opposite types, those of the category model, which take values in discrete
categories. So forgetting the discreteness preserves them strictly, by `rfl`
(`OverCat/Maps/DiscreteToCat`). This is the point of the definition. The functors into `Type u`
would give a model too, embedded into the category model by taking discrete categories, but this
embedding preserves Σ-types only up to isomorphism: the discrete category on the objects of a fibre
has different morphisms from the fibre (`Basic`). Here the types keep their category structure, and
discreteness is a proposition.

The Hom-types of the category model are types of the discrete model (`OverCat/Shared/Hom`).

* `Basic`: the comprehension structure pulled back along `IDisc.forget` (`Comprehension.comap`).
* `TypeFormers/Sigma`: Σ-types, those of the category model.
* `TypeFormers/Unit`: unit types, those of the category model, at the discrete category
  `discrete' PUnit`.
* `OpFunctor`: the discrete categories `discrete' S` are their own opposites, by `propext`. It
  imports no rewrite rules. The general facts on the opposite of a discrete category are in
  `CategoryTheory/Opposite/Discrete`: it is discrete, and it is the category itself if empty types
  are unique (`EmptyUnique`, in `Logic/EmptyUnique`), which is independent of Lean's axioms and is
  a hypothesis of these results.
* `TypeFormers/Op`: opposite types, those of the category model, involutive and stable under
  substitution by `rfl`. If empty types are unique, a discrete type is its own opposite (op-Disc,
  `op_eq_self`), propositionally.
* `Small`: at level `v + 1`, the discrete types of level `v`, the functors `Γ ⥤ Cat.{v, v}` into
  discrete categories, as a full split comprehension category `SmallIDisc`, along their lift into
  the category model; they lift into the discrete model too (`liftDisc`).
-/

universe u

open CategoryTheory Displayed ComprehensionCategory DiscreteModel Opfibration.Straightening
  Displayed.Discrete.Straightening

/-! ## Main results -/

/-- **The discrete model** is a full split comprehension category over `Cat`. -/
recall ComprehensionCategory.DiscreteModel.splitComprehension :
    SplitComprehension IDisc.{u, u, u, u}

recall ComprehensionCategory.DiscreteModel.fullComprehension : FullComprehension IDisc.{u, u, u, u}

/-- **The discrete model has Σ-types.** -/
recall ComprehensionCategory.DiscreteModel.hasSigma : HasSigma IDisc.{u, u, u, u}

/-- **The discrete model has unit types**, those of the category model. -/
recall ComprehensionCategory.DiscreteModel.hasUnit : HasUnit IDisc.{u, u, u, u}

/-- The Σ-types of the discrete model are those of the category model, on the nose. -/
example {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) (B : IDisc.{u, u}.Ty (Γ ▹ A)) :
    IDisc.forget.toDispFunctor.obj (Σ[A] B) = ICatLax.sigma A.toFunctor B.toFunctor :=
  rfl

/-- **The discrete model has opposite types**, involutive by `rfl`. -/
recall ComprehensionCategory.DiscreteModel.op_op {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) :
    DiscreteModel.op (DiscreteModel.op A) = A

/-- **op-Disc**: if empty types are unique, a discrete type is its own opposite. -/
recall ComprehensionCategory.DiscreteModel.op_eq_self (hE : EmptyUnique.{u})
    {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) : DiscreteModel.op A = A

/-- A discrete category is its own opposite. -/
recall ComprehensionCategory.DiscreteModel.opFunctor'_obj_discrete' (S : Type u) :
    opFunctor'.obj (discrete' S) = discrete' S
