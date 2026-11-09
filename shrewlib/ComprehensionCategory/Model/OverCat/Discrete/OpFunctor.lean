import CategoryTheory.Opposite.Discrete
import Displayed.Discrete.DiscreteCat

/-!
# The opposite of a discrete category on a type

The opposite of a discrete category is discrete (`CategoryTheory.isDiscrete_opFunctor'_obj`, in
`CategoryTheory/Opposite/Discrete`), which gives the opposite types of the discrete model.

The discrete categories `discrete' S` of `Displayed/Discrete/DiscreteCat` are moreover their own
opposites, by `propext` (`opFunctor'_obj_discrete'`): `t = s` and `s = t` are different types,
but equivalent propositions. This gives Hom-op for the Hom-types, whose values are such discrete
categories. It is not the case for every discrete category, unless empty types are unique
(`CategoryTheory.opFunctor'_obj_of_isDiscrete`).

This file imports no rewrite rules, and must not, for the reason given in
`CategoryTheory/Opposite/OpFunctor`: it compares category structures given as
structures.
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed.Discrete

/-- **A discrete category is its own opposite**, by `propext`. -/
theorem opCategory'_discreteCategory' (S : Type u) :
    opCategory' (discreteCategory' S) = discreteCategory' S :=
  category_eq_of_hom_eq _ _ fun _ _ =>
    congrArg (fun p : Prop => ULift.{u} (PLift p)) (propext eq_comm)

theorem opFunctor'_obj_discrete' (S : Type u) : opFunctor'.obj (discrete' S) = discrete' S :=
  congrArg (@Cat.of S) (opCategory'_discreteCategory' S)

/-- The opposite of the functor of a function is that functor. -/
theorem opFunctor'_map_discreteMap' {S T : Type u} (k : S → T) :
    opFunctor'.map (discreteMap' k) ≍ discreteMap' k :=
  catHom_heq_of_obj (opCategory'_discreteCategory' S) (opCategory'_discreteCategory' T) _ _
    fun _ => rfl

end ComprehensionCategory.DiscreteModel
