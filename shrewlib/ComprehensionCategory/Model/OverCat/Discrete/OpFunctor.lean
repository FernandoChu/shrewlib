import CategoryTheory.Opposite.OpFunctor
import Displayed.Discrete.DiscreteCat

/-!
# The opposite of a discrete category

The opposite `opFunctor'.obj C` of a discrete category `C` is discrete
(`isDiscrete_opFunctor'_obj`): its morphisms `x ⟶ y` are the morphisms `y ⟶ x` of `C`. This gives
the opposite types of the discrete model.

The discrete categories `discrete' S` of `Displayed/Discrete/DiscreteCat` are moreover their own
opposites, by `propext` (`opFunctor'_obj_discrete'`): `t = s` and `s = t` are different types,
but equivalent propositions. This gives Hom-op for the Hom-types, whose values are such discrete
categories. It is not the case for every discrete category: the morphisms `x ⟶ y` and `y ⟶ x` of
a discrete category are subsingletons inhabited exactly when `x = y`, so equivalent types, but not
equal in general.

This file imports no rewrite rules, and must not, for the reason given in
`CategoryTheory/Opposite/OpFunctor`: it compares category structures given as
structures.
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed.Discrete

/-- **The opposite of a discrete category is discrete.** -/
theorem isDiscrete_opFunctor'_obj (C : Cat.{u, u}) [IsDiscrete C] :
    IsDiscrete (opFunctor'.obj C) where
  subsingleton x y := IsDiscrete.subsingleton (C := C) y x
  eq_of_hom f := (IsDiscrete.eq_of_hom (C := C) f).symm

/-! ## Discrete categories on types are self-opposite -/

/-- Two category structures with the same morphisms are equal if the morphisms are subsingletons:
then the identities and composites agree. -/
theorem category_eq_of_hom_eq {C : Type u} (c d : Category.{u} C)
    (h : ∀ x y, @Quiver.Hom C c.toQuiver x y = @Quiver.Hom C d.toQuiver x y)
    [∀ x y, Subsingleton (@Quiver.Hom C d.toQuiver x y)] : c = d := by
  obtain @⟨@⟨@⟨H⟩, id, comp⟩, _, _, _⟩ := c
  obtain @⟨@⟨@⟨H'⟩, id', comp'⟩, _, _, _⟩ := d
  obtain rfl : H = H' := funext fun x => funext fun y => h x y
  obtain rfl : @id = @id' := funext fun _ => Subsingleton.elim _ _
  obtain rfl : @comp = @comp' := by
    funext _ _ _ _ _
    exact Subsingleton.elim _ _
  rfl

/-- **A discrete category is its own opposite**, by `propext`. -/
theorem opCategory'_discreteCategory' (S : Type u) :
    opCategory' (discreteCategory' S) = discreteCategory' S :=
  category_eq_of_hom_eq _ _ fun _ _ =>
    congrArg (fun p : Prop => ULift.{u} (PLift p)) (propext eq_comm)

theorem opFunctor'_obj_discrete' (S : Type u) : opFunctor'.obj (discrete' S) = discrete' S :=
  congrArg (@Cat.of S) (opCategory'_discreteCategory' S)

/-- Functors into discrete categories are determined by their objects, also between equal
category structures. -/
theorem catHom_heq_of_obj {S T : Type u} {c c' : Category.{u} S} {d d' : Category.{u} T}
    (hc : c = c') (hd : d = d') [∀ x y, Subsingleton (@Quiver.Hom T d'.toQuiver x y)]
    (F : @Cat.of S c ⟶ @Cat.of T d) (G : @Cat.of S c' ⟶ @Cat.of T d')
    (hobj : ∀ x, F.toFunctor.obj x = G.toFunctor.obj x) : F ≍ G := by
  subst hc hd
  exact heq_of_eq (Cat.Hom.ext (Functor.ext hobj fun _ _ _ => Subsingleton.elim _ _))

/-- The opposite of the functor of a function is that functor. -/
theorem opFunctor'_map_discreteMap' {S T : Type u} (k : S → T) :
    opFunctor'.map (discreteMap' k) ≍ discreteMap' k :=
  catHom_heq_of_obj (opCategory'_discreteCategory' S) (opCategory'_discreteCategory' T) _ _
    fun _ => rfl

end ComprehensionCategory.DiscreteModel
