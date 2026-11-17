import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Discrete categories

The discrete category `discrete' S` on a type `S` has the elements of `S` as objects, and the proofs
of `s = t` as morphisms `s ⟶ t` (`discreteCategory'`), and it is discrete in the sense of
Mathlib's `IsDiscrete`. Functions give functors between them (`discreteMap'`). In any category
that is `IsDiscrete`, morphisms between equal objects are heterogeneously equal
(`hom_heq_of_isDiscrete`).

Unlike Mathlib's `Discrete S`, the objects are the elements of `S` themselves, and the morphisms are
not the structure `Discrete.Hom s t`: `(t = s) = (s = t)` holds by `propext`, so that `discrete' S`
is its own opposite (`opFunctor'_obj_discrete'`, in
`ComprehensionCategory/Model/OverCat/Discrete/OpFunctor`). Its morphisms are subsingletons, and any
two of them with the same type are definitionally equal, by eta for `ULift` and `PLift` and proof
irrelevance.

This file imports no rewrite rules, and must not, for the reason given in `Opposite/OpFunctor`:
the laws of `discreteCategory'` could not be checked.
-/

universe v u

namespace CategoryTheory

/-- The discrete category structure on `S`, whose morphisms `s ⟶ t` are the proofs of `s = t`.
Unlike Mathlib's `Discrete S`, whose morphisms form the structure `Discrete.Hom s t`, it is equal
to its opposite (`opCategory'_discreteCategory'`), since `(t = s) = (s = t)`. -/
@[instance_reducible]
def discreteCategory' (S : Type u) : Category.{u} S where
  Hom s t := ULift.{u} (PLift (s = t))
  id _ := ⟨⟨rfl⟩⟩
  comp f g := ⟨⟨f.down.down.trans g.down.down⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The discrete category on `S`. -/
def discrete' (S : Type u) : Cat.{u, u} :=
  @Cat.of S (discreteCategory' S)

instance (S : Type u) (s t : S) : Subsingleton (@Quiver.Hom S (discreteCategory' S).toQuiver s t) :=
  inferInstanceAs (Subsingleton (ULift (PLift (s = t))))

/-- Any two morphisms of a discrete category with the same type are equal. -/
theorem discrete'_hom_ext {S : Type u} {s t : discrete' S} (f g : s ⟶ t) : f = g :=
  Subsingleton.elim (α := ULift.{u} (PLift (@Eq S s t))) f g

/-- `discrete' S` is discrete, in the sense of Mathlib's `IsDiscrete`. -/
instance isDiscrete_discrete' (S : Type u) : IsDiscrete (discrete' S) where
  subsingleton _ _ := ⟨discrete'_hom_ext⟩
  eq_of_hom f := f.down.down

/-- Morphisms of a discrete category between equal objects are heterogeneously equal. -/
theorem hom_heq_of_isDiscrete {C : Type u} [Category.{v} C] [IsDiscrete C] {x x' y y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y') : f ≍ g := by
  subst hx hy
  exact heq_of_eq (Subsingleton.elim f g)

/-- The functor between discrete categories of a function. -/
def discreteMap' {S T : Type u} (k : S → T) : discrete' S ⟶ discrete' T :=
  Cat.Hom.ofFunctor
    { obj s := k s
      map e := ⟨⟨congrArg k e.down.down⟩⟩ }

end CategoryTheory
