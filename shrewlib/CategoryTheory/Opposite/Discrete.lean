import CategoryTheory.Opposite.OpFunctor
import Logic.EmptyUnique
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The opposite of a discrete category

The opposite `opFunctor'.obj C` of a discrete category `C` is discrete
(`isDiscrete_opFunctor'_obj`): its morphisms `x ⟶ y` are the morphisms `y ⟶ x` of `C`.

A discrete category need not be its own opposite: its morphisms `x ⟶ y` and `y ⟶ x` are
subsingletons inhabited exactly when `x = y`, so equivalent types, but not equal in general. When
`x ≠ y`, both are empty, and two empty types are not provably equal. They are if empty types are
unique (`EmptyUnique`, in `Logic/EmptyUnique`), and then every discrete category is its own
opposite (`opFunctor'_obj_of_isDiscrete`), and so is every functor into discrete categories
(`comp_opFunctor'_of_isDiscrete`).

Two category structures on the same objects are equal if their morphisms are, provided that these
are subsingletons (`category_eq_of_hom_eq`), and functors into categories with subsingleton
morphisms are determined by their objects (`catHom_heq_of_obj`).

This file imports no rewrite rules, and must not, for the reason given in `OpFunctor`: it compares
category structures given as structures.
-/

universe v u v₁ u₁

namespace CategoryTheory

/-- **The opposite of a discrete category is discrete.** -/
theorem isDiscrete_opFunctor'_obj (C : Cat.{v, u}) [IsDiscrete C] :
    IsDiscrete (opFunctor'.obj C) where
  subsingleton x y := IsDiscrete.subsingleton (C := C) y x
  eq_of_hom f := (IsDiscrete.eq_of_hom (C := C) f).symm

/-- Two category structures with the same morphisms are equal if the morphisms are subsingletons:
then the identities and composites agree. -/
theorem category_eq_of_hom_eq {C : Type u} (c d : Category.{v} C)
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

/-- Functors into categories with subsingleton morphisms are determined by their objects, also
between equal category structures. -/
theorem catHom_heq_of_obj {S T : Type u} {c c' : Category.{v} S} {d d' : Category.{v} T}
    (hc : c = c') (hd : d = d') [∀ x y, Subsingleton (@Quiver.Hom T d'.toQuiver x y)]
    (F : @Cat.of S c ⟶ @Cat.of T d) (G : @Cat.of S c' ⟶ @Cat.of T d')
    (hobj : ∀ x, F.toFunctor.obj x = G.toFunctor.obj x) : F ≍ G := by
  subst hc hd
  exact heq_of_eq (Cat.Hom.ext (Functor.ext hobj fun _ _ _ => Subsingleton.elim _ _))

/-- **If empty types are unique, a discrete category is its own opposite**: its morphisms `y ⟶ x`
and `x ⟶ y` are those of `x` if `x = y`, and empty types otherwise. -/
theorem opCategory'_eq_of_isDiscrete (hE : EmptyUnique.{v}) (C : Cat.{v, u}) [IsDiscrete C] :
    opCategory' (Cat.str C) = Cat.str C :=
  category_eq_of_hom_eq _ _ fun x y => by
    by_cases h : x = y
    · subst h
      rfl
    · exact hE _ _ ⟨fun f => h (IsDiscrete.eq_of_hom (C := C) f).symm⟩
        ⟨fun f => h (IsDiscrete.eq_of_hom (C := C) f)⟩

theorem opFunctor'_obj_of_isDiscrete (hE : EmptyUnique.{v}) (C : Cat.{v, u}) [IsDiscrete C] :
    opFunctor'.obj C = C :=
  congrArg (@Cat.of C) (opCategory'_eq_of_isDiscrete hE C)

/-- **If empty types are unique, a functor into discrete categories is its own opposite**: the
opposite of each functor between discrete categories is that functor, as they agree on objects. -/
theorem comp_opFunctor'_of_isDiscrete (hE : EmptyUnique.{v}) {Γ : Type u₁} [Category.{v₁} Γ]
    (A : Γ ⥤ Cat.{v, u}) (hA : ∀ γ, IsDiscrete (A.obj γ)) : A ⋙ opFunctor' = A :=
  Functor.hext (fun γ => @opFunctor'_obj_of_isDiscrete hE (A.obj γ) (hA γ)) fun γ γ' f =>
    @catHom_heq_of_obj _ _ _ _ _ _ (@opCategory'_eq_of_isDiscrete hE (A.obj γ) (hA γ))
      (@opCategory'_eq_of_isDiscrete hE (A.obj γ') (hA γ'))
      (fun x y => (hA γ').subsingleton x y) (opFunctor'.map (A.map f)) (A.map f) fun _ => rfl

end CategoryTheory
