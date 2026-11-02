import ComprehensionCategory.Model.Cat.Discrete
import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# The strictly involutive opposite of a category

`opFunctor' : Cat ⥤ Cat` sends a category to its opposite, and `opFunctor' ⋙ opFunctor' = 𝟭 Cat`
holds by `rfl` (`opFunctor'_comp_opFunctor'`). Mathlib's `Cat.opFunctor` is involutive only up to
isomorphism (`Cat.opFunctorInvolutive`): `Cᵒᵖᵒᵖ` is the type `Opposite (Opposite C)`, not `C`. So
`opFunctor'.obj C` is instead the opposite category structure on the type of `C` itself
(`opCategory'`), with the morphisms `y ⟶ x` of `C` as morphisms from `x` to `y`. Its double
opposite is `C` by eta for structures and functions, and so is that of a functor. It is naturally
isomorphic to `Cat.opFunctor`, by `op` and `unop` (`opFunctor'Iso`).

This file imports no rewrite rules, and must not. With the category laws as rules, the laws of
`opCategory'` cannot be checked: in `𝟙 x ≫ f`, composed in the structure being defined, the rule
`Category.id_comp` is selected but does not match, as the structure is not of the form
`Category.toCategoryStruct _`, and the composite is then not unfolded, in the elaborator or the
kernel. Once defined, composites in `opCategory' c` are composites in
`Category.toCategoryStruct (opCategory' c)`, on which the rules apply.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory

/-- The opposite category structure on the type `C` itself: a morphism from `x` to `y` is a
morphism `y ⟶ x` of `c`. Unlike the category `Cᵒᵖ`, its double opposite is `c` definitionally. -/
@[instance_reducible]
def opCategory' {C : Type u} (c : Category.{u} C) : Category.{u} C where
  Hom x y := y ⟶ x
  id x := 𝟙 x
  comp f g := g ≫ f
  id_comp := Category.comp_id
  comp_id := Category.id_comp
  assoc f g h := (Category.assoc h g f).symm

/-- **The opposite functor** `Cat ⥤ Cat`, sending a category to the opposite structure on its
objects, and a functor to the functor with the same components. -/
def opFunctor' : Cat.{u, u} ⥤ Cat.{u, u} where
  obj C := @Cat.of C (opCategory' (Cat.str C))
  map F := Cat.Hom.ofFunctor
    { obj X := F.toFunctor.obj X
      map f := F.toFunctor.map f
      map_id X := F.toFunctor.map_id X
      map_comp f g := F.toFunctor.map_comp g f }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The opposite functor is involutive on the nose.** -/
theorem opFunctor'_comp_opFunctor' : opFunctor'.{u} ⋙ opFunctor' = 𝟭 _ :=
  rfl

/-- The opposite of `C` is Mathlib's `Cᵒᵖ`: `x ↦ op x`, with inverse `unop`. The two composites are
identities by eta for `Opposite`. -/
def opFunctor'ObjIso (C : Cat.{u, u}) : opFunctor'.obj C ≅ Cat.opFunctor.obj C where
  hom := Cat.Hom.ofFunctor
    { obj X := Opposite.op X
      map f := Quiver.Hom.op f
      map_id _ := rfl
      map_comp _ _ := rfl }
  inv := Cat.Hom.ofFunctor
    { obj X := Opposite.unop X
      map f := Quiver.Hom.unop f
      map_id _ := rfl
      map_comp _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The opposite functor is Mathlib's `Cat.opFunctor`**, up to a natural isomorphism. -/
def opFunctor'Iso : opFunctor'.{u} ≅ Cat.opFunctor :=
  NatIso.ofComponents opFunctor'ObjIso fun _ => rfl

/-! ## Discrete categories are self-opposite

The discrete categories `discrete' S` of `ComprehensionCategory/Model/Cat/Discrete` are their own
opposites, by `propext`: `t = s` and `s = t` are different types. -/

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

end ComprehensionCategory.CatModel
