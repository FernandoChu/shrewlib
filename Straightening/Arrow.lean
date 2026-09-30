import Nfib.Displayed.Fibration
import Mathlib.CategoryTheory.Category.Cat

/-!
# The arrow category `Cat^→`, displayed over `Cat`

The arrow category of `Cat`, fibred over `Cat` by the codomain, as a displayed category: an object
over `A` is a small category `E` with a functor `p : E ⥤ A`, and a morphism over `u : A ⟶ B` from
`(E, p)` to `(E', p')` is a functor `w : E ⥤ E'` with `w ⋙ p' = p ⋙ u`. Its total category is the
arrow category `Cat^→`, and its projection is the codomain functor.

The laws hold by `rfl`, since composition of functors is definitionally associative and unital.
-/

universe u

namespace Straightening

open CategoryTheory Nfib

/-- An object of `Cat^→` over `A`: a small category with a functor to `A`. -/
structure ArrOb (A : Cat.{u, u}) where
  /-- The domain category. -/
  dom : Cat.{u, u}
  /-- The functor to `A`. -/
  proj : dom ⥤ A

/-- A morphism of `Cat^→` over `u : A ⟶ B`: a functor between the domains making the square
commute on the nose. -/
def ArrHom {A B : Cat.{u, u}} (u : A ⟶ B) (X : ArrOb A) (Y : ArrOb B) : Type u :=
  { w : X.dom ⥤ Y.dom // w ⋙ Y.proj = X.proj ⋙ u.toFunctor }

theorem ArrHom.ext {A B : Cat.{u, u}} {u : A ⟶ B} {X : ArrOb A} {Y : ArrOb B} {w w' : ArrHom u X Y}
    (h : w.1 = w'.1) : w = w' :=
  Subtype.ext h

/-- `Cat^→` as a category displayed over `Cat` by the codomain. -/
def Arr : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob := ArrOb
  Hom := ArrHom
  id X := ⟨𝟭 _, rfl⟩
  comp {_ _ _ u v X Y Z} w w' := ⟨w.1 ⋙ w'.1, by
    obtain ⟨w, hw⟩ := w
    obtain ⟨w', hw'⟩ := w'
    change w ⋙ (w' ⋙ Z.proj) = (X.proj ⋙ u.toFunctor) ⋙ v.toFunctor
    rw [hw', ← hw]; rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end Straightening
