import Displayed.Displayed.DisplayedCat
import Displayed.Displayed.Codomain
import Mathlib.CategoryTheory.EqToHom

/-!
# Taking fibres

Taking fibres is a vertical functor `DisplayedCat.fibresFunctor : cod Cat ⟶ DisplayedCat`. It sends
`p : E ⥤ A` to the displayed category of its fibres `fibres X`: the objects over `a` are the objects
`e` of `E` with `p e = a` (`Fibre X a`), and the morphisms over `f` are the morphisms of `E` that
`p` sends to `f` (`FibreHom X f`). A commuting square `w ⋙ p' = p ⋙ u` is sent to the restriction
of `w` to the fibres. It is the inverse of `DisplayedCat.total`, in `CodCatEquiv/Equivalence`.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

namespace DisplayedCat

section Fibres

variable {A : Cat.{u, u}} (X : (cod Cat.{u, u}).Ob A)

/-- The fibre of `p : E ⥤ A` over `a`, on objects. -/
def Fibre (a : A) : Type u := { e : X.dom // X.hom.toFunctor.obj e = a }

/-- The morphisms of `E` over `f`, between objects of the fibres. -/
def FibreHom {a a' : A} (f : a ⟶ a') (x : Fibre X a) (y : Fibre X a') : Type u :=
  { g : x.1 ⟶ y.1 // X.hom.toFunctor.map g ≫ eqToHom y.2 = eqToHom x.2 ≫ f }

variable {X}

/-- Composition of morphisms over base morphisms. -/
def FibreHom.comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fibre X a} {y : Fibre X a'}
    {z : Fibre X a''} (s : FibreHom X f x y) (t : FibreHom X g y z) : FibreHom X (f ≫ g) x z :=
  ⟨s.1 ≫ t.1, ((congrArg (X.hom.toFunctor.map s.1 ≫ ·) t.2).trans (congrArg (· ≫ g) s.2) :)⟩

/-- A morphism over `f` lies over `f` up to the identifications of the fibres. -/
theorem FibreHom.proj_map {a a' : A} {f : a ⟶ a'} {x : Fibre X a} {y : Fibre X a'}
    (s : FibreHom X f x y) : X.hom.toFunctor.map s.1 = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  exact s.2

/-- Morphisms over equal base morphisms with the same underlying morphism of `E` are
heterogeneously equal. -/
theorem FibreHom.heq_of_val {a a' : A} {f f' : a ⟶ a'} (h : f = f') {x : Fibre X a}
    {y : Fibre X a'} (s : FibreHom X f x y) (t : FibreHom X f' x y) (hv : s.1 = t.1) : s ≍ t := by
  subst h
  exact heq_of_eq (Subtype.ext hv)

variable (X) in
/-- The fibres of `p : E ⥤ A`, displayed over `A`: the objects over `a` are those of
`Fibre X a`, and the morphisms over `f` are the morphisms of `E` over `f`. -/
def fibres : Displayed.{u, u, u, u} A where
  Ob a := Fibre X a
  Hom f x y := FibreHom X f x y
  id x := ⟨𝟙 x.1, rfl⟩
  comp s t := FibreHom.comp s t

theorem fibres.comp_val {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : Fibre X a}
    {y : Fibre X a'} {z : Fibre X a''} (s : (fibres X).Hom f x y) (t : (fibres X).Hom g y z) :
    Subtype.val (s ≫ᵈ t : FibreHom X (f ≫ g) x z) =
      Subtype.val (s : FibreHom X f x y) ≫ Subtype.val (t : FibreHom X g y z) :=
  rfl

/-- A commuting square `w ⋙ p' = p ⋙ u` restricts to the fibres. -/
theorem proj_map_map {B : Cat.{u, u}} {u : A ⟶ B} {Y : (cod Cat.{u, u}).Ob B} (w : X ⟶[u] Y)
    {a a' : A}
    {f : a ⟶ a'} {x : Fibre X a} {y : Fibre X a'} (s : FibreHom X f x y)
    (hx : Y.hom.toFunctor.obj (w.1.toFunctor.obj x.1) = u.toFunctor.obj a)
    (hy : Y.hom.toFunctor.obj (w.1.toFunctor.obj y.1) = u.toFunctor.obj a') :
    Y.hom.toFunctor.map (w.1.toFunctor.map s.1) ≫ eqToHom hy = eqToHom hx ≫ u.toFunctor.map f := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  obtain ⟨s, hs⟩ := s
  obtain rfl : X.hom.toFunctor.map s = f := hs
  have := Functor.congr_hom (show w.1.toFunctor ⋙ Y.hom.toFunctor = X.hom.toFunctor ⋙ u.toFunctor
    from congrArg Cat.Hom.toFunctor w.2) s
  rw [Functor.comp_map] at this
  rw [this]
  exact congrArg (fun t => eqToHom hx ≫ u.toFunctor.map (X.hom.toFunctor.map s) ≫ t)
    ((eqToHom_trans _ hy).trans (eqToHom_refl _ _))

/-- The restriction of a commuting square to the fibres, a displayed functor over `u`. -/
def fibresMap {B : Cat.{u, u}} {u : A ⟶ B} {Y : (cod Cat.{u, u}).Ob B} (w : X ⟶[u] Y) :
    DispFunctor u.toFunctor (fibres X) (fibres Y) where
  obj x := ⟨w.1.toFunctor.obj x.1, (Functor.congr_obj (congrArg Cat.Hom.toFunctor w.2) x.1).trans
    (congrArg u.toFunctor.obj x.2)⟩
  map s := ⟨w.1.toFunctor.map s.1, proj_map_map w s _ _⟩

end Fibres

/-- **Taking fibres**, a vertical functor from `cod Cat`. -/
def fibresFunctor : VertFunctor (cod Cat.{u, u}) DisplayedCat.{u} where
  obj X := fibres X
  map w := fibresMap w

end DisplayedCat

end Displayed
