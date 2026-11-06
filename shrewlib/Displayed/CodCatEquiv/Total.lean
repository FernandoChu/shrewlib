import Displayed.Displayed.Total
import Displayed.Displayed.DisplayedCat
import Displayed.Displayed.Codomain

/-!
# Taking total categories

Taking total categories is a vertical functor `DisplayedCat.total : DisplayedCat ⟶ cod Cat`,
sending `D` to the projection `π : D.Total ⥤ A`, and a displayed functor over `u` to the functor
it induces between the total categories (`DispFunctor.total`).

It is an equivalence, with inverse taking fibres, in `CodCatEquiv/Equivalence`; in particular it is
fully faithful (`DisplayedCat.totalFullyFaithful`).
-/

universe u

open CategoryTheory

namespace Displayed.DisplayedCat

open scoped Displayed

section Total

variable {A B : Cat.{u, u}}

/-- The total category of `D`, with its projection, as an object of `cod Cat`. -/
def totalObj (D : Displayed.{u, u, u, u} A) : (cod Cat.{u, u}).Ob A :=
  ⟨Cat.of D.Total, D.π.toCatHom⟩

/-- The functor between total categories induced by a displayed functor over `u`. -/
def totalMap {u : A ⟶ B} {D : Displayed.{u, u, u, u} A} {E : Displayed.{u, u, u, u} B}
    (H : DispFunctor u.toFunctor D E) : totalObj D ⟶[u] totalObj E :=
  ⟨H.total.toCatHom, rfl⟩

/-- **Taking total categories**, a vertical functor into `cod Cat`. -/
def total : VertFunctor DisplayedCat.{u} (cod Cat.{u, u}) where
  obj D := totalObj D
  map H := totalMap H

end Total

end Displayed.DisplayedCat
