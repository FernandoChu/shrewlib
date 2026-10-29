import Displayed.Displayed.DisplayedCat
import Displayed.Fibration.Basic

/-!
# Reindexing in `DisplayedCat` goes to pullbacks

Taking total categories, `DisplayedCat.total : DisplayedCat ⟶ cod Cat`, sends the morphism
`DisplayedCat.clift u E : DisplayedCat.pull u E ⟶[u] E` out of the reindexing to a cartesian
morphism of `cod Cat` (`DisplayedCat.isCartesianTotalMapClift`): the total category of
`DisplayedCat.pull u E` is the pullback of `E.Total` along `u`.
-/

universe v₁ u₁ u

open CategoryTheory

namespace Displayed.DisplayedCat

open scoped Displayed

variable {A B : Cat.{u, u}} {u : A ⟶ B} {E : Displayed.{u, u, u, u} B}

/-- **Reindexing goes to pullbacks**: `(pull u E).Total` is the pullback of `E.Total` along `u`.
The factorization of a functor `χ : Z ⥤ E.Total` over `r ⋙ g ⋙ u` has the same displayed
components, read as a lift over `r ⋙ g` into `pull u E`. -/
def isCartesianTotalMapClift : IsCartesian (total.map (clift u E)) where
  lift g z χ := ⟨(TotalLift.ofFunctor χ.1.toFunctor
    (show χ.1.toFunctor ⋙ E.π = (z.hom.toFunctor ⋙ g.toFunctor) ⋙ u.toFunctor from
      congrArg Cat.Hom.toFunctor χ.2)).toPull.functor.toCatHom, rfl⟩
  lift_fac _ _ _ := CodHom.ext (Cat.Hom.ext
    ((TotalLift.toPull_functor_comp _).trans (TotalLift.functor_ofFunctor _ _)))
  lift_uniq {_ g z _} ψ hψ := by
    subst hψ
    exact CodHom.ext (Cat.Hom.ext ((congrArg TotalLift.functor (TotalLift.toPull_ofFunctor
      ψ.1.toFunctor (show ψ.1.toFunctor ⋙ (pull u E).π = z.hom.toFunctor ⋙ g.toFunctor from
        congrArg Cat.Hom.toFunctor ψ.2) _)).trans (TotalLift.functor_ofFunctor _ _)).symm)

end Displayed.DisplayedCat
