import Displayed.Displayed.Readme
import Displayed.Fibration.Readme
import Displayed.Opfibration.Readme
import Displayed.Straightening.Readme
import Displayed.CodCatEquiv.Readme
import Displayed.Discrete.Readme

/-!
# Displayed categories

Categories displayed over a category, whose laws are rules and hold as plain equations. Each
folder has a `Readme.lean`.

* `Displayed/`: displayed categories in general, vertical functors and equivalences, the total
  category and the codomain displayed category.
* `Opfibration/`: opcartesian morphisms and cloven, pre-split and split opfibrations, which
  compose;
  `Straightening/` is the equivalence over `Cat` between functors `A ⥤ Cat` and split
  opfibrations.
* `Fibration/`: cartesian morphisms and cloven, pre-split and split fibrations, which compose;
  `Straightening/` is the equivalence over `Cat` between functors `Aᵒᵖ ⥤ Cat` and split fibrations.
  It is the dual of `Opfibration/`.
* `Straightening/`: straightening–unstraightening for displayed categories, the isomorphism
  `LaxNormalCat ≅ DisplayedCat` over `Cat`, and the fibrations over `Cat` it gives.
* `CodCatEquiv/`: the equivalence `DisplayedCat ≃ cod Cat` over `Cat` taking total categories:
  displayed categories over `A` are the functors into `A`.
* `Discrete/`: discrete opfibrations; `Straightening/` is the equivalence over `Cat` between
  functors into discrete categories and discrete opfibrations, the restriction of that for split
  opfibrations.
-/
