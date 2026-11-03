import ComprehensionCategory.Model.OverCat.Cat.Readme
import ComprehensionCategory.Model.OverCat.Discrete.Readme
import ComprehensionCategory.Model.OverCat.Displayed.Readme
import ComprehensionCategory.Model.OverCat.Maps.Readme
import ComprehensionCategory.Model.OverCat.Shared.Readme

/-!
# Models over `Cat`

Three full split comprehension categories over `Cat`, one folder each, with a `Readme.lean`:

* `Cat/`: the category model `ICatLax`, whose types in context `Γ` are the functors `Γ ⥤ Cat`, and
  whose context extension `Γ ▹ A` is the total category of the unstraightening of `A`. It has
  Σ-types, opposite types, and a Coquand-style universe of the types of a lower level, the
  functors into smaller categories, which form a comprehension category `SmallICat`.
* `Discrete/`: the discrete model `IDisc`, the full sub-comprehension category of the category
  model on the functors into discrete categories. It has Σ-types and opposite types, those of the
  category model.
* `Displayed/`: the displayed category model `LaxNormalCat`, whose types are the lax normal functors
  into profunctors, with the equivalence `LaxNormalCat ≃ cod Cat` as comprehension functor. It has
  Σ-types.

Two more folders relate them:

* `Shared/`: type formers relating the models: the Hom-types of the category model are types of
  the discrete model, the category model has a Coquand-style universe of the discrete types, and
  the twist of a type of the category model, contravariant in its last variable, is a type of the
  displayed model, covariant in it, which gives the twisted Hom-types and their term `refl`.
* `Maps/`: maps of comprehension categories between the models, and their preservation of type
  formers: forgetting the discreteness is a strict map from the discrete model to the category
  model, preserving Σ-types and opposite types, and the lifts of the types of a lower level into the
  category model are strict maps, along which it has universes of them.

A result about a single model goes in its folder, a type former in the `TypeFormers/` folder of the
model of its types, or in `Shared/` if its premises are types of another model, and a result
relating two models in `Maps/`.
-/
