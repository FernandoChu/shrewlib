import Displayed.CodCatEquiv.Fibration

/-!
# Displayed categories and functors into the base

In this folder we compare two categories displayed over `Cat`:

* `DisplayedCat` (`Displayed/Displayed/DisplayedCat.lean`): the displayed categories over `A`, and
  the displayed functors over `u`;
* `cod Cat` (`Displayed/Displayed/Codomain.lean`): the functors `p : E ⥤ A`, and the commuting
  squares over `u`.

There are two vertical functors over `Cat` between them, `total : DisplayedCat ⟶ cod Cat` and
`fibresFunctor : cod Cat ⟶ DisplayedCat`, and they form an equivalence over `Cat`
(`DisplayedCat.codEquiv`): displayed categories over `A` are the functors into `A`.

The files give its ingredients:

* `Total`: the functor `total`, sending `D` to the projection `π : D.Total ⥤ A`.
* `Fibres`: the functor `fibresFunctor`, sending `p` to the displayed category of its fibres.
* `Equivalence`: the unit and counit, the equivalence `codEquiv`, and hence that `total` is fully
  faithful.
* `Fibration`: `total` sends the chosen lifts of the split fibration `DisplayedCat` to pullback
  squares, and `cod Cat` is a fibration, by transfer along `codEquiv`. It is not split. Both follow
  from the equivalence.
-/

universe v u

open CategoryTheory Displayed

/-! ## Main results -/

/-- **Displayed categories over `A` are the functors into `A`**: taking total categories is an
equivalence over `Cat`, with inverse taking fibres. -/
recall Displayed.DisplayedCat.codEquiv : VertEquivalence DisplayedCat.{v, u, v, u} (cod Cat.{v, u})

/-- Taking total categories is fully faithful. -/
recall Displayed.DisplayedCat.totalFullyFaithful : DisplayedCat.total.{v, u}.FullyFaithful

/-- Taking total categories sends the chosen lifts of `DisplayedCat` to pullback squares. -/
recall Displayed.DisplayedCat.isCartesianTotalMapClift {A B : Cat.{v, u}} {u : A ⟶ B}
    {E : Displayed.{v, u} B} :
    IsCartesian (DisplayedCat.total.map (DisplayedCat.clift u E))

/-- `cod Cat` is a fibration, by transfer along `DisplayedCat.codEquiv`. It is not split. -/
recall Displayed.DisplayedCat.fibCodCat : Fib (cod Cat.{v, u})
