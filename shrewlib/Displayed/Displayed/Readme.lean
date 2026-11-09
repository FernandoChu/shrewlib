import Displayed.Displayed.Basic
import Displayed.Displayed.DisplayedCat
import Displayed.Displayed.Equivalence
import Displayed.Displayed.Total
import Displayed.Displayed.Sigma
import Displayed.Displayed.Codomain

/-!
# Displayed categories in general

* `Basic`: displayed categories `Displayed A` over `A`, their fibers `Fiber`, displayed functors
  `DispFunctor u` over a functor `u` between the bases, vertical functors `VertFunctor`, the
  displayed functors over `𝟭 A`, and vertical natural transformations `VertNatTrans`. Two displayed
  categories are equal if a vertical functor between them is the identity on objects and a cast on
  morphisms (`VertFunctor.eq_of_map_cast`).
* `DisplayedCat`: the displayed categories and displayed functors, displayed over `Cat`, and
  reindexing. Its equivalence with `cod Cat` is in `CodCatEquiv/`.
* `Equivalence`: equivalences over the base (`VertEquivalence`), which are fully faithful.
* `Total`: the total category `D.Total`, `π`, `ι`, and the functors that displayed functors induce
  between total categories, as well as the natural transformations and equivalences that vertical
  ones induce.
* `Sigma`: the composite `D.sigmaDisp E` over `A` of `D` over `A` and `E` over `D.Total`, whose
  total category is that of `E`, up to reassociation.
* `Codomain`: the codomain displayed category `cod C`, and the action `codMap F` of a functor on
  it. Its cartesian morphisms are in `Fibration/Codomain`.
-/

universe v₁ u₁

open CategoryTheory Displayed

open scoped Displayed

/-! ## Main results -/

/-- A vertical equivalence is fully faithful on the morphisms over each base morphism. -/
recall Displayed.VertEquivalence.map_injective {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    {φ φ' : x ⟶[f] y} (h : e.functor.map φ = e.functor.map φ') : φ = φ'

recall Displayed.VertEquivalence.map_surjective {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) {a a' : A} {f : a ⟶ a'} {x : D.Ob a}
    {y : D.Ob a'} (ψ : e.functor.obj x ⟶[f] e.functor.obj y) : ∃ φ, e.functor.map φ = ψ

/-- A vertical equivalence induces an equivalence of total categories, over the base. -/
recall Displayed.VertEquivalence.total {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) : D.Total ≌ E.Total

recall Displayed.VertEquivalence.total_functor_comp_π {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) : e.total.functor ⋙ E.π = D.π
