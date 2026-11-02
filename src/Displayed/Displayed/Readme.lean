import Displayed.Displayed.Basic
import Displayed.Displayed.Functor
import Displayed.Displayed.DisplayedCat
import Displayed.Displayed.Equivalence
import Displayed.Displayed.Total
import Displayed.Displayed.Sigma
import Displayed.Displayed.Codomain

/-!
# Displayed categories in general

* `Basic`: displayed categories `Displayed A` over `A`, their fibers `Fiber`, displayed functors
  `DispFunctor u` over a functor `u` between the bases, vertical functors `VertFunctor`, the
  displayed functors over `𝟭 A`, and vertical natural transformations `VertNatTrans`.
* `Functor`: the functors that displayed functors induce between total categories, and functors
  into a total category given by their displayed components (`TotalLift`).
* `DisplayedCat`: the displayed categories and displayed functors, displayed over `Cat`, the
  fully faithful functor `DisplayedCat ⟶ cod Cat` taking total categories, and reindexing.
* `Equivalence`: equivalences over the base (`VertEquivalence`), which are fully faithful.
* `Total`: the total category `D.Total`, `π`, `ι`, and the induced functors, natural
  transformations and equivalences of total categories.
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
