import Displayed.Displayed.Basic
import Displayed.Displayed.Functor
import Displayed.Displayed.DisplayedCat
import Displayed.Displayed.Equivalence
import Displayed.Displayed.Total
import Displayed.Displayed.Sigma
import Displayed.Displayed.Codomain
import Displayed.Displayed.Straightening.Readme

/-!
# Displayed categories in general

* `Basic`: displayed categories `Displayed A` over `A`, their fibers `Fiber`, vertical functors
  `VertFunctor` and vertical natural transformations `VertNatTrans`.
* `Functor`: displayed functors `DispFunctor u` over a functor `u` between the bases, and the
  functors they induce between total categories.
* `DisplayedCat`: the displayed categories and displayed functors, displayed over `Cat`, and the
  fully faithful functor `DisplayedCat ⟶ cod Cat` taking total categories, which sends
  reindexings to pullbacks.
* `Equivalence`: equivalences over the base (`VertEquivalence`), which are fully faithful.
* `Total`: the total category `D.Total`, `π`, `ι`, and the induced functors, natural
  transformations and equivalences of total categories.
* `Sigma`: the composite `D.sigmaDisp E` over `A` of `D` over `A` and `E` over `D.Total`, whose
  total category is that of `E`, up to reassociation.
* `Codomain`: the codomain displayed category `cod C`.
* `Straightening/`: straightening–unstraightening for displayed categories.
-/

universe v₁ u₁ v u

open CategoryTheory Limits Displayed

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

/-- The cartesian morphisms of `cod C` are the pullback squares. -/
recall Displayed.cod.isLimitOfIsCartesian {C : Type u} [Category.{v} C] {a a' : C}
    {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} {φ : x ⟶[f] y} (H : IsCartesian φ) :
    IsLimit (cod.cone φ)

recall Displayed.cod.isCartesianOfIsLimit {C : Type u} [Category.{v} C] {a a' : C}
    {f : a ⟶ a'} {x : (cod C).Ob a} {y : (cod C).Ob a'} {φ : x ⟶[f] y}
    (P : IsLimit (cod.cone φ)) : IsCartesian φ

/-- With chosen pullbacks, `cod C` is a fibration. -/
recall Displayed.cod.fib {C : Type u} [Category.{v} C] [ChosenPullbacks C] : Fib (cod C)
