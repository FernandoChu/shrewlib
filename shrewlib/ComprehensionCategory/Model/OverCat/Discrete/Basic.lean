import ComprehensionCategory.Model.OverCat.Cat.Basic
import Displayed.Discrete.Straightening.IDisc

/-!
# The discrete model

The *discrete model* is the comprehension category `IDisc` over `Cat`
(`Displayed/Discrete/Straightening/IDisc`) whose types in context `Γ` are the functors `Γ ⥤ Cat`
into discrete categories, and whose morphisms are those of the category model `ICatLax`: it is the
full sub-comprehension category of the category model on these types.

Its comprehension is that of the category model, along the functor `IDisc.forget : IDisc ⟶ ICatLax`
forgetting the discreteness, which preserves the chosen lifts on the nose, so the comprehension
functor `IDisc.forget ⋙ᵥ compr` preserves cartesian morphisms (`Comprehension.comap`). The extended
context `Γ ▹ A` is that of the category model, `Γ ⋉ A`: its objects are pairs `(γ, x)` with
`x : A γ`, and its morphisms `(γ, x) ⟶ (γ', x')` are the `f : γ ⟶ γ'` with `A f x = x'`, since
`A γ'` is discrete.

Forgetting the discreteness is fully faithful, so the discrete model is a full split comprehension
category. It is a strict map of comprehension categories from the discrete model to the category
model, since the comprehension functor of the discrete model is `IDisc.forget ⋙ᵥ compr` by
definition (`OverCat/Maps/DiscreteToCat`).

## Why not functors into sets

The evident choice of types is the functors `Γ ⥤ Type u`, with the natural transformations as
morphisms, and the comprehension of the category model along the embedding `E` into it that sends
`F` to the functor `γ ↦ discrete' (F γ)` into discrete categories. This is a full split
comprehension category, and `E` is a strict map of comprehension categories, both by `rfl`. It
has Σ-types: the unstraightenings of `E F` and `E G` are discrete opfibrations, and so is their
composite `X` (`DiscOpfibOb.sigma`), and `Σ[F] G` sends `γ` to the set `X.Ob γ` of objects of the
fibre of `X` over `γ`, with the pushforwards of `X`.

But `E` does not preserve these Σ-types strictly, as a submodel should. The Σ-type of `E F` and
`E G` in the category model is the straightening of the same `X`, which sends `γ` to the fibre
`X.Fiber γ` itself. So `E (Σ[F] G)` and `Σ[E F] (E G)` send `γ` to two categories with the same
objects, the pairs `p = ⟨x, y⟩` of `x : F γ` and `y : G (γ, x)`, but different morphisms `p ⟶ q`:

* in `discrete' (X.Ob γ)`, the proofs of `p = q`, in `ULift (PLift (p = q))`;
* in `X.Fiber γ`, the pairs of a proof `φ` of `x = x'` and a proof of `G (𝟙 γ, φ) y = y'`.

Both are subsingletons inhabited exactly when `p = q`, so the two categories are isomorphic, and
`E` preserves Σ-types up to a canonical isomorphism. But they are different types, and Lean
cannot prove them equal: `propext` identifies equivalent propositions, not equivalent types, which
would be univalence, inconsistent with Lean. The Σ-type of the category model keeps the category
structure that the composite builds, while a functor into sets forgets it, and `E` can only
rebuild the discrete category on the set of objects.

The same happens for every type former: each has to be built anew for the functors into sets, and
is related to that of the category model only up to isomorphism. The functors into discrete
categories keep their category structure, and discreteness is a proposition, so it is never
compared: a type former of the category model that preserves discreteness is one of the discrete
model, which `IDisc.forget` preserves by `rfl`. This is the case for Σ-types (`TypeFormers/Sigma`)
and opposite types (`TypeFormers/Op`).
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel

open scoped Displayed

/-! ## The comprehension structure -/

/-- The comprehension structure of the discrete model: that of the category model, along the
functor forgetting the discreteness. -/
@[instance_reducible]
instance comprehension : Comprehension IDisc.{u, u, u, u} :=
  Comprehension.comap IDisc.forget.toDispFunctor IDisc.forget.isCartesianMap

/-- **The discrete model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension IDisc.{u, u, u, u} where

@[instance_reducible]
instance fullComprehension : FullComprehension IDisc.{u, u, u, u} where
  comprFullyFaithful := IDisc.forgetFullyFaithful.comp comprFullyFaithful

end ComprehensionCategory.DiscreteModel
