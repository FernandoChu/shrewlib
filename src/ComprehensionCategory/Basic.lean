import Displayed.Displayed.Codomain

/-!
# Comprehension categories

A comprehension category over `C` (Jacobs, *Comprehension categories and the semantics of type
dependency*), here in displayed form, is a fibration `D` over `C`, whose objects over `Γ` are
thought of as types in context `Γ`, with a vertical functor `compr : D ⟶ cod C` to the codomain
displayed category that preserves cartesian morphisms. It sends a type `A` over `Γ` to a morphism
`𝐩 A : Γ ▹ A ⟶ Γ`, the projection out of the extended context, and the chosen lift of
`σ : Δ ⟶ Γ` at `A` to the pullback square

```
  Δ ▹ A⦃σ⦄ --𝐪(σ, A)--> Γ ▹ A
      |                    |
   𝐩 A⦃σ⦄                 𝐩 A
      |                    |
      v                    v
      Δ ---------σ-------> Γ
```

We provide:

* the class `Comprehension D` of comprehension structures on a fibration `[Fib D]`, and the
  class `FullComprehension D` of inverses to its comprehension functor on hom-types;
* split comprehension categories, `SplitComprehension D`: a comprehension structure on a split
  fibration (`SplitFib D`). A full split comprehension category is
  `[SplitComprehension D] [FullComprehension D]`;
* `Comprehension.ofClift`: it suffices that the chosen lifts go to cartesian morphisms;
* the extended context `D.ext A`, the projection `D.proj A : D.ext A ⟶ Γ`, and the morphism
  `D.q σ A : D.ext (D.pull σ A) ⟶ D.ext A` with its pullback square (`isPullback_q`).

## Notation

Scoped in `Displayed`, so as to read as on paper:

* `D.Ty Γ`, the types in context `Γ` (an abbreviation of `D.Ob Γ`);
* `Γ ▹ A` for the extended context `D.ext A`, which is left associative: `Γ ▹ A ▹ B`;
* `A⦃σ⦄` for the substitution `D.pull σ A` of `A` along `σ : Δ ⟶ Γ`;
* `𝐩 A` for the projection `D.proj A : Γ ▹ A ⟶ Γ`;
* `𝐪(σ, A)` for `D.q σ A : Δ ▹ A⦃σ⦄ ⟶ Γ ▹ A`.

They are notations for the existing terms, so that the rules see no new constants, and they are
displayed back in goals. The displayed category `D` is inferred from the type of `A`: when it is
not syntactically `D.Ob Γ` or `D.Ty Γ`, as for the functors `Γ ⥤ Cat` of the category model, the
explicit forms `D.ext A`, … are needed.
-/

universe v u v₂ u₂

open CategoryTheory Limits

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- The types in context `Γ`: the objects of `D` over `Γ`. -/
abbrev Ty (D : Displayed.{v, u, v₂, u₂} C) (Γ : C) : Type u₂ := D.Ob Γ

/-- A comprehension category structure on a cloven fibration `D` over `C`: a vertical functor to
the codomain displayed category `cod C` that preserves cartesian morphisms, that is, sends them to
pullback squares. It takes the cleavage as a parameter, so that the same class serves for split
comprehension categories, over a `SplitFib D`. -/
class Comprehension (D : Displayed.{v, u, v₂, u₂} C) [Fib D] where
  /-- The comprehension functor. -/
  compr : VertFunctor D (cod C)
  /-- The comprehension functor preserves cartesian morphisms. -/
  isCartesianComprMap : ∀ {a a' : C} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y},
    IsCartesian φ → IsCartesian (compr.map φ)

/-- A comprehension category is *full* if its comprehension functor is fully faithful. This is
the data of an inverse on each displayed hom-type (`VertFunctor.FullyFaithful`), over a
`Comprehension D`, so that it combines with `SplitComprehension D`. -/
class FullComprehension (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] where
  /-- The comprehension functor is fully faithful. -/
  comprFullyFaithful : (Comprehension.compr (D := D)).FullyFaithful

/-- A split comprehension category: a comprehension category whose fibration is split. As for
`SplitFib`, the split fibration is an instance field, so that the comprehension structure is
stated over it. A full split comprehension category is a `SplitComprehension D` with
`FullComprehension D`. -/
class SplitComprehension (D : Displayed.{v, u, v₂, u₂} C) where
  /-- The underlying split fibration. -/
  [toSplitFib : SplitFib D]
  /-- The comprehension structure. -/
  [toComprehension : Comprehension D]

attribute [instance_reducible, instance] SplitComprehension.toSplitFib
  SplitComprehension.toComprehension

/-- A comprehension structure from a vertical functor that sends the chosen lifts to cartesian
morphisms. -/
@[instance_reducible]
def Comprehension.ofClift {D : Displayed.{v, u, v₂, u₂} C} [Fib D] (P : VertFunctor D (cod C))
    (hP : ∀ {a a' : C} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (P.map (D.clift f y))) :
    Comprehension D where
  compr := P
  isCartesianComprMap H := P.isCartesianMapOfClift hP H

section Comprehension

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] {a a' : C}

/-- The comprehension functor of `D`. -/
def compr : VertFunctor D (cod C) := Comprehension.compr

/-- The comprehension functor preserves cartesian morphisms. -/
def isCartesianComprMap {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsCartesian φ) : IsCartesian ((D.compr).map φ) :=
  Comprehension.isCartesianComprMap H

/-- The extension `D.ext x` of the context `a` by `x`. -/
def ext (x : D.Ob a) : C := ((D.compr).obj x).dom

/-- The projection `D.proj x : D.ext x ⟶ a`. -/
def proj (x : D.Ob a) : D.ext x ⟶ a := ((D.compr).obj x).hom

/-- The action of the comprehension functor on a morphism over `f`, between extended contexts. -/
def extMap {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) : D.ext x ⟶ D.ext y :=
  ((D.compr).map φ).1

theorem extMap_proj {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.extMap φ ≫ D.proj y = D.proj x ≫ f :=
  ((D.compr).map φ).2

theorem extMap_id (x : D.Ob a) : D.extMap (𝟙ᵈ x) = 𝟙 (D.ext x) := rfl

theorem extMap_comp {a'' : C} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.extMap (φ ≫ᵈ ψ) = D.extMap φ ≫ D.extMap ψ := rfl

/-- The image of a cartesian morphism is a pullback square. -/
theorem isPullback_extMap {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsCartesian φ) : IsPullback (D.extMap φ) (D.proj x) (D.proj y) f :=
  cod.isPullback_of_isCartesian (D.isCartesianComprMap H)

/-- The morphism `D.q σ x : D.ext (D.pull σ x) ⟶ D.ext x` over `σ : a ⟶ a'`, the image of the
chosen lift. -/
def q (σ : a ⟶ a') (x : D.Ob a') : D.ext (D.pull σ x) ⟶ D.ext x := D.extMap (D.clift σ x)

end Comprehension

/-! ## Notation -/

/-- `Γ ▹ A` is the extension `D.ext A` of the context `Γ` by the type `A`. -/
scoped notation:65 Γ:65 " ▹ " A:66 => Displayed.ext _ (a := Γ) A

/-- `A⦃σ⦄` is the substitution `D.pull σ A` of the type `A` along `σ`. -/
scoped syntax:max term:max noWs "⦃" term "⦄" : term

scoped macro_rules | `($A⦃$σ⦄) => `(Displayed.pull _ $σ $A)

/-- `𝐩 A` is the projection `D.proj A : Γ ▹ A ⟶ Γ`. -/
scoped notation:max "𝐩 " A:max => Displayed.proj _ A

/-- `𝐪(σ, A)` is the morphism `D.q σ A : Δ ▹ A⦃σ⦄ ⟶ Γ ▹ A` over `σ`. -/
scoped notation:max "𝐪(" σ ", " A ")" => Displayed.q _ σ A

open Lean PrettyPrinter Delaborator SubExpr in
/-- Displays `D.ext A`, for `A` over `Γ`, as `Γ ▹ A`. -/
@[scoped delab app.Displayed.ext]
def delabExt : Delab := whenPPOption getPPNotation <| withOverApp 7 do
  let Γ ← withNaryArg 5 delab
  let A ← withNaryArg 6 delab
  `($Γ ▹ $A)

/-- Displays `D.pull σ A` as `A⦃σ⦄`. -/
@[scoped app_unexpander Displayed.pull]
def unexpandPull : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $σ $A) => `($A⦃$σ⦄)
  | _ => throw ()

/-- Displays `Fib.pull σ A` as `A⦃σ⦄`. -/
@[scoped app_unexpander Fib.pull]
def unexpandFibPull : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $A) => `($A⦃$σ⦄)
  | _ => throw ()

/-- Displays `D.proj A` as `𝐩 A`. -/
@[scoped app_unexpander Displayed.proj]
def unexpandProj : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $A) => `(𝐩 $A)
  | _ => throw ()

/-- Displays `D.q σ A` as `𝐪(σ, A)`. -/
@[scoped app_unexpander Displayed.q]
def unexpandQ : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $σ $A) => `(𝐪($σ, $A))
  | _ => throw ()

section Substitution

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] {Δ Γ : C}

theorem q_proj (σ : Δ ⟶ Γ) (A : D.Ty Γ) : 𝐪(σ, A) ≫ 𝐩 A = 𝐩 A⦃σ⦄ ≫ σ :=
  D.extMap_proj (D.clift σ A)

/-- **Substitution is pullback**: `Δ ▹ A⦃σ⦄` is the pullback of `𝐩 A` along `σ`. -/
theorem isPullback_q (σ : Δ ⟶ Γ) (A : D.Ty Γ) : IsPullback 𝐪(σ, A) 𝐩 A⦃σ⦄ (𝐩 A) σ :=
  D.isPullback_extMap (D.isCartesianClift σ A)

end Substitution

section FullComprehension

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] [FullComprehension D]
  {a a' : C}

/-- In a full comprehension category, morphisms over `f` are the morphisms between extended
contexts that commute with the projections. -/
def comprHomEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.compr).obj x ⟶[f] (D.compr).obj y) where
  toFun := (D.compr).map
  invFun := FullComprehension.comprFullyFaithful.preimage
  left_inv := FullComprehension.comprFullyFaithful.preimage_map
  right_inv := FullComprehension.comprFullyFaithful.map_preimage

end FullComprehension

end Displayed
