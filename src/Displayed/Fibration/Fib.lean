import Displayed.Basic
import Displayed.Cartesian
import Displayed.Total
import Mathlib.Tactic.IrreducibleDef

/-!
# Fibrations

The exact dual of `Opfib.lean`, whose sections this file mirrors.

A `Fib` structure on a displayed category `D` is a cloven fibration: a chosen pullback `pull f y`
for every base morphism `f : a ⟶ a'` and object `y` over `a'`, and a chosen cartesian lift
`clift f y : pull f y ⟶[f] y`. A `PreSplitFib` adds the splitting axioms on objects,
`pull (𝟙 a) y = y` and `pull (f ≫ g) y = pull f (pull g y)`, which are rewrite rules. A `SplitFib`
adds the splitting axioms on lifts, `clift (𝟙 a) y = 𝟙ᵈ y` and
`clift (f ≫ g) y = clift f (pull g y) ≫ᵈ clift g y`. These are plain equations, since the rules on
objects make the domains agree definitionally, and are rules too.

From a `Fib` (or a (pre-)split one, where noted) we derive, all as rewrite rules:

* the vertical factorization `cartesianFactor φ : x ⟶ pull f y` of `φ : x ⟶[f] y` through the
  chosen lift, with `cartesianFactor φ ≫ᵈ clift f y = φ`;
* the fiber transport `pullMap f β : pull f x ⟶ pull f y`, its functoriality in `β`, and, for a
  `SplitFib`, in `f`, which hold on the nose;
* the interchange `clift f x ≫ᵈ β = pullMap f β ≫ᵈ clift f y`, oriented so that chosen lifts come
  last.

As for `pushMap`, `pullMap` is an `irreducible_def`, since the rules rewrite its definition back
into it. Composites are normalized to be right-associated, so the `_assoc` forms of the rules are
not literally dual to those of `Opfib.lean`: here the rules must also see `clift f y` followed by
further morphisms, as in `cartesianFactor φ ≫ᵈ (clift f y ≫ᵈ χ)` and `clift f x ≫ᵈ (β ≫ᵈ χ)`.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

open scoped Displayed

/-! ## The classes -/

/-- A (cloven) fibration structure on a displayed category: a chosen cartesian lift of every base
morphism at every object over its codomain. -/
class Fib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pullback of `y` along `f`. -/
  pull : {a a' : A} → (f : a ⟶ a') → D.Ob a' → D.Ob a
  /-- The chosen cartesian lift of `f` at `y`. -/
  clift : {a a' : A} → (f : a ⟶ a') → (y : D.Ob a') → (pull f y ⟶[f] y)
  /-- The chosen lifts are cartesian. -/
  clift_cartesian : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (clift f y)

/-- A pre-split fibration: a fibration whose chosen pullbacks are strictly functorial on objects.
These axioms are rewrite rules. -/
class PreSplitFib (D : Displayed.{v₁, u₁, v₂, u₂} A) extends Fib D where
  pull_id : ∀ {a : A} (y : D.Ob a), pull (𝟙 a) y = y
  pull_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    pull (f ≫ g) y = pull f (pull g y)

attribute [rewrite_rule] PreSplitFib.pull_id PreSplitFib.pull_comp

/-- A split fibration: a pre-split fibration whose chosen lifts are strictly functorial. As for
`SplitOpfib`, the pre-split structure is an instance field rather than a parent, so that the rules
`pull_id` and `pull_comp` apply to the axioms on lifts. -/
class SplitFib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The underlying pre-split fibration. -/
  [toPreSplitFib : PreSplitFib D]
  /-- The lift of the identity is the displayed identity. -/
  clift_id : ∀ {a : A} (y : D.Ob a), Fib.clift (𝟙 a) y = 𝟙ᵈ y
  /-- The lift of a composite is the composite of lifts. -/
  clift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    Fib.clift (f ≫ g) y = Fib.clift f (Fib.pull g y) ≫ᵈ Fib.clift g y

attribute [instance_reducible, instance] SplitFib.toPreSplitFib

attribute [rewrite_rule] SplitFib.clift_id SplitFib.clift_comp

/-! ## Chosen pullbacks and lifts -/

section Lift

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Fib D]

/-- The chosen pullback of `y` along `f`, viewed as an object of the fiber over `a`. -/
@[reducible] def pull {a a' : A} (f : a ⟶ a') (y : D.Ob a') : D.Fiber a :=
  Fib.pull f y

/-- The chosen cartesian lift of `f` at `y`. -/
def clift {a a' : A} (f : a ⟶ a') (y : D.Ob a') : (D.pull f y) ⟶[f] y := Fib.clift f y

theorem clift_cartesian {a a' : A} (f : a ⟶ a') (y : D.Ob a') :
    IsCartesian (D.clift f y) := Fib.clift_cartesian f y

end Lift

section LiftPreSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [PreSplitFib D]

@[rewrite_rule]
theorem pull_id {a : A} (y : D.Ob a) : D.pull (𝟙 a) y = y :=
  PreSplitFib.pull_id y

@[rewrite_rule]
theorem pull_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a'') :
    D.pull (f ≫ g) y = D.pull f (D.pull g y) :=
  PreSplitFib.pull_comp f g y

end LiftPreSplit

section LiftSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitFib D]

@[rewrite_rule]
theorem clift_id {a : A} (y : D.Ob a) : D.clift (𝟙 a) y = 𝟙ᵈ y := SplitFib.clift_id y

@[rewrite_rule]
theorem clift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a'') :
    D.clift (f ≫ g) y = D.clift f (D.pull g y) ≫ᵈ D.clift g y := SplitFib.clift_comp f g y

end LiftSplit

/-! ## Cartesian factorization -/

section Factor

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Fib D] {a a' a'' : A}

/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift `clift f y` by a
vertical morphism `x ⟶ pull f y`. -/
noncomputable def cartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    x ⟶[𝟙 a] (D.pull f y) :=
  IsCartesian.lift (D.clift_cartesian f y) (𝟙 a) φ

@[rewrite_rule]
theorem cartesianFactor_comp_clift {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.cartesianFactor φ ≫ᵈ D.clift f y = φ :=
  IsCartesian.lift_fac (D.clift_cartesian f y) (𝟙 a) φ

@[rewrite_rule]
theorem cartesianFactor_comp_clift_assoc {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (χ : y ⟶[g] z) :
    D.cartesianFactor φ ≫ᵈ (D.clift f y ≫ᵈ χ) = φ ≫ᵈ χ :=
  congrArg (· ≫ᵈ χ) (D.cartesianFactor_comp_clift φ)

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with `cartesianFactor φ`. -/
theorem cartesianFactor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : x ⟶[𝟙 a] (D.pull f y)) (h : β ≫ᵈ D.clift f y = φ) : β = D.cartesianFactor φ :=
  IsCartesian.lift_uniq (D.clift_cartesian f y) β h

@[rewrite_rule]
theorem cartesianFactor_clift (f : a ⟶ a') (y : D.Ob a') :
    D.cartesianFactor (D.clift f y) = 𝟙ᵈ (D.pull f y) :=
  (D.cartesianFactor_uniq (D.clift f y) (𝟙ᵈ _) rfl).symm

/-- The hom-set bijection defining a fibration: `(x ⟶[f] y) ≃ (x ⟶ pull f y)`. -/
noncomputable def cartesianHomEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ (x ⟶[𝟙 a] (D.pull f y)) where
  toFun φ := D.cartesianFactor φ
  invFun β := β ≫ᵈ D.clift f y
  left_inv _ := rfl
  right_inv β := (D.cartesianFactor_uniq _ β rfl).symm

end Factor

section FactorSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitFib D] {a : A}

/-- The factorization of a vertical morphism is the morphism itself. -/
@[rewrite_rule]
theorem cartesianFactor_vert {x y : D.Ob a} (β : x ⟶[𝟙 a] y) : D.cartesianFactor β = β :=
  (D.cartesianFactor_uniq β β rfl).symm

end FactorSplit

/-! ## Transport of vertical morphisms -/

section PullMap

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Fib D] {a a' a'' : A}

/-- Transport of a vertical morphism along `f`. -/
noncomputable irreducible_def pullMap (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.pull f x ⟶ D.pull f y :=
  D.cartesianFactor (D.clift f x ≫ᵈ β)

/-- The defining property of `pullMap`. -/
theorem pullMap_clift (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.pullMap f β ≫ᵈ D.clift f y = D.clift f x ≫ᵈ β := by
  rw [pullMap_def]

/-! The laws of `pullMap` and `cartesianFactor` below are proved before the interchange rule
`clift_vert` is declared: once it is a rule, `pullMap_clift` holds by `rfl` and can no longer be
used to reason about `pullMap`. -/

/-- `pullMap f` preserves identities. -/
theorem pullMap_id_vert (f : a ⟶ a') (x : D.Fiber a') :
    D.pullMap f (𝟙ᵈ x) = 𝟙ᵈ (D.pull f x) :=
  IsCartesian.hom_ext (φ := D.clift f x) (D.clift_cartesian f x) (D.pullMap_clift f (𝟙ᵈ x))

/-- `pullMap f` preserves composition. -/
theorem pullMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a'} (β : x ⟶ y) (γ : y ⟶ z) :
    D.pullMap f (β ≫ᵈ γ) = D.pullMap f β ≫ᵈ D.pullMap f γ := by
  refine IsCartesian.hom_ext (φ := D.clift f z) (D.clift_cartesian f z) ?_
  calc D.pullMap f (β ≫ᵈ γ) ≫ᵈ D.clift f z = D.clift f x ≫ᵈ (β ≫ᵈ γ) := D.pullMap_clift f _
    _ = (D.pullMap f β ≫ᵈ D.clift f y) ≫ᵈ γ :=
      congrArg (· ≫ᵈ γ) (D.pullMap_clift f β).symm
    _ = D.pullMap f β ≫ᵈ (D.pullMap f γ ≫ᵈ D.clift f z) :=
      congrArg (D.pullMap f β ≫ᵈ ·) (D.pullMap_clift f γ).symm

end PullMap

section PullMapSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitFib D] {a a' a'' : A}

/-- Transport along the identity is the identity. -/
theorem pullMap_id {x y : D.Fiber a} (β : x ⟶ y) : D.pullMap (𝟙 a) β = β :=
  D.pullMap_clift (𝟙 a) β

/-- Transport along a composite is the composite of transports. -/
theorem pullMap_comp (f : a ⟶ a') (g : a' ⟶ a'') {x y : D.Fiber a''} (β : x ⟶ y) :
    D.pullMap (f ≫ g) β = D.pullMap f (D.pullMap g β) := by
  refine IsCartesian.hom_ext (φ := D.clift (f ≫ g) y) (D.clift_cartesian (f ≫ g) y) ?_
  calc D.pullMap (f ≫ g) β ≫ᵈ D.clift (f ≫ g) y = D.clift (f ≫ g) x ≫ᵈ β :=
        D.pullMap_clift (f ≫ g) β
    _ = D.clift f (D.pull g x) ≫ᵈ (D.pullMap g β ≫ᵈ D.clift g y) :=
      congrArg (D.clift f (D.pull g x) ≫ᵈ ·) (D.pullMap_clift g β).symm
    _ = (D.pullMap f (D.pullMap g β) ≫ᵈ D.clift f (D.pull g y)) ≫ᵈ D.clift g y :=
      congrArg (· ≫ᵈ D.clift g y) (D.pullMap_clift f (D.pullMap g β)).symm

/-- The factorization of a composite: compose with the transported second factorization. -/
theorem cartesianFactor_comp {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.cartesianFactor (φ ≫ᵈ ψ) =
      D.cartesianFactor φ ≫ᵈ D.pullMap f (D.cartesianFactor ψ) := by
  refine (D.cartesianFactor_uniq _ _ ?_).symm
  calc (D.cartesianFactor φ ≫ᵈ D.pullMap f (D.cartesianFactor ψ)) ≫ᵈ D.clift (f ≫ g) z
        = D.cartesianFactor φ ≫ᵈ ((D.pullMap f (D.cartesianFactor ψ) ≫ᵈ
            D.clift f (D.pull g z)) ≫ᵈ D.clift g z) := rfl
    _ = D.cartesianFactor φ ≫ᵈ ((D.clift f y ≫ᵈ D.cartesianFactor ψ) ≫ᵈ D.clift g z) :=
      congrArg (fun t => D.cartesianFactor φ ≫ᵈ (t ≫ᵈ D.clift g z))
        (D.pullMap_clift f (D.cartesianFactor ψ))
    _ = D.cartesianFactor φ ≫ᵈ (D.clift f y ≫ᵈ (D.cartesianFactor ψ ≫ᵈ D.clift g z)) :=
      congrArg (D.cartesianFactor φ ≫ᵈ ·)
        (D.assoc (D.clift f y) (D.cartesianFactor ψ) (D.clift g z))
    _ = φ ≫ᵈ ψ := rfl

end PullMapSplit

section Interchange

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Fib D] {a a' a'' : A}

/-- Interchange of a chosen lift with a vertical morphism, oriented so that the lift comes last. -/
theorem clift_vert (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.clift f x ≫ᵈ β = D.pullMap f β ≫ᵈ D.clift f y :=
  (D.pullMap_clift f β).symm

/-- `clift_vert` under a further composite, as it appears in right-associated composites. -/
theorem clift_vert_assoc (f : a ⟶ a') {g : a' ⟶ a''} {x y : D.Fiber a'} {z : D.Ob a''}
    (β : x ⟶ y) (χ : y ⟶[g] z) :
    D.clift f x ≫ᵈ (β ≫ᵈ χ) = D.pullMap f β ≫ᵈ (D.clift f y ≫ᵈ χ) :=
  congrArg (· ≫ᵈ χ) (D.clift_vert f β)

attribute [rewrite_rule] pullMap_id_vert pullMap_comp_vert pullMap_id pullMap_comp
  cartesianFactor_comp clift_vert clift_vert_assoc

/-- The pullback functor `D.Fiber a' ⥤ D.Fiber a`. -/
noncomputable def pullFunctor (f : a ⟶ a') : D.Fiber a' ⥤ D.Fiber a where
  obj y := D.pull f y
  map β := D.pullMap f β
  map_id y := D.pullMap_id_vert f y
  map_comp β γ := D.pullMap_comp_vert f β γ

@[simp] theorem pullFunctor_obj (f : a ⟶ a') (y : D.Fiber a') :
    (D.pullFunctor f).obj y = D.pull f y := rfl

@[simp] theorem pullFunctor_map (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    (D.pullFunctor f).map β = D.pullMap f β := rfl

end Interchange

/-! ## The total category -/

section Total

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Fib D] {a a' a'' : A}

/-- The chosen cartesian morphisms of the total category. -/
def totalClift (f : a ⟶ a') (y : D.Ob a') : D.tot (D.pull f y) ⟶ D.tot y := ⟨f, D.clift f y⟩

@[simp] theorem totalClift_base (f : a ⟶ a') (y : D.Ob a') : (D.totalClift f y).base = f := rfl

@[simp] theorem totalClift_fiber (f : a ⟶ a') (y : D.Ob a') :
    (D.totalClift f y).fiber = D.clift f y := rfl

theorem π_map_totalClift (f : a ⟶ a') (y : D.Ob a') : D.π.map (D.totalClift f y) = f := rfl

/-- Every morphism of the total category factors as a vertical morphism followed by the chosen
lift. -/
theorem totalMk_eq_comp_totalClift {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.totalMk f φ = D.totalVert (D.cartesianFactor φ) ≫ D.totalClift f y := rfl

/-- Interchange in the total category: a chosen lift followed by a vertical morphism is the
transported vertical morphism followed by the chosen lift. -/
theorem totalClift_comp_totalVert (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.totalClift f x ≫ D.totalVert β = D.totalVert (D.pullMap f β) ≫ D.totalClift f y := rfl

end Total

section TotalSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitFib D] {a a' a'' : A}

theorem totalClift_id (y : D.Ob a) : D.totalClift (𝟙 a) y = 𝟙 (D.tot y) := rfl

theorem totalClift_comp (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a'') :
    D.totalClift (f ≫ g) y = D.totalClift f (D.pull g y) ≫ D.totalClift g y := rfl

end TotalSplit

end Displayed
