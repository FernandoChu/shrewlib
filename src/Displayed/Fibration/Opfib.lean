import Displayed.Basic
import Displayed.Cartesian
import Displayed.Total
import Mathlib.Tactic.IrreducibleDef

/-!
# Opfibrations

An `Opfib` structure on a displayed category `D` is a cloven opfibration: a chosen pushforward
`push f x` for every base morphism `f : a ⟶ a'` and object `x` over `a`, and a chosen opcartesian
lift `olift f x : x ⟶[f] push f x`. A `PreSplitOpfib` adds the splitting axioms on objects,
`push (𝟙 a) x = x` and `push (f ≫ g) x = push g (push f x)`, which are rewrite rules. A
`SplitOpfib` adds the splitting axioms on lifts, `olift (𝟙 a) x = 𝟙ᵈ x` and
`olift (f ≫ g) x = olift f x ≫ᵈ olift g (push f x)`. These are plain equations, since the rules on
objects make the codomains agree definitionally, and are rules too.

From an `Opfib` (or a (pre-)split one, where noted) we derive, all as rewrite rules:

* the vertical factorization `opcartesianFactor φ : push f x ⟶ y` of `φ : x ⟶[f] y` through the
  chosen lift, with `olift f x ≫ᵈ opcartesianFactor φ = φ`;
* the fiber transport `pushMap f β : push f x ⟶ push f y`, its functoriality in `β`, and, for a
  `SplitOpfib`, in `f`, which hold on the nose;
* the interchange `β ≫ᵈ olift f y = olift f x ≫ᵈ pushMap f β`, oriented so that chosen lifts come
  first.

These make the dual opfibration of `B` (`DualOp.lean`) a displayed category whose laws hold by
`rfl`. Since the interchange rule has `pushMap` on its right-hand side, and `pushMap` is defined
by a factorization that the rules rewrite back into `pushMap`, `pushMap` is an `irreducible_def`:
unfolding it would loop.

`Fib.lean` is the exact dual, with chosen cartesian lifts `clift f y : pull f y ⟶[f] y`. Its
sections mirror the sections of this file.

This is part of milestone **M2** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

open scoped Displayed

/-! ## The classes -/

/-- A (cloven) opfibration structure on a displayed category: a chosen opcartesian lift of every
base morphism at every object over its domain. -/
class Opfib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pushforward of `x` along `f`. -/
  push : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Ob a'
  /-- The chosen opcartesian lift of `f` at `x`. -/
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → (x ⟶[f] push f x)
  /-- The chosen lifts are opcartesian. -/
  olift_opcartesian : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)

/-- A pre-split opfibration: an opfibration whose chosen pushforwards are strictly functorial on
objects. These axioms are rewrite rules. -/
class PreSplitOpfib (D : Displayed.{v₁, u₁, v₂, u₂} A) extends Opfib D where
  push_id : ∀ {a : A} (x : D.Ob a), push (𝟙 a) x = x
  push_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    push (f ≫ g) x = push g (push f x)

attribute [rewrite_rule] PreSplitOpfib.push_id PreSplitOpfib.push_comp

/-- A split opfibration: a pre-split opfibration whose chosen lifts are strictly functorial.

The pre-split structure is an instance field rather than a parent: the fields of a parent are
local variables while the later fields are elaborated, so the rules `push_id` and `push_comp`
would not apply to them. As a field, `push` is `Opfib.push` of an instance, the axioms on objects
hold definitionally, and the axioms on lifts are plain equations. -/
class SplitOpfib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The underlying pre-split opfibration. -/
  [toPreSplitOpfib : PreSplitOpfib D]
  /-- The lift of the identity is the displayed identity. -/
  olift_id : ∀ {a : A} (x : D.Ob a), Opfib.olift (𝟙 a) x = 𝟙ᵈ x
  /-- The lift of a composite is the composite of lifts. -/
  olift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    Opfib.olift (f ≫ g) x = Opfib.olift f x ≫ᵈ Opfib.olift g (Opfib.push f x)

attribute [instance_reducible, instance] SplitOpfib.toPreSplitOpfib

attribute [rewrite_rule] SplitOpfib.olift_id SplitOpfib.olift_comp

/-! ## Chosen pushforwards and lifts -/

section Lift

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D]

/-- The chosen pushforward of `x` along `f`, viewed as an object of the fiber over `a'`. -/
@[reducible] def push {a a' : A} (f : a ⟶ a') (x : D.Ob a) : D.Fiber a' :=
  Opfib.push f x

/-- The chosen opcartesian lift of `f` at `x`. -/
def olift {a a' : A} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] (D.push f x) := Opfib.olift f x

theorem olift_opcartesian {a a' : A} (f : a ⟶ a') (x : D.Ob a) :
    IsOpcartesian (D.olift f x) := Opfib.olift_opcartesian f x

end Lift

section LiftPreSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [PreSplitOpfib D]

@[rewrite_rule]
theorem push_id {a : A} (x : D.Ob a) : D.push (𝟙 a) x = x :=
  PreSplitOpfib.push_id x

@[rewrite_rule]
theorem push_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.push (f ≫ g) x = D.push g (D.push f x) :=
  PreSplitOpfib.push_comp f g x

end LiftPreSplit

section LiftSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D]

@[rewrite_rule]
theorem olift_id {a : A} (x : D.Ob a) : D.olift (𝟙 a) x = 𝟙ᵈ x := SplitOpfib.olift_id x

@[rewrite_rule]
theorem olift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.olift (f ≫ g) x = D.olift f x ≫ᵈ D.olift g (D.push f x) := SplitOpfib.olift_comp f g x

end LiftSplit

/-! ## Opcartesian factorization -/

section Factor

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift `olift f x` by a
vertical morphism `push f x ⟶ y`. -/
noncomputable def opcartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    (D.push f x) ⟶[𝟙 a'] y :=
  IsOpcartesian.desc (D.olift_opcartesian f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_comp_opcartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.olift f x ≫ᵈ D.opcartesianFactor φ = φ :=
  IsOpcartesian.desc_fac (D.olift_opcartesian f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_comp_opcartesianFactor_assoc {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.olift f x ≫ᵈ (D.opcartesianFactor φ ≫ᵈ ψ) = φ ≫ᵈ ψ :=
  congrArg (· ≫ᵈ ψ) (D.olift_comp_opcartesianFactor φ)

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with
`opcartesianFactor φ`. -/
theorem opcartesianFactor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : (D.push f x) ⟶[𝟙 a'] y) (h : D.olift f x ≫ᵈ β = φ) : β = D.opcartesianFactor φ :=
  IsOpcartesian.desc_uniq (D.olift_opcartesian f x) β h

@[rewrite_rule]
theorem opcartesianFactor_olift (f : a ⟶ a') (x : D.Ob a) :
    D.opcartesianFactor (D.olift f x) = 𝟙ᵈ (D.push f x) :=
  (D.opcartesianFactor_uniq (D.olift f x) (𝟙ᵈ _) rfl).symm

/-- The hom-set bijection defining an opfibration: `(x ⟶[f] y) ≃ (push f x ⟶ y)`. -/
noncomputable def opcartesianHomEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.push f x) ⟶[𝟙 a'] y) where
  toFun φ := D.opcartesianFactor φ
  invFun β := D.olift f x ≫ᵈ β
  left_inv _ := rfl
  right_inv β := (D.opcartesianFactor_uniq _ β rfl).symm

end Factor

section FactorSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a : A}

/-- The factorization of a vertical morphism is the morphism itself. -/
@[rewrite_rule]
theorem opcartesianFactor_vert {x y : D.Ob a} (β : x ⟶[𝟙 a] y) : D.opcartesianFactor β = β :=
  (D.opcartesianFactor_uniq β β rfl).symm

end FactorSplit

/-! ## Transport of vertical morphisms -/

section PushMap

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Transport of a vertical morphism along `f`. -/
noncomputable irreducible_def pushMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.push f x ⟶ D.push f y :=
  D.opcartesianFactor (β ≫ᵈ D.olift f y)

/-- The defining property of `pushMap`. -/
theorem olift_pushMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.olift f x ≫ᵈ D.pushMap f β = β ≫ᵈ D.olift f y := by
  rw [pushMap_def]

/-! The laws of `pushMap` and `opcartesianFactor` below are proved before the interchange rule
`vert_olift` is declared: once it is a rule, `olift_pushMap` holds by `rfl` and can no longer be
used to reason about `pushMap`. -/

/-- `pushMap f` preserves identities. -/
theorem pushMap_id_vert (f : a ⟶ a') (x : D.Fiber a) :
    D.pushMap f (𝟙ᵈ x) = 𝟙ᵈ (D.push f x) :=
  IsOpcartesian.hom_ext (φ := D.olift f x) (D.olift_opcartesian f x) (D.olift_pushMap f (𝟙ᵈ x))

/-- `pushMap f` preserves composition. -/
theorem pushMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.pushMap f (β ≫ᵈ γ) = D.pushMap f β ≫ᵈ D.pushMap f γ := by
  refine IsOpcartesian.hom_ext (φ := D.olift f x) (D.olift_opcartesian f x) ?_
  calc D.olift f x ≫ᵈ D.pushMap f (β ≫ᵈ γ) = β ≫ᵈ (γ ≫ᵈ D.olift f z) := D.olift_pushMap f _
    _ = β ≫ᵈ (D.olift f y ≫ᵈ D.pushMap f γ) :=
      congrArg (β ≫ᵈ ·) (D.olift_pushMap f γ).symm
    _ = D.olift f x ≫ᵈ (D.pushMap f β ≫ᵈ D.pushMap f γ) :=
      congrArg (· ≫ᵈ D.pushMap f γ) (D.olift_pushMap f β).symm

end PushMap

section PushMapSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

/-- Transport along the identity is the identity. -/
theorem pushMap_id {x y : D.Fiber a} (β : x ⟶ y) : D.pushMap (𝟙 a) β = β :=
  D.olift_pushMap (𝟙 a) β

/-- Transport along a composite is the composite of transports. -/
theorem pushMap_comp (f : a ⟶ a') (g : a' ⟶ a'') {x y : D.Fiber a} (β : x ⟶ y) :
    D.pushMap (f ≫ g) β = D.pushMap g (D.pushMap f β) := by
  refine IsOpcartesian.hom_ext (φ := D.olift (f ≫ g) x) (D.olift_opcartesian (f ≫ g) x) ?_
  calc D.olift (f ≫ g) x ≫ᵈ D.pushMap (f ≫ g) β = β ≫ᵈ D.olift (f ≫ g) y :=
        D.olift_pushMap (f ≫ g) β
    _ = D.olift f x ≫ᵈ (D.pushMap f β ≫ᵈ D.olift g (D.push f y)) :=
      congrArg (· ≫ᵈ D.olift g (D.push f y)) (D.olift_pushMap f β).symm
    _ = D.olift f x ≫ᵈ (D.olift g (D.push f x) ≫ᵈ D.pushMap g (D.pushMap f β)) :=
      congrArg (D.olift f x ≫ᵈ ·) (D.olift_pushMap g (D.pushMap f β)).symm

/-- The factorization of a composite: transport the first factorization and compose. -/
theorem opcartesianFactor_comp {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.opcartesianFactor (φ ≫ᵈ ψ) =
      D.pushMap g (D.opcartesianFactor φ) ≫ᵈ D.opcartesianFactor ψ := by
  refine (D.opcartesianFactor_uniq _ _ ?_).symm
  calc D.olift (f ≫ g) x ≫ᵈ (D.pushMap g (D.opcartesianFactor φ) ≫ᵈ D.opcartesianFactor ψ)
        = D.olift f x ≫ᵈ ((D.olift g (D.push f x) ≫ᵈ D.pushMap g (D.opcartesianFactor φ)) ≫ᵈ
            D.opcartesianFactor ψ) := rfl
    _ = D.olift f x ≫ᵈ ((D.opcartesianFactor φ ≫ᵈ D.olift g y) ≫ᵈ D.opcartesianFactor ψ) :=
      congrArg (fun t => D.olift f x ≫ᵈ (t ≫ᵈ D.opcartesianFactor ψ))
        (D.olift_pushMap g (D.opcartesianFactor φ))
    _ = D.olift f x ≫ᵈ (D.opcartesianFactor φ ≫ᵈ (D.olift g y ≫ᵈ D.opcartesianFactor ψ)) :=
      congrArg (D.olift f x ≫ᵈ ·)
        (D.assoc (D.opcartesianFactor φ) (D.olift g y) (D.opcartesianFactor ψ))
    _ = φ ≫ᵈ ψ := rfl

end PushMapSplit

section Interchange

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Interchange of a vertical morphism with a chosen lift, oriented so that the lift comes first. -/
theorem vert_olift (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    β ≫ᵈ D.olift f y = D.olift f x ≫ᵈ D.pushMap f β :=
  (D.olift_pushMap f β).symm

/-- `vert_olift` under a further composite, as it appears in right-associated composites. -/
theorem vert_olift_assoc (f : a ⟶ a') {g : a' ⟶ a''} {x y : D.Fiber a} {z : D.Ob a''}
    (β : x ⟶ y) (φ : D.push f y ⟶[g] z) :
    β ≫ᵈ (D.olift f y ≫ᵈ φ) = D.olift f x ≫ᵈ (D.pushMap f β ≫ᵈ φ) :=
  congrArg (· ≫ᵈ φ) (D.vert_olift f β)

attribute [rewrite_rule] pushMap_id_vert pushMap_comp_vert pushMap_id pushMap_comp
  opcartesianFactor_comp vert_olift vert_olift_assoc

/-- The pushforward functor `D.Fiber a ⥤ D.Fiber a'`. -/
noncomputable def pushFunctor (f : a ⟶ a') : D.Fiber a ⥤ D.Fiber a' where
  obj x := D.push f x
  map β := D.pushMap f β
  map_id x := D.pushMap_id_vert f x
  map_comp β γ := D.pushMap_comp_vert f β γ

@[simp] theorem pushFunctor_obj (f : a ⟶ a') (x : D.Fiber a) :
    (D.pushFunctor f).obj x = D.push f x := rfl

@[simp] theorem pushFunctor_map (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    (D.pushFunctor f).map β = D.pushMap f β := rfl

end Interchange

/-! ## The total category -/

section Total

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- The chosen opcartesian morphisms of the total category. -/
def totalOlift (f : a ⟶ a') (x : D.Ob a) : D.tot x ⟶ D.tot (D.push f x) := ⟨f, D.olift f x⟩

@[simp] theorem totalOlift_base (f : a ⟶ a') (x : D.Ob a) : (D.totalOlift f x).base = f := rfl

@[simp] theorem totalOlift_fiber (f : a ⟶ a') (x : D.Ob a) :
    (D.totalOlift f x).fiber = D.olift f x := rfl

theorem π_map_totalOlift (f : a ⟶ a') (x : D.Ob a) : D.π.map (D.totalOlift f x) = f := rfl

/-- Every morphism of the total category factors as the chosen lift followed by a vertical
morphism. -/
theorem totalMk_eq_totalOlift_comp {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.totalMk f φ = D.totalOlift f x ≫ D.totalVert (D.opcartesianFactor φ) := rfl

/-- Interchange in the total category: a vertical morphism followed by a chosen lift is the chosen
lift followed by the transported vertical morphism. -/
theorem totalVert_comp_totalOlift (g : a' ⟶ a'') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.totalVert β ≫ D.totalOlift g y = D.totalOlift g x ≫ D.totalVert (D.pushMap g β) := rfl

end Total

section TotalSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

theorem totalOlift_id (x : D.Ob a) : D.totalOlift (𝟙 a) x = 𝟙 (D.tot x) := rfl

theorem totalOlift_comp (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.totalOlift (f ≫ g) x = D.totalOlift f x ≫ D.totalOlift g (D.push f x) := rfl

end TotalSplit

end Displayed
