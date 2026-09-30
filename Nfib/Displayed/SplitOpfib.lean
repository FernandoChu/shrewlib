import Nfib.Displayed.Basic
import Nfib.Displayed.Cartesian
import Mathlib.Tactic.IrreducibleDef

/-!
# Opfibrations, fibrations and their split versions

An `Opfib` structure on a displayed category `D` is a cloven opfibration: a chosen pushforward
`transp f x` for every base morphism `f` and object `x`, and a chosen opcartesian lift
`olift f x : x ⟶[f] transp f x`. A `PreSplitOpfib` extends it with the
splitting axioms on objects, `transp (𝟙 a) x = x` and `transp (f ≫ g) x = transp g (transp f x)`,
which are rewrite rules. A `SplitOpfib` adds the splitting axioms on lifts,
`olift (𝟙 a) x = 𝟙ᵈ x` and `olift (f ≫ g) x = olift f x ≫ᵈ olift g (transp f x)`. These are plain
equations, since the rules on objects make the codomains agree definitionally, and are rules too.
`Fib`, `PreSplitFib` and `SplitFib` are the exact duals (chosen cartesian lifts).

From an `Opfib` (or a (pre-)split one, where noted) we derive, all as rewrite rules:

* the vertical factorization `factor φ : transp f x ⟶ y` of a displayed morphism through the chosen
  lift, with `olift f x ≫ᵈ factor φ = φ`;
* the fiber transport `transpMap f β : transp f x ⟶ transp f y`, its functoriality in `β`, and,
  for a `SplitOpfib`, in `f`, which hold on the nose;
* the interchange `β ≫ᵈ olift f y = olift f x ≫ᵈ transpMap f β`, oriented so that chosen lifts come
  first.

These make the dual opfibration of `B` (`DualOp.lean`) a displayed category whose laws hold by
`rfl`. Since the interchange rule has `transpMap` on its right-hand side, and `transpMap` is defined
by a factorization that the rules rewrite back into `transpMap`, `transpMap` is an
`irreducible_def`: unfolding it would loop.

This is part of milestone **M2** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂

namespace Nfib

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

open scoped Displayed

/-- A (cloven) opfibration structure on a displayed category: a chosen opcartesian lift of every
base morphism at every object over its domain. -/
class Opfib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pushforward of `x` along `f`. -/
  transp : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Ob a'
  /-- The chosen opcartesian lift of `f` at `x`. -/
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → (x ⟶[f] transp f x)
  /-- The chosen lifts are opcartesian. -/
  olift_opcartesian : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)

/-- A pre-split opfibration: an opfibration whose chosen pushforwards are strictly functorial on
objects. These axioms are rewrite rules. -/
class PreSplitOpfib (D : Displayed.{v₁, u₁, v₂, u₂} A) extends Opfib D where
  transp_id : ∀ {a : A} (x : D.Ob a), transp (𝟙 a) x = x
  transp_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    transp (f ≫ g) x = transp g (transp f x)

attribute [rewrite_rule] PreSplitOpfib.transp_id PreSplitOpfib.transp_comp

/-- A split opfibration: a pre-split opfibration whose chosen lifts are strictly functorial.

The pre-split structure is an instance field rather than a parent: the fields of a parent are
local variables while the later fields are elaborated, so the rules `transp_id` and `transp_comp`
would not apply to them. As a field, `transp` is `Opfib.transp` of an instance, the axioms on
objects hold definitionally, and the axioms on lifts are plain equations. -/
class SplitOpfib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The underlying pre-split opfibration. -/
  [toPreSplitOpfib : PreSplitOpfib D]
  /-- The lift of the identity is the displayed identity. -/
  olift_id : ∀ {a : A} (x : D.Ob a), Opfib.olift (𝟙 a) x = 𝟙ᵈ x
  /-- The lift of a composite is the composite of lifts. -/
  olift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    Opfib.olift (f ≫ g) x = Opfib.olift f x ≫ᵈ Opfib.olift g (Opfib.transp f x)

attribute [instance_reducible, instance] SplitOpfib.toPreSplitOpfib

attribute [rewrite_rule] SplitOpfib.olift_id SplitOpfib.olift_comp

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

/-- A split fibration: a pre-split fibration whose chosen lifts are strictly functorial. The exact
dual of `SplitOpfib`. -/
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

section

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D]

/-- The chosen pushforward of `x` along `f`, viewed as an object of the fiber over `a'`. -/
@[reducible] def transp {a a' : A} (f : a ⟶ a') (x : D.Ob a) : D.Fiber a' :=
  Opfib.transp f x

/-- The chosen opcartesian lift of `f` at `x`. -/
def olift {a a' : A} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] (D.transp f x) := Opfib.olift f x

theorem olift_opcartesian {a a' : A} (f : a ⟶ a') (x : D.Ob a) :
    IsOpcartesian (D.olift f x) := Opfib.olift_opcartesian f x

end

section

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [PreSplitOpfib D]

@[rewrite_rule]
theorem transp_id {a : A} (x : D.Ob a) : D.transp (𝟙 a) x = x :=
  PreSplitOpfib.transp_id x

@[rewrite_rule]
theorem transp_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.transp (f ≫ g) x = D.transp g (D.transp f x) :=
  PreSplitOpfib.transp_comp f g x

end

section

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D]

@[rewrite_rule]
theorem olift_id {a : A} (x : D.Ob a) : D.olift (𝟙 a) x = 𝟙ᵈ x := SplitOpfib.olift_id x

@[rewrite_rule]
theorem olift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.olift (f ≫ g) x = D.olift f x ≫ᵈ D.olift g (D.transp f x) := SplitOpfib.olift_comp f g x

end

section Factor

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift `olift f x` by a
vertical morphism `transp f x ⟶ y`. -/
noncomputable def factor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    (D.transp f x) ⟶[𝟙 a'] y :=
  IsOpcartesian.desc (D.olift_opcartesian f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_factor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.olift f x ≫ᵈ D.factor φ = φ :=
  IsOpcartesian.desc_fac (D.olift_opcartesian f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_factor_assoc {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.olift f x ≫ᵈ (D.factor φ ≫ᵈ ψ) = φ ≫ᵈ ψ :=
  congrArg (· ≫ᵈ ψ) (D.olift_factor φ)

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with `factor φ`. -/
theorem factor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : (D.transp f x) ⟶[𝟙 a'] y) (h : D.olift f x ≫ᵈ β = φ) : β = D.factor φ :=
  IsOpcartesian.desc_uniq (D.olift_opcartesian f x) β h

@[rewrite_rule]
theorem factor_olift (f : a ⟶ a') (x : D.Ob a) : D.factor (D.olift f x) = 𝟙ᵈ (D.transp f x) :=
  (D.factor_uniq (D.olift f x) (𝟙ᵈ _) rfl).symm

/-- The hom-set bijection defining an opfibration: `D.Hom f x y ≃ (transp f x ⟶ y)`. -/
noncomputable def homEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.transp f x) ⟶[𝟙 a'] y) where
  toFun φ := D.factor φ
  invFun β := D.olift f x ≫ᵈ β
  left_inv _ := rfl
  right_inv β := (D.factor_uniq _ β rfl).symm

end Factor

section FactorSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a : A}

/-- The factorization of a vertical morphism is the morphism itself. -/
@[rewrite_rule]
theorem factor_vert {x y : D.Ob a} (β : x ⟶[𝟙 a] y) : D.factor β = β :=
  (D.factor_uniq β β rfl).symm

end FactorSplit

section TranspMap

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Transport of a vertical morphism along `f`. -/
noncomputable irreducible_def transpMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.transp f x ⟶ D.transp f y :=
  D.factor (β ≫ᵈ D.olift f y)

/-- The defining property of `transpMap`. -/
theorem olift_transpMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.olift f x ≫ᵈ D.transpMap f β = β ≫ᵈ D.olift f y := by
  rw [transpMap_def]

/-! The laws of `transpMap` and `factor` below are proved before the interchange rule
`vert_olift` is declared: once it is a rule, `olift_transpMap` holds by `rfl` and can no longer be
used to reason about `transpMap`. -/

/-- `transpMap f` preserves identities. -/
theorem transpMap_id_vert (f : a ⟶ a') (x : D.Fiber a) :
    D.transpMap f (𝟙ᵈ x) = 𝟙ᵈ (D.transp f x) :=
  IsOpcartesian.hom_ext (φ := D.olift f x) (D.olift_opcartesian f x) (D.olift_transpMap f (𝟙ᵈ x))

/-- `transpMap f` preserves composition. -/
theorem transpMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.transpMap f (β ≫ᵈ γ) = D.transpMap f β ≫ᵈ D.transpMap f γ := by
  refine IsOpcartesian.hom_ext (φ := D.olift f x) (D.olift_opcartesian f x) ?_
  calc D.olift f x ≫ᵈ D.transpMap f (β ≫ᵈ γ) = β ≫ᵈ (γ ≫ᵈ D.olift f z) := D.olift_transpMap f _
    _ = β ≫ᵈ (D.olift f y ≫ᵈ D.transpMap f γ) :=
      congrArg (β ≫ᵈ ·) (D.olift_transpMap f γ).symm
    _ = D.olift f x ≫ᵈ (D.transpMap f β ≫ᵈ D.transpMap f γ) :=
      congrArg (· ≫ᵈ D.transpMap f γ) (D.olift_transpMap f β).symm

end TranspMap

section TranspMapSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

/-- Transport along the identity is the identity. -/
theorem transpMap_id {x y : D.Fiber a} (β : x ⟶ y) : D.transpMap (𝟙 a) β = β :=
  D.olift_transpMap (𝟙 a) β

/-- Transport along a composite is the composite of transports. -/
theorem transpMap_comp (f : a ⟶ a') (g : a' ⟶ a'') {x y : D.Fiber a} (β : x ⟶ y) :
    D.transpMap (f ≫ g) β = D.transpMap g (D.transpMap f β) := by
  refine IsOpcartesian.hom_ext (φ := D.olift (f ≫ g) x) (D.olift_opcartesian (f ≫ g) x) ?_
  calc D.olift (f ≫ g) x ≫ᵈ D.transpMap (f ≫ g) β = β ≫ᵈ D.olift (f ≫ g) y :=
        D.olift_transpMap (f ≫ g) β
    _ = D.olift f x ≫ᵈ (D.transpMap f β ≫ᵈ D.olift g (D.transp f y)) :=
      congrArg (· ≫ᵈ D.olift g (D.transp f y)) (D.olift_transpMap f β).symm
    _ = D.olift f x ≫ᵈ (D.olift g (D.transp f x) ≫ᵈ D.transpMap g (D.transpMap f β)) :=
      congrArg (D.olift f x ≫ᵈ ·) (D.olift_transpMap g (D.transpMap f β)).symm

/-- `factor` of a composite: transport the first factorization and compose. -/
theorem factor_comp {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.factor (φ ≫ᵈ ψ) = D.transpMap g (D.factor φ) ≫ᵈ D.factor ψ := by
  refine (D.factor_uniq _ _ ?_).symm
  calc D.olift (f ≫ g) x ≫ᵈ (D.transpMap g (D.factor φ) ≫ᵈ D.factor ψ)
        = D.olift f x ≫ᵈ ((D.olift g (D.transp f x) ≫ᵈ D.transpMap g (D.factor φ)) ≫ᵈ
            D.factor ψ) := rfl
    _ = D.olift f x ≫ᵈ ((D.factor φ ≫ᵈ D.olift g y) ≫ᵈ D.factor ψ) :=
      congrArg (fun t => D.olift f x ≫ᵈ (t ≫ᵈ D.factor ψ)) (D.olift_transpMap g (D.factor φ))
    _ = D.olift f x ≫ᵈ (D.factor φ ≫ᵈ (D.olift g y ≫ᵈ D.factor ψ)) :=
      congrArg (D.olift f x ≫ᵈ ·) (D.assoc (D.factor φ) (D.olift g y) (D.factor ψ))
    _ = φ ≫ᵈ ψ := rfl

end TranspMapSplit

section TranspMap

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Interchange of a vertical morphism with a chosen lift, oriented so that the lift comes first. -/
theorem vert_olift (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    β ≫ᵈ D.olift f y = D.olift f x ≫ᵈ D.transpMap f β :=
  (D.olift_transpMap f β).symm

theorem vert_olift_assoc (f : a ⟶ a') {g : a' ⟶ a''} {x y : D.Fiber a} {z : D.Ob a''}
    (β : x ⟶ y) (φ : D.transp f y ⟶[g] z) :
    β ≫ᵈ (D.olift f y ≫ᵈ φ) = D.olift f x ≫ᵈ (D.transpMap f β ≫ᵈ φ) :=
  congrArg (· ≫ᵈ φ) (D.vert_olift f β)

attribute [rewrite_rule] transpMap_id_vert transpMap_comp_vert transpMap_id transpMap_comp
  factor_comp vert_olift vert_olift_assoc

/-- The fiber transport functor `D.Fiber a ⥤ D.Fiber a'`. -/
noncomputable def transpFunctor (f : a ⟶ a') : D.Fiber a ⥤ D.Fiber a' where
  obj x := D.transp f x
  map β := D.transpMap f β
  map_id x := D.transpMap_id_vert f x
  map_comp β γ := D.transpMap_comp_vert f β γ

@[simp] theorem transpFunctor_obj (f : a ⟶ a') (x : D.Fiber a) :
    (D.transpFunctor f).obj x = D.transp f x := rfl

@[simp] theorem transpFunctor_map (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    (D.transpFunctor f).map β = D.transpMap f β := rfl

end TranspMap

section TotalOlift

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- The chosen opcartesian morphisms of the total category. -/
def totalOlift (f : a ⟶ a') (x : D.Ob a) : D.tot x ⟶ D.tot (D.transp f x) := ⟨f, D.olift f x⟩

@[simp] theorem totalOlift_base (f : a ⟶ a') (x : D.Ob a) : (D.totalOlift f x).base = f := rfl

@[simp] theorem totalOlift_fiber (f : a ⟶ a') (x : D.Ob a) :
    (D.totalOlift f x).fiber = D.olift f x := rfl

theorem π_map_totalOlift (f : a ⟶ a') (x : D.Ob a) : D.π.map (D.totalOlift f x) = f := rfl

/-- Every morphism of the total category factors as the chosen lift followed by a vertical
morphism. -/
theorem factorTotal {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.totalMk f φ = D.totalOlift f x ≫ D.totalVert (D.factor φ) := rfl

/-- Interchange in the total category: a vertical morphism followed by a chosen lift is the chosen
lift followed by the transported vertical morphism. -/
theorem totalVert_comp_totalOlift (g : a' ⟶ a'') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.totalVert β ≫ D.totalOlift g y = D.totalOlift g x ≫ D.totalVert (D.transpMap g β) := rfl

end TotalOlift

section TotalOliftSplit

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

theorem totalOlift_id (x : D.Ob a) : D.totalOlift (𝟙 a) x = 𝟙 (D.tot x) := rfl

theorem totalOlift_comp (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.totalOlift (f ≫ g) x = D.totalOlift f x ≫ D.totalOlift g (D.transp f x) := rfl

end TotalOliftSplit

end Displayed

end Nfib
