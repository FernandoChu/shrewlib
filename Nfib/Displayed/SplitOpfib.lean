import Nfib.Displayed.Basic
import Nfib.Displayed.Cartesian
import Mathlib.Tactic.IrreducibleDef

/-!
# Split opfibrations and fibrations

A `SplitOpfib` structure on a displayed category `D` is a strictly functorial cloven opfibration:
a chosen pushforward `transp f x` for every base morphism `f` and object `x`, a chosen opcartesian
lift `olift f x`, and the splitting axioms. `SplitFib` is the exact dual (chosen cartesian lifts).

The splitting axioms on objects, `transp (𝟙 a) x = x` and
`transp (f ≫ g) x = transp g (transp f x)`, are rewrite rules. They live in a separate structure
`Cleavage`, a field of `SplitOpfib`, so that they are already rules when the axioms on lifts are
declared: `olift (𝟙 a) x = 𝟙ᵈ x` then compares morphisms with definitionally equal codomains, and
is a plain equation.

From a `SplitOpfib` we derive, all as rewrite rules:

* the vertical factorization `factor φ : transp f x ⟶ y` of a displayed morphism through the chosen
  lift, with `olift f x ≫ᵈ factor φ = φ`;
* the fiber transport `transpMap f β : transp f x ⟶ transp f y` and its functoriality in both `β`
  and `f`, which hold on the nose;
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

/-- A cleavage of `D`: strictly functorial chosen pushforwards of objects. -/
structure Cleavage (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pushforward of `x` along `f`. -/
  transp : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Ob a'
  transp_id : ∀ {a : A} (x : D.Ob a), transp (𝟙 a) x = x
  transp_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    transp (f ≫ g) x = transp g (transp f x)

attribute [rewrite_rule] Cleavage.transp_id Cleavage.transp_comp

open scoped Displayed in
/-- A split opfibration structure on a displayed category: strictly functorial chosen opcartesian
lifts. -/
class SplitOpfib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pushforwards. -/
  cleavage : Cleavage D
  /-- The chosen opcartesian lift of `f` at `x`. -/
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → (x ⟶[f] cleavage.transp f x)
  /-- The chosen lifts are opcartesian. -/
  olift_opcartesian : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)
  /-- The lift of the identity is the displayed identity. -/
  olift_id : ∀ {a : A} (x : D.Ob a), olift (𝟙 a) x = 𝟙ᵈ x
  /-- The lift of a composite is the composite of lifts. -/
  olift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    olift (f ≫ g) x = olift f x ≫ᵈ olift g (cleavage.transp f x)

attribute [rewrite_rule] SplitOpfib.olift_id SplitOpfib.olift_comp

/-- A fibration cleavage of `D`: strictly functorial chosen pullbacks of objects. -/
structure FibCleavage (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pullback of `y` along `f`. -/
  pull : {a a' : A} → (f : a ⟶ a') → D.Ob a' → D.Ob a
  pull_id : ∀ {a : A} (y : D.Ob a), pull (𝟙 a) y = y
  pull_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    pull (f ≫ g) y = pull f (pull g y)

attribute [rewrite_rule] FibCleavage.pull_id FibCleavage.pull_comp

open scoped Displayed in
/-- A split fibration structure on a displayed category: strictly functorial chosen cartesian
lifts. The exact dual of `SplitOpfib`. -/
class SplitFib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pullbacks. -/
  cleavage : FibCleavage D
  /-- The chosen cartesian lift of `f` at `y`. -/
  clift : {a a' : A} → (f : a ⟶ a') → (y : D.Ob a') → (cleavage.pull f y ⟶[f] y)
  /-- The chosen lifts are cartesian. -/
  clift_cartesian : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (clift f y)
  /-- The lift of the identity is the displayed identity. -/
  clift_id : ∀ {a : A} (y : D.Ob a), clift (𝟙 a) y = 𝟙ᵈ y
  /-- The lift of a composite is the composite of lifts. -/
  clift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    clift (f ≫ g) y = clift f (cleavage.pull g y) ≫ᵈ clift g y

attribute [rewrite_rule] SplitFib.clift_id SplitFib.clift_comp

open scoped Displayed

section

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D]

/-- The chosen pushforward of `x` along `f`, viewed as an object of the fiber over `a'`. -/
@[reducible] def transp {a a' : A} (f : a ⟶ a') (x : D.Ob a) : D.Fiber a' :=
  (SplitOpfib.cleavage (D := D)).transp f x

/-- The chosen opcartesian lift of `f` at `x`. -/
def olift {a a' : A} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] (D.transp f x) := SplitOpfib.olift f x

theorem olift_opcartesian {a a' : A} (f : a ⟶ a') (x : D.Ob a) :
    IsOpcartesian (D.olift f x) := SplitOpfib.olift_opcartesian f x

@[rewrite_rule]
theorem transp_id {a : A} (x : D.Ob a) : D.transp (𝟙 a) x = x :=
  (SplitOpfib.cleavage (D := D)).transp_id x

@[rewrite_rule]
theorem transp_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.transp (f ≫ g) x = D.transp g (D.transp f x) :=
  (SplitOpfib.cleavage (D := D)).transp_comp f g x

@[rewrite_rule]
theorem olift_id {a : A} (x : D.Ob a) : D.olift (𝟙 a) x = 𝟙ᵈ x := SplitOpfib.olift_id x

@[rewrite_rule]
theorem olift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.olift (f ≫ g) x = D.olift f x ≫ᵈ D.olift g (D.transp f x) := SplitOpfib.olift_comp f g x

end

section Factor

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

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

/-- The factorization of a vertical morphism is the morphism itself. -/
@[rewrite_rule]
theorem factor_vert {x y : D.Ob a} (β : x ⟶[𝟙 a] y) : D.factor β = β :=
  (D.factor_uniq β β rfl).symm

/-- The hom-set bijection defining an opfibration: `D.Hom f x y ≃ (transp f x ⟶ y)`. -/
noncomputable def homEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.transp f x) ⟶[𝟙 a'] y) where
  toFun φ := D.factor φ
  invFun β := D.olift f x ≫ᵈ β
  left_inv _ := rfl
  right_inv β := (D.factor_uniq _ β rfl).symm

end Factor

section TranspMap

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

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

variable (D : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

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

theorem totalOlift_id (x : D.Ob a) : D.totalOlift (𝟙 a) x = 𝟙 (D.tot x) := rfl

theorem totalOlift_comp (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.totalOlift (f ≫ g) x = D.totalOlift f x ≫ D.totalOlift g (D.transp f x) := rfl

/-- Interchange in the total category: a vertical morphism followed by a chosen lift is the chosen
lift followed by the transported vertical morphism. -/
theorem totalVert_comp_totalOlift (g : a' ⟶ a'') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.totalVert β ≫ D.totalOlift g y = D.totalOlift g x ≫ D.totalVert (D.transpMap g β) := rfl

end TotalOlift

end Displayed

end Nfib
