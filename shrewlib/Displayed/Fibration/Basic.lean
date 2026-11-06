import Displayed.Displayed.Basic
import Displayed.Displayed.Total
import Mathlib.Tactic.IrreducibleDef

/-!
# Fibrations

The exact dual of `Opfibration/Basic.lean`, whose sections this file mirrors. It starts with
cartesian morphisms (`IsCartesian`, whose factorizations are data), and displayed functors that
preserve them (`DispFunctor.PreservesCartesian`), such as vertical equivalences
(`VertEquivalence.isCartesianMap`).

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

Finally, a cleavage transfers along an equivalence over `A` (`VertEquivalence.fib`).

As for `pushMap`, `pullMap` is an `irreducible_def`, since the rules rewrite its definition back
into it, and it is unfolded by `pullMap_eq_lift`. Composites are normalized to be
right-associated, so the `_assoc` forms of the rules are not literally dual to those of
`Opfibration/Basic.lean`: here the rules must also see `clift f y` followed by further morphisms,
as in `cartesianFactor φ ≫ᵈ (clift f y ≫ᵈ χ)` and `clift f x ≫ᵈ (β ≫ᵈ χ)`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

open scoped Displayed

/-! ## Cartesian morphisms -/

section Cartesian

variable {D : Displayed.{v₁, u₁, v₂, u₂} A}

/-- `φ : x ⟶[f] y` is *cartesian*: every displayed map into `y` over `g ≫ f` factors uniquely
through `φ` by a displayed map over `g`. (This is the *strong* cartesian property.) The
factorization is data, so that it computes; it is unique, so that this structure is a
subsingleton. -/
structure IsCartesian {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) where
  /-- The factorization of `χ` through `φ`. -/
  lift : ∀ {a₀ : A} (g : a₀ ⟶ a) {z : D.Ob a₀}, (z ⟶[g ≫ f] y) → (z ⟶[g] x)
  lift_fac : ∀ {a₀ : A} (g : a₀ ⟶ a) {z : D.Ob a₀} (χ : z ⟶[g ≫ f] y), lift g χ ≫ᵈ φ = χ
  /-- Any factorization of `χ` through `φ` agrees with `lift`. -/
  lift_uniq : ∀ {a₀ : A} {g : a₀ ⟶ a} {z : D.Ob a₀} {χ : z ⟶[g ≫ f] y} (ψ : z ⟶[g] x),
    ψ ≫ᵈ φ = χ → ψ = lift g χ

attribute [simp] IsCartesian.lift_fac

namespace IsCartesian

variable {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}

instance : Subsingleton (IsCartesian φ) where
  allEq H H' := by
    obtain ⟨l, fac, _⟩ := H
    obtain ⟨l', _, uniq'⟩ := H'
    obtain rfl : @l = @l' := by
      funext a₀ g z χ
      exact uniq' _ (fac g χ)
    rfl

/-- Two maps into `x` that agree after postcomposition with a cartesian `φ` are equal. -/
theorem hom_ext (H : IsCartesian φ) {a₀ : A} {g : a₀ ⟶ a} {z : D.Ob a₀}
    {ψ ψ' : z ⟶[g] x} (h : ψ ≫ᵈ φ = ψ' ≫ᵈ φ) : ψ = ψ' :=
  (H.lift_uniq ψ rfl).trans (H.lift_uniq ψ' h.symm).symm

/-- Precomposing a cartesian morphism with a vertical isomorphism gives a cartesian morphism. -/
def isoComp {x' : D.Ob a} (H : IsCartesian φ) (ι : x' ⟶[𝟙 a] x) (ι' : x ⟶[𝟙 a] x')
    (h : ι' ≫ᵈ ι = 𝟙ᵈ x) (h' : ι ≫ᵈ ι' = 𝟙ᵈ x') : IsCartesian (ι ≫ᵈ φ) where
  lift g _ χ := (H.lift g χ ≫ᵈ ι' :)
  lift_fac g _ χ := ((congrArg (fun t => H.lift g χ ≫ᵈ (t ≫ᵈ φ)) h).trans (H.lift_fac g χ) :)
  lift_uniq ψ hψ := ((congrArg (ψ ≫ᵈ ·) h').symm.trans
      (congrArg (· ≫ᵈ ι') (H.lift_uniq (ψ ≫ᵈ ι :) hψ)) :)

/-- Postcomposing a cartesian morphism with a vertical isomorphism gives a cartesian morphism. -/
def compIso {y' : D.Ob a'} (H : IsCartesian φ) (ι : y ⟶[𝟙 a'] y') (ι' : y' ⟶[𝟙 a'] y)
    (h : ι' ≫ᵈ ι = 𝟙ᵈ y') (h' : ι ≫ᵈ ι' = 𝟙ᵈ y) : IsCartesian (φ ≫ᵈ ι) where
  lift g _ χ := H.lift g (χ ≫ᵈ ι' :)
  lift_fac g _ χ :=
    ((congrArg (· ≫ᵈ ι) (H.lift_fac g (χ ≫ᵈ ι' :))).trans (congrArg (χ ≫ᵈ ·) h) :)
  lift_uniq ψ hψ := H.lift_uniq ψ
    ((congrArg (fun t => ψ ≫ᵈ (φ ≫ᵈ t)) h').symm.trans (congrArg (· ≫ᵈ ι') hψ) :)

end IsCartesian

/-- A displayed functor *preserves cartesian morphisms* if it sends cartesian morphisms to
cartesian morphisms; since `IsCartesian` is data, this is a function on the factorizations. This is
what is usually called a cartesian, or fibred, functor. `CartesianFunctor` is the strict notion,
for cleavages: it preserves the chosen lifts on the nose. -/
abbrev DispFunctor.PreservesCartesian {B : Type u₄} [Category.{v₄} B] {u : A ⥤ B}
    {E : Displayed.{v₄, u₄, v₅, u₅} B} (F : DispFunctor u D E) : Type _ :=
  ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y},
    IsCartesian φ → IsCartesian (F.map φ)

namespace VertEquivalence

variable {E : Displayed.{v₁, u₁, v₃, u₃} A} (e : VertEquivalence D E)

/-- **A vertical equivalence preserves cartesian morphisms.** The factorization of `χ` is the
counit, followed by the image of the factorization of the preimage of `χ`. -/
def isCartesianMap : e.functor.PreservesCartesian := fun {_ _ _ _ _ φ} H => {
  lift {_} g z χ :=
    (e.counitIso.inv.app z ≫ᵈ
      e.functor.map (H.lift g (e.preimage (e.counitIso.hom.app z ≫ᵈ χ :))) :)
  lift_fac {_} g z χ :=
    (((congrArg (fun t => e.counitIso.inv.app z ≫ᵈ e.functor.map t)
      (H.lift_fac g (e.preimage (e.counitIso.hom.app z ≫ᵈ χ :)))).trans
        (congrArg (e.counitIso.inv.app z ≫ᵈ ·)
          (e.map_preimage (e.counitIso.hom.app z ≫ᵈ χ :)))).trans
        (VertNatIso.inv_hom_id_app_assoc e.counitIso z χ) :)
  lift_uniq {_ g z χ} ψ hψ := by
    let ε := e.counitIso
    have h₁ : e.preimage (ε.hom.app z ≫ᵈ ψ :) ≫ᵈ φ = e.preimage (ε.hom.app z ≫ᵈ χ :) :=
      e.map_injective
        (((congrArg (· ≫ᵈ e.functor.map φ) (e.map_preimage (ε.hom.app z ≫ᵈ ψ :))).trans
          ((congrArg (ε.hom.app z ≫ᵈ ·) hψ).trans (e.map_preimage _).symm)) :)
    have h₂ : e.preimage (ε.hom.app z ≫ᵈ ψ :) = H.lift g (e.preimage (ε.hom.app z ≫ᵈ χ :)) :=
      H.lift_uniq _ h₁
    exact ((VertNatIso.inv_hom_id_app_assoc ε z ψ).symm.trans
      (congrArg (ε.inv.app z ≫ᵈ ·) ((e.map_preimage _).symm.trans (congrArg e.functor.map h₂))) :) }

end VertEquivalence

end Cartesian

/-! ## The classes -/

/-- A (cloven) fibration structure on a displayed category: a chosen cartesian lift of every base
morphism at every object over its codomain. -/
class Fib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The chosen pullback of `y` along `f`. -/
  pull : {a a' : A} → (f : a ⟶ a') → D.Ob a' → D.Ob a
  /-- The chosen cartesian lift of `f` at `y`. -/
  clift : {a a' : A} → (f : a ⟶ a') → (y : D.Ob a') → (pull f y ⟶[f] y)
  /-- The chosen lifts are cartesian. -/
  isCartesianClift : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (clift f y)

/-- A pre-split fibration: a fibration whose chosen pullbacks are strictly functorial on objects.
These axioms are rewrite rules. Its axioms default to `by intros; rfl`, as they hold definitionally
in most instances. -/
class PreSplitFib (D : Displayed.{v₁, u₁, v₂, u₂} A) extends Fib D where
  pull_id : ∀ {a : A} (y : D.Ob a), pull (𝟙 a) y = y := by intros; rfl
  pull_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    pull (f ≫ g) y = pull f (pull g y) := by intros; rfl

attribute [rewrite_rule] PreSplitFib.pull_id PreSplitFib.pull_comp

/-- A split fibration: a pre-split fibration whose chosen lifts are strictly functorial. As for
`SplitOpfib`, the pre-split structure is an instance field rather than a parent, so that the rules
`pull_id` and `pull_comp` apply to the axioms on lifts. Its axioms default to `by intros; rfl`, as
they hold definitionally in most instances. -/
class SplitFib (D : Displayed.{v₁, u₁, v₂, u₂} A) where
  /-- The underlying pre-split fibration. -/
  [toPreSplitFib : PreSplitFib D]
  /-- The lift of the identity is the displayed identity. -/
  clift_id : ∀ {a : A} (y : D.Ob a), Fib.clift (𝟙 a) y = 𝟙ᵈ y := by intros; rfl
  /-- The lift of a composite is the composite of lifts. -/
  clift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a''),
    Fib.clift (f ≫ g) y = Fib.clift f (Fib.pull g y) ≫ᵈ Fib.clift g y := by intros; rfl

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

/-- The chosen lift is cartesian. -/
def isCartesianClift {a a' : A} (f : a ⟶ a') (y : D.Ob a') :
    IsCartesian (D.clift f y) := Fib.isCartesianClift f y

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
def cartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    x ⟶[𝟙 a] (D.pull f y) :=
  IsCartesian.lift (D.isCartesianClift f y) (𝟙 a) φ

@[rewrite_rule]
theorem cartesianFactor_comp_clift {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.cartesianFactor φ ≫ᵈ D.clift f y = φ :=
  IsCartesian.lift_fac (D.isCartesianClift f y) (𝟙 a) φ

@[rewrite_rule]
theorem cartesianFactor_comp_clift_assoc {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (χ : y ⟶[g] z) :
    D.cartesianFactor φ ≫ᵈ (D.clift f y ≫ᵈ χ) = φ ≫ᵈ χ :=
  congrArg (· ≫ᵈ χ) (D.cartesianFactor_comp_clift φ)

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with `cartesianFactor φ`. -/
theorem cartesianFactor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : x ⟶[𝟙 a] (D.pull f y)) (h : β ≫ᵈ D.clift f y = φ) : β = D.cartesianFactor φ :=
  IsCartesian.lift_uniq (D.isCartesianClift f y) β h

@[rewrite_rule]
theorem cartesianFactor_clift (f : a ⟶ a') (y : D.Ob a') :
    D.cartesianFactor (D.clift f y) = 𝟙ᵈ (D.pull f y) :=
  (D.cartesianFactor_uniq (D.clift f y) (𝟙ᵈ _) rfl).symm

/-- The factorizations of heterogeneously equal morphisms over equal base morphisms are
heterogeneously equal. -/
theorem cartesianFactor_heq {f f' : a ⟶ a'} (h : f = f') {x : D.Ob a} {y : D.Ob a'}
    {φ : x ⟶[f] y} {φ' : x ⟶[f'] y} (hφ : φ ≍ φ') :
    D.cartesianFactor φ ≍ D.cartesianFactor φ' := by
  subst h
  cases hφ
  rfl

/-- The hom-set bijection defining a fibration: `(x ⟶[f] y) ≃ (x ⟶ pull f y)`. -/
def cartesianHomEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
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
irreducible_def pullMap (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.pull f x ⟶ D.pull f y :=
  D.cartesianFactor (D.clift f x ≫ᵈ β)

/-- The defining property of `pullMap`. -/
theorem pullMap_clift (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.pullMap f β ≫ᵈ D.clift f y = D.clift f x ≫ᵈ β := by
  rw [pullMap_def]

/-- `pullMap` unfolded, stated with `IsCartesian.lift` and `Fib.clift`, on which no rule is keyed.
Unlike `pullMap_def`, which the rules below turn into `pullMap f β = pullMap f β`, it can be used
after them: it compares `pullMap` in two fibrations whose factorizations agree. -/
theorem pullMap_eq_lift (f : a ⟶ a') {x y : D.Fiber a'} (β : x ⟶ y) :
    D.pullMap f β =
      (Fib.isCartesianClift f y).lift (𝟙 a) (D.comp (g := 𝟙 a') (Fib.clift f x) β) := by
  rw [pullMap_def]
  rfl

/-! The laws of `pullMap` and `cartesianFactor` below are proved before the interchange rule
`clift_vert` is declared: once it is a rule, `pullMap_clift` holds by `rfl` and can no longer be
used to reason about `pullMap`. -/

/-- `pullMap f` preserves identities. -/
theorem pullMap_id_vert (f : a ⟶ a') (x : D.Fiber a') :
    D.pullMap f (𝟙ᵈ x) = 𝟙ᵈ (D.pull f x) :=
  IsCartesian.hom_ext (φ := D.clift f x) (D.isCartesianClift f x) (D.pullMap_clift f (𝟙ᵈ x))

/-- `pullMap f` preserves composition. -/
theorem pullMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a'} (β : x ⟶ y) (γ : y ⟶ z) :
    D.pullMap f (β ≫ᵈ γ) = D.pullMap f β ≫ᵈ D.pullMap f γ := by
  refine IsCartesian.hom_ext (φ := D.clift f z) (D.isCartesianClift f z) ?_
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
  refine IsCartesian.hom_ext (φ := D.clift (f ≫ g) y) (D.isCartesianClift (f ≫ g) y) ?_
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
def pullFunctor (f : a ⟶ a') : D.Fiber a' ⥤ D.Fiber a where
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

/-! The chosen lifts of a split `D` in `D.Total` are split, as rules: rules keyed on the
identities and composites of `D.Total` then apply to `totalClift (𝟙 a) y` and
`totalClift (f ≫ g) y`, which are these only up to unfolding. -/

@[rewrite_rule]
theorem totalClift_id (y : D.Ob a) : D.totalClift (𝟙 a) y = 𝟙 (D.tot y) := rfl

@[rewrite_rule]
theorem totalClift_comp (f : a ⟶ a') (g : a' ⟶ a'') (y : D.Ob a'') :
    D.totalClift (f ≫ g) y = D.totalClift f (D.pull g y) ≫ D.totalClift g y := rfl

end TotalSplit

/-! ## Preservation of cartesian morphisms -/

section Preservation

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A} [Fib D]

/-- The factorization of a cartesian morphism through the chosen lift is a vertical isomorphism,
with inverse the factorization of the chosen lift through it. -/
theorem cartesianFactor_inv_comp {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    {φ : x ⟶[f] y} (H : IsCartesian φ) :
    H.lift (𝟙 a) (D.clift f y) ≫ᵈ D.cartesianFactor φ = 𝟙ᵈ (D.pull f y) :=
  IsCartesian.hom_ext (D.isCartesianClift f y) (H.lift_fac (𝟙 a) (D.clift f y))

theorem cartesianFactor_comp_inv {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'}
    {φ : x ⟶[f] y} (H : IsCartesian φ) :
    D.cartesianFactor φ ≫ᵈ H.lift (𝟙 a) (D.clift f y) = 𝟙ᵈ x :=
  H.hom_ext (congrArg (D.cartesianFactor φ ≫ᵈ ·) (H.lift_fac (𝟙 a) (D.clift f y)))

/-- A vertical functor out of a fibration preserves cartesian morphisms as soon as it sends the
chosen lifts to cartesian morphisms: every cartesian morphism is a vertical isomorphism followed
by a chosen lift. -/
def VertFunctor.isCartesianMapOfClift (P : VertFunctor D E)
    (hP : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'), IsCartesian (P.map (D.clift f y))) :
    P.PreservesCartesian := fun {a _ f _ y φ} H =>
  ((congrArg P.map (D.cartesianFactor_comp_clift φ).symm).trans (P.map_comp _ _)) ▸
    (hP f y).isoComp _ (P.map (H.lift (𝟙 a) (D.clift f y)))
      (congrArg P.map (cartesianFactor_inv_comp H) :)
      (congrArg P.map (cartesianFactor_comp_inv H) :)

end Preservation

/-! ## Transfer along equivalences -/

section Transfer

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}

/-- A cleavage transfers along an equivalence over `A`: the chosen lift at `y` is the image of the
chosen lift at `G y`, followed by the counit. -/
@[instance_reducible]
def VertEquivalence.fib (e : VertEquivalence D E) [Fib D] : Fib E where
  pull f y := e.functor.obj (D.pull f (e.inverse.obj y))
  clift f y := (e.functor.map (D.clift f (e.inverse.obj y)) ≫ᵈ e.counitIso.hom.app y :)
  isCartesianClift f y :=
    (e.isCartesianMap (D.isCartesianClift f _)).compIso _ (e.counitIso.inv.app y)
      (VertNatIso.inv_hom_id_app e.counitIso y) (VertNatIso.hom_inv_id_app e.counitIso y)

end Transfer

end Displayed
