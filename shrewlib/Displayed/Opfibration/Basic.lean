import Displayed.Displayed.Basic
import Displayed.Displayed.Total
import Mathlib.Tactic.IrreducibleDef

/-!
# Opfibrations

The file starts with opcartesian morphisms (`IsOpcartesian`: the strong opcartesian property and
its universal-property API), which vertical equivalences preserve
(`VertEquivalence.isOpcartesianMap`) and fully faithful vertical functors reflect
(`VertFunctor.FullyFaithful.isOpcartesianOfMap`). `IsOpcartesian φ` carries the factorization
through `φ` as data, with its uniqueness: Lean has no computable unique choice, so a `Prop`
stating unique existence would make every construction from the factorizations, such as
`pushMap`, noncomputable. By uniqueness it is a subsingleton.

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

These make the dual opfibration of `B` (`Opfibration/DualOp.lean`) a displayed category whose laws
hold by `rfl`. Since the interchange rule has `pushMap` on its right-hand side, and `pushMap` is
defined by a factorization that the rules rewrite back into `pushMap`, `pushMap` is an
`irreducible_def`: unfolding it would loop. It is unfolded by `pushMap_eq_desc`, stated with
`Opfib.olift` and `IsOpcartesian.desc`, on which no rule is keyed, to compute it in concrete
opfibrations.

Finally, an opcleavage transfers along an equivalence over `A` (`VertEquivalence.opfib`).

`Fibration/Basic.lean` is the exact dual, with chosen cartesian lifts
`clift f y : pull f y ⟶[f] y`. Its sections mirror the sections of this file.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A]

open scoped Displayed

/-! ## Opcartesian morphisms -/

section Opcartesian

variable {D : Displayed.{v₂, u₂} A}

/-- `φ : x ⟶[f] y` is *opcartesian*: every displayed map out of `x` over `f ≫ g` factors uniquely
through `φ` by a displayed map over `g`. (This is the *strong* opcartesian property.) The
factorization is data, so that it computes; it is unique, so that this structure is a
subsingleton. -/
structure IsOpcartesian {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) where
  /-- The factorization of `χ` through `φ`. -/
  desc : ∀ {a'' : A} (g : a' ⟶ a'') {z : D.Ob a''}, (x ⟶[f ≫ g] z) → (y ⟶[g] z)
  desc_fac : ∀ {a'' : A} (g : a' ⟶ a'') {z : D.Ob a''} (χ : x ⟶[f ≫ g] z), φ ≫ᵈ desc g χ = χ
  /-- Any factorization of `χ` through `φ` agrees with `desc`. -/
  desc_uniq : ∀ {a'' : A} {g : a' ⟶ a''} {z : D.Ob a''} {χ : x ⟶[f ≫ g] z} (ψ : y ⟶[g] z),
    φ ≫ᵈ ψ = χ → ψ = desc g χ

attribute [simp] IsOpcartesian.desc_fac

namespace IsOpcartesian

variable {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}

instance : Subsingleton (IsOpcartesian φ) where
  allEq H H' := by
    obtain ⟨d, fac, _⟩ := H
    obtain ⟨d', _, uniq'⟩ := H'
    obtain rfl : @d = @d' := by
      funext a'' g z χ
      exact uniq' _ (fac g χ)
    rfl

/-- Two maps out of `y` that agree after precomposition with an opcartesian `φ` are equal. -/
theorem hom_ext (H : IsOpcartesian φ) {a'' : A} {g : a' ⟶ a''} {z : D.Ob a''}
    {ψ ψ' : y ⟶[g] z} (h : φ ≫ᵈ ψ = φ ≫ᵈ ψ') : ψ = ψ' :=
  (H.desc_uniq ψ rfl).trans (H.desc_uniq ψ' h.symm).symm

/-- Precomposing an opcartesian morphism with a vertical isomorphism gives an opcartesian
morphism. -/
def isoComp {x' : D.Ob a} (H : IsOpcartesian φ) (ι : x' ⟶[𝟙 a] x) (ι' : x ⟶[𝟙 a] x')
    (h : ι' ≫ᵈ ι = 𝟙ᵈ x) (h' : ι ≫ᵈ ι' = 𝟙ᵈ x') : IsOpcartesian (ι ≫ᵈ φ) where
  desc g _ χ := H.desc g (ι' ≫ᵈ χ :)
  desc_fac g _ χ :=
    ((congrArg (ι ≫ᵈ ·) (H.desc_fac g (ι' ≫ᵈ χ :))).trans (congrArg (· ≫ᵈ χ) h') :)
  desc_uniq ψ hψ := H.desc_uniq ψ
    ((congrArg (fun t => t ≫ᵈ (φ ≫ᵈ ψ)) h).symm.trans (congrArg (ι' ≫ᵈ ·) hψ) :)

end IsOpcartesian

/-- A displayed functor *preserves opcartesian morphisms* if it sends opcartesian morphisms to
opcartesian morphisms; since `IsOpcartesian` is data, this is a function on the factorizations. -/
abbrev DispFunctor.PreservesOpcartesian {B : Type u₄} [Category.{v₄} B] {u : A ⥤ B}
    {E : Displayed.{v₅, u₅} B} (F : DispFunctor u D E) : Type _ :=
  ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y},
    IsOpcartesian φ → IsOpcartesian (F.map φ)

namespace VertEquivalence

variable {E : Displayed.{v₃, u₃} A} (e : VertEquivalence D E)

/-- **A vertical equivalence preserves opcartesian morphisms.** The factorization of `χ` is the
image of the factorization of the preimage of `χ`, followed by the counit. -/
def isOpcartesianMap : e.functor.PreservesOpcartesian := fun {_ _ _ _ _ φ} H => {
  desc {_} g z χ :=
    (e.functor.map (H.desc g (e.preimage (χ ≫ᵈ e.counitIso.inv.app z :))) ≫ᵈ
      e.counitIso.hom.app z :)
  desc_fac {_} g z χ :=
    (((congrArg (fun t => e.functor.map t ≫ᵈ e.counitIso.hom.app z)
      (H.desc_fac g (e.preimage (χ ≫ᵈ e.counitIso.inv.app z :)))).trans
        (congrArg (· ≫ᵈ e.counitIso.hom.app z)
          (e.map_preimage (χ ≫ᵈ e.counitIso.inv.app z :)))).trans
        (congrArg (χ ≫ᵈ ·) (VertNatIso.inv_hom_id_app e.counitIso z)) :)
  desc_uniq {_ g z χ} ψ hψ := by
    let ε := e.counitIso
    have h₁ : φ ≫ᵈ e.preimage (ψ ≫ᵈ ε.inv.app z :) = e.preimage (χ ≫ᵈ ε.inv.app z :) :=
      e.map_injective
        (((congrArg (e.functor.map φ ≫ᵈ ·) (e.map_preimage _)).trans
          ((congrArg (· ≫ᵈ ε.inv.app z) hψ).trans (e.map_preimage _).symm)) :)
    have h₂ : e.preimage (ψ ≫ᵈ ε.inv.app z :) = H.desc g (e.preimage (χ ≫ᵈ ε.inv.app z :)) :=
      H.desc_uniq _ h₁
    exact ((congrArg (ψ ≫ᵈ ·) (VertNatIso.inv_hom_id_app ε z)).symm.trans
      (congrArg (· ≫ᵈ ε.hom.app z) ((e.map_preimage _).symm.trans (congrArg e.functor.map h₂))) :) }

end VertEquivalence

namespace VertFunctor.FullyFaithful

variable {E : Displayed.{v₃, u₃} A} {F : VertFunctor D E} (hF : F.FullyFaithful)

/-- **A fully faithful vertical functor reflects opcartesian morphisms.** The factorization of `χ`
is the preimage of the factorization of its image. -/
def isOpcartesianOfMap {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}
    (H : IsOpcartesian (F.map φ)) : IsOpcartesian φ where
  desc g _ χ := hF.preimage (H.desc g (F.map χ))
  desc_fac g _ χ := hF.map_injective
    ((congrArg (F.map φ ≫ᵈ ·) (hF.map_preimage _)).trans (H.desc_fac g (F.map χ)))
  desc_uniq ψ hψ := hF.map_injective
    ((H.desc_uniq (F.map ψ) (congrArg F.map hψ)).trans (hF.map_preimage _).symm)

end VertFunctor.FullyFaithful

end Opcartesian

/-! ## The classes -/

/-- A (cloven) opfibration structure on a displayed category: a chosen opcartesian lift of every
base morphism at every object over its domain. -/
class Opfib (D : Displayed.{v₂, u₂} A) where
  /-- The chosen pushforward of `x` along `f`. -/
  push : {a a' : A} → (f : a ⟶ a') → D.Ob a → D.Ob a'
  /-- The chosen opcartesian lift of `f` at `x`. -/
  olift : {a a' : A} → (f : a ⟶ a') → (x : D.Ob a) → (x ⟶[f] push f x)
  /-- The chosen lifts are opcartesian. -/
  isOpcartesianOlift : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a), IsOpcartesian (olift f x)

/-- A pre-split opfibration: an opfibration whose chosen pushforwards are strictly functorial on
objects. These axioms are rewrite rules. Its axioms default to `by intros; rfl`, as they hold
definitionally in most instances. -/
class PreSplitOpfib (D : Displayed.{v₂, u₂} A) extends Opfib D where
  push_id : ∀ {a : A} (x : D.Ob a), push (𝟙 a) x = x := by intros; rfl
  push_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    push (f ≫ g) x = push g (push f x) := by intros; rfl

attribute [rewrite_rule] PreSplitOpfib.push_id PreSplitOpfib.push_comp

/-- A split opfibration: a pre-split opfibration whose chosen lifts are strictly functorial.

The pre-split structure is an instance field rather than a parent: the fields of a parent are
local variables while the later fields are elaborated, so the rules `push_id` and `push_comp`
would not apply to them. As a field, `push` is `Opfib.push` of an instance, the axioms on objects
hold definitionally, and the axioms on lifts are plain equations. Its axioms default to
`by intros; rfl`, as they hold definitionally in most instances. -/
class SplitOpfib (D : Displayed.{v₂, u₂} A) where
  /-- The underlying pre-split opfibration. -/
  [toPreSplitOpfib : PreSplitOpfib D]
  /-- The lift of the identity is the displayed identity. -/
  olift_id : ∀ {a : A} (x : D.Ob a), Opfib.olift (𝟙 a) x = 𝟙ᵈ x := by intros; rfl
  /-- The lift of a composite is the composite of lifts. -/
  olift_comp : ∀ {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a),
    Opfib.olift (f ≫ g) x = Opfib.olift f x ≫ᵈ Opfib.olift g (Opfib.push f x) := by intros; rfl

attribute [instance_reducible, instance] SplitOpfib.toPreSplitOpfib

attribute [rewrite_rule] SplitOpfib.olift_id SplitOpfib.olift_comp

/-! ## Chosen pushforwards and lifts -/

section Lift

variable (D : Displayed.{v₂, u₂} A) [Opfib D]

/-- The chosen pushforward of `x` along `f`, viewed as an object of the fiber over `a'`. -/
@[reducible] def push {a a' : A} (f : a ⟶ a') (x : D.Ob a) : D.Fiber a' :=
  Opfib.push f x

/-- The chosen opcartesian lift of `f` at `x`. -/
def olift {a a' : A} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] (D.push f x) := Opfib.olift f x

/-- The chosen lift is opcartesian. -/
def isOpcartesianOlift {a a' : A} (f : a ⟶ a') (x : D.Ob a) :
    IsOpcartesian (D.olift f x) := Opfib.isOpcartesianOlift f x

end Lift

section LiftPreSplit

variable (D : Displayed.{v₂, u₂} A) [PreSplitOpfib D]

@[rewrite_rule]
theorem push_id {a : A} (x : D.Ob a) : D.push (𝟙 a) x = x :=
  PreSplitOpfib.push_id x

@[rewrite_rule]
theorem push_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.push (f ≫ g) x = D.push g (D.push f x) :=
  PreSplitOpfib.push_comp f g x

end LiftPreSplit

section LiftSplit

variable (D : Displayed.{v₂, u₂} A) [SplitOpfib D]

@[rewrite_rule]
theorem olift_id {a : A} (x : D.Ob a) : D.olift (𝟙 a) x = 𝟙ᵈ x := SplitOpfib.olift_id x

@[rewrite_rule]
theorem olift_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.olift (f ≫ g) x = D.olift f x ≫ᵈ D.olift g (D.push f x) := SplitOpfib.olift_comp f g x

end LiftSplit

/-! ## Opcartesian factorization -/

section Factor

variable (D : Displayed.{v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Vertical factorization: any `φ : x ⟶[f] y` factors through the chosen lift `olift f x` by a
vertical morphism `push f x ⟶ y`. -/
def opcartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    (D.push f x) ⟶[𝟙 a'] y :=
  IsOpcartesian.desc (D.isOpcartesianOlift f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_comp_opcartesianFactor {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    D.olift f x ≫ᵈ D.opcartesianFactor φ = φ :=
  IsOpcartesian.desc_fac (D.isOpcartesianOlift f x) (𝟙 a') φ

@[rewrite_rule]
theorem olift_comp_opcartesianFactor_assoc {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z) :
    D.olift f x ≫ᵈ (D.opcartesianFactor φ ≫ᵈ ψ) = φ ≫ᵈ ψ :=
  congrArg (· ≫ᵈ ψ) (D.olift_comp_opcartesianFactor φ)

/-- Any vertical morphism factoring `φ` through the chosen lift agrees with
`opcartesianFactor φ`. -/
theorem opcartesianFactor_uniq {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y)
    (β : (D.push f x) ⟶[𝟙 a'] y) (h : D.olift f x ≫ᵈ β = φ) : β = D.opcartesianFactor φ :=
  IsOpcartesian.desc_uniq (D.isOpcartesianOlift f x) β h

@[rewrite_rule]
theorem opcartesianFactor_olift (f : a ⟶ a') (x : D.Ob a) :
    D.opcartesianFactor (D.olift f x) = 𝟙ᵈ (D.push f x) :=
  (D.opcartesianFactor_uniq (D.olift f x) (𝟙ᵈ _) rfl).symm

/-- `opcartesianFactor_olift` for the unfolding `Opfib.olift` of `D.olift`, which rules such as
`OpcartesianFunctor.map_olift` produce: rules are matched by unfolding the term, not the
pattern. -/
@[rewrite_rule]
theorem opcartesianFactor_opfibOlift (f : a ⟶ a') (x : D.Ob a) :
    D.opcartesianFactor (Opfib.olift f x) = 𝟙ᵈ (D.push f x) :=
  D.opcartesianFactor_olift f x

/-- The factorizations of heterogeneously equal morphisms over equal base morphisms are
heterogeneously equal. -/
theorem opcartesianFactor_heq {f f' : a ⟶ a'} (h : f = f') {x : D.Ob a} {y : D.Ob a'}
    {φ : x ⟶[f] y} {φ' : x ⟶[f'] y} (hφ : φ ≍ φ') :
    D.opcartesianFactor φ ≍ D.opcartesianFactor φ' := by
  subst h
  cases hφ
  rfl

/-- The hom-set bijection defining an opfibration: `(x ⟶[f] y) ≃ (push f x ⟶ y)`. -/
def opcartesianHomEquiv (f : a ⟶ a') (x : D.Ob a) (y : D.Ob a') :
    (x ⟶[f] y) ≃ ((D.push f x) ⟶[𝟙 a'] y) where
  toFun φ := D.opcartesianFactor φ
  invFun β := D.olift f x ≫ᵈ β
  left_inv _ := rfl
  right_inv β := (D.opcartesianFactor_uniq _ β rfl).symm

end Factor

section FactorSplit

variable (D : Displayed.{v₂, u₂} A) [SplitOpfib D] {a : A}

/-- The factorization of a vertical morphism is the morphism itself. -/
@[rewrite_rule]
theorem opcartesianFactor_vert {x y : D.Ob a} (β : x ⟶[𝟙 a] y) : D.opcartesianFactor β = β :=
  (D.opcartesianFactor_uniq β β rfl).symm

end FactorSplit

/-! ## Transport of vertical morphisms -/

section PushMap

variable (D : Displayed.{v₂, u₂} A) [Opfib D] {a a' a'' : A}

/-- Transport of a vertical morphism along `f`. -/
irreducible_def pushMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.push f x ⟶ D.push f y :=
  D.opcartesianFactor (β ≫ᵈ D.olift f y)

/-- The defining property of `pushMap`. -/
theorem olift_pushMap (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.olift f x ≫ᵈ D.pushMap f β = β ≫ᵈ D.olift f y := by
  rw [pushMap_def]

/-- `pushMap` unfolded, stated with `IsOpcartesian.desc` and `Opfib.olift`, on which no rule is
keyed. Unlike `pushMap_def`, which the rules below turn into `pushMap f β = pushMap f β`, it can
be used after them: it compares `pushMap` in two opfibrations whose factorizations agree, such as
an opfibration and its reindexing. -/
theorem pushMap_eq_desc (f : a ⟶ a') {x y : D.Fiber a} (β : x ⟶ y) :
    D.pushMap f β =
      (Opfib.isOpcartesianOlift f x).desc (𝟙 a') (D.comp (f := 𝟙 a) β (Opfib.olift f y)) := by
  rw [pushMap_def]
  rfl

/-! The laws of `pushMap` and `opcartesianFactor` below are proved before the interchange rule
`vert_olift` is declared: once it is a rule, `olift_pushMap` holds by `rfl` and can no longer be
used to reason about `pushMap`. -/

/-- `pushMap f` preserves identities. -/
theorem pushMap_id_vert (f : a ⟶ a') (x : D.Fiber a) :
    D.pushMap f (𝟙ᵈ x) = 𝟙ᵈ (D.push f x) :=
  IsOpcartesian.hom_ext (φ := D.olift f x) (D.isOpcartesianOlift f x) (D.olift_pushMap f (𝟙ᵈ x))

/-- `pushMap f` preserves composition. -/
theorem pushMap_comp_vert (f : a ⟶ a') {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.pushMap f (β ≫ᵈ γ) = D.pushMap f β ≫ᵈ D.pushMap f γ := by
  refine IsOpcartesian.hom_ext (φ := D.olift f x) (D.isOpcartesianOlift f x) ?_
  calc D.olift f x ≫ᵈ D.pushMap f (β ≫ᵈ γ) = β ≫ᵈ (γ ≫ᵈ D.olift f z) := D.olift_pushMap f _
    _ = β ≫ᵈ (D.olift f y ≫ᵈ D.pushMap f γ) :=
      congrArg (β ≫ᵈ ·) (D.olift_pushMap f γ).symm
    _ = D.olift f x ≫ᵈ (D.pushMap f β ≫ᵈ D.pushMap f γ) :=
      congrArg (· ≫ᵈ D.pushMap f γ) (D.olift_pushMap f β).symm

end PushMap

section PushMapSplit

variable (D : Displayed.{v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

/-- Transport along the identity is the identity. -/
theorem pushMap_id {x y : D.Fiber a} (β : x ⟶ y) : D.pushMap (𝟙 a) β = β :=
  D.olift_pushMap (𝟙 a) β

/-- Transport along a composite is the composite of transports. -/
theorem pushMap_comp (f : a ⟶ a') (g : a' ⟶ a'') {x y : D.Fiber a} (β : x ⟶ y) :
    D.pushMap (f ≫ g) β = D.pushMap g (D.pushMap f β) := by
  refine IsOpcartesian.hom_ext (φ := D.olift (f ≫ g) x) (D.isOpcartesianOlift (f ≫ g) x) ?_
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

variable (D : Displayed.{v₂, u₂} A) [Opfib D] {a a' a'' : A}

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
def pushFunctor (f : a ⟶ a') : D.Fiber a ⥤ D.Fiber a' where
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

variable (D : Displayed.{v₂, u₂} A) [Opfib D] {a a' a'' : A}

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

variable (D : Displayed.{v₂, u₂} A) [SplitOpfib D] {a a' a'' : A}

/-! The chosen lifts of a split `D` in `D.Total` are split, as rules: rules keyed on the
identities and composites of `D.Total` then apply to `totalOlift (𝟙 a) x` and
`totalOlift (f ≫ g) x`, which are these only up to unfolding. -/

@[rewrite_rule]
theorem totalOlift_id (x : D.Ob a) : D.totalOlift (𝟙 a) x = 𝟙 (D.tot x) := rfl

@[rewrite_rule]
theorem totalOlift_comp (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    D.totalOlift (f ≫ g) x = D.totalOlift f x ≫ D.totalOlift g (D.push f x) := rfl

end TotalSplit

/-! ## Transfer along equivalences -/

section Transfer

variable {D : Displayed.{v₂, u₂} A} {E : Displayed.{v₃, u₃} A}

/-- An opcleavage transfers along an equivalence over `A`: the chosen lift at `x` is the inverse
of the counit, followed by the image of the chosen lift at `G x`. -/
@[instance_reducible]
def VertEquivalence.opfib (e : VertEquivalence D E) [Opfib D] : Opfib E where
  push f x := e.functor.obj (D.push f (e.inverse.obj x))
  olift f x := (e.counitIso.inv.app x ≫ᵈ e.functor.map (D.olift f (e.inverse.obj x)) :)
  isOpcartesianOlift f x :=
    (e.isOpcartesianMap (D.isOpcartesianOlift f _)).isoComp _ (e.counitIso.hom.app x)
      (VertNatIso.hom_inv_id_app e.counitIso x) (VertNatIso.inv_hom_id_app e.counitIso x)

end Transfer

end Displayed
