import Rules.Category
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# 2-categories

A 2-category is a strict bicategory: a `Bicategory` whose unitors and associators are given by the
equalities `𝟙 a ≫ f = f`, `f ≫ 𝟙 b = f` and `(f ≫ g) ≫ h = f ≫ g ≫ h` (Mathlib's
`Bicategory.Strict`). `TwoCategory B` bundles the two, so that its instance occurs in the laws
below, which are rules:

* the laws of 1-cells, so that composites of 1-cells are right-associated, without identities;
* the unitors and associators are identities, `λ_ f ↦ Iso.refl f`, and so on;
* whiskering is functorial, `f ◁ (η ≫ θ) ↦ f ◁ η ≫ f ◁ θ` and so on;
* whiskering is strictly unital and associative: `𝟙 a ◁ η ↦ η`, `(f ≫ g) ◁ η ↦ f ◁ g ◁ η`,
  `η ▷ 𝟙 b ↦ η`, `η ▷ (g ≫ h) ↦ η ▷ g ▷ h` and `(f ◁ η) ▷ h ↦ f ◁ η ▷ h`.

Together with the category laws for 2-cells (`Rules.Category`), whiskered 2-cells have a normal
form `f₁ ◁ ⋯ ◁ fₙ ◁ η ▷ g₁ ▷ ⋯ ▷ gₘ`, and the coherence laws of the bicategory hold by `rfl`.
Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory

/-- A 2-category: a bicategory whose unitors and associators are identities. -/
class TwoCategory (B : Type u) extends Bicategory.{w, v} B, Bicategory.Strict B

namespace TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] {a b c d : B}

/-! ## 1-cells -/

@[rewrite_rule]
theorem id_comp' (f : a ⟶ b) : 𝟙 a ≫ f = f :=
  Strict.id_comp f

@[rewrite_rule]
theorem comp_id' (f : a ⟶ b) : f ≫ 𝟙 b = f :=
  Strict.comp_id f

@[rewrite_rule]
theorem assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Strict.assoc f g h

/-! ## Unitors and associators -/

@[rewrite_rule]
theorem leftUnitor_eq (f : a ⟶ b) : λ_ f = Iso.refl f :=
  Strict.leftUnitor_eqToIso f

@[rewrite_rule]
theorem rightUnitor_eq (f : a ⟶ b) : ρ_ f = Iso.refl f :=
  Strict.rightUnitor_eqToIso f

@[rewrite_rule]
theorem associator_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : α_ f g h = Iso.refl (f ≫ g ≫ h) :=
  Strict.associator_eqToIso f g h

/-! ## Whiskering -/

@[rewrite_rule]
theorem whiskerLeft_id' (f : a ⟶ b) (g : b ⟶ c) : f ◁ 𝟙 g = 𝟙 (f ≫ g) :=
  Bicategory.whiskerLeft_id f g

@[rewrite_rule]
theorem whiskerLeft_comp' (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ :=
  Bicategory.whiskerLeft_comp f η θ

@[rewrite_rule]
theorem id_whiskerRight' (f : a ⟶ b) (g : b ⟶ c) : 𝟙 f ▷ g = 𝟙 (f ≫ g) :=
  Bicategory.id_whiskerRight f g

@[rewrite_rule]
theorem comp_whiskerRight' {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i :=
  Bicategory.comp_whiskerRight η θ i

@[rewrite_rule]
theorem id_whiskerLeft' {f g : a ⟶ b} (η : f ⟶ g) : 𝟙 a ◁ η = η :=
  Bicategory.id_whiskerLeft η

@[rewrite_rule]
theorem comp_whiskerLeft' (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η = f ◁ g ◁ η :=
  Bicategory.comp_whiskerLeft f g η

@[rewrite_rule]
theorem whiskerRight_id' {f g : a ⟶ b} (η : f ⟶ g) : η ▷ 𝟙 b = η :=
  Bicategory.whiskerRight_id η

@[rewrite_rule]
theorem whiskerRight_comp' {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) = η ▷ g ▷ h :=
  Bicategory.whiskerRight_comp η g h

@[rewrite_rule]
theorem whisker_assoc' (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h = f ◁ η ▷ h :=
  Bicategory.whisker_assoc f η h

/-! ## Whiskering with equal 1-cells

A rule `f ≫ g ↦ h` on 1-cells overlaps with the rules for whiskering with a composite: the 2-cells
`(f ≫ g) ◁ η` and `θ ▷ (f ≫ g)` rewrite both to `f ◁ g ◁ η`, `θ ▷ f ▷ g` and to `h ◁ η`, `θ ▷ h`.
Such rules come with the whiskered forms `f ◁ g ◁ η ↦ h ◁ η` and `θ ▷ f ▷ g ↦ θ ▷ h`, which are
proved from the following, and with the reassociated form `f ≫ g ≫ k ↦ h ≫ k`. -/

theorem whiskerLeft_congr {f f' : a ⟶ b} (e : f = f') {g h : b ⟶ c} (η : g ⟶ h) :
    HEq (f ◁ η) (f' ◁ η) := by
  cases e; rfl

theorem whiskerRight_congr {f g : a ⟶ b} (η : f ⟶ g) {h h' : b ⟶ c} (e : h = h') :
    HEq (η ▷ h) (η ▷ h') := by
  cases e; rfl

/-! ## Checking definitional equalities in the kernel -/

open Lean Meta in
/-- Recomputes the implicit 1-cells of whiskerings from the types of their explicit 2-cells. They
can differ from these by definitional equality, for example after `IsComma.hom_ext` gives both
sides of an equation the type of one of them, and rules match implicit arguments structurally. -/
def canonicalizeWhiskers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Bicategory.whiskerLeft 9 then
      let args := e.getAppArgs
      let some (_, _, g, h) := (← whnfR (← inferType args[8]!)).app4? ``Quiver.Hom |
        return .continue
      return .done (mkAppN e.getAppFn (args.set! 6 g |>.set! 7 h))
    else if e.isAppOfArity ``Bicategory.whiskerRight 9 then
      let args := e.getAppArgs
      let some (_, _, f, g) := (← whnfR (← inferType args[7]!)).app4? ``Quiver.Hom |
        return .continue
      return .done (mkAppN e.getAppFn (args.set! 5 f |>.set! 6 g))
    else
      return .continue)

open Lean Meta Elab Tactic in
/-- Closes a goal `a = b` or `HEq a b` by reflexivity, checking `a ≡ b` (and the equality of their
types) in the kernel rather than the elaborator. Both apply the rules, but the elaborator first
tries hard to unify the arguments of applications with the same head, which is slow on composites
of many 1-cells induced by universal properties.

If the kernel does not identify the two sides of an equation directly, they are compared through
their forms with canonical implicit arguments (`canonicalizeWhiskers`) and the weak head normal
forms of these, computed by the kernel: when it compares two applications of the same head, it
compares their arguments first, which can fail where rewriting both sides would succeed. -/
elab "kernel_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.hasMVar then
    throwError "kernel_rfl: the goal contains metavariables"
  let env ← getEnv
  let lctx ← getLCtx
  let defEq (a b : Expr) : MetaM Bool := do
    match Kernel.isDefEq env lctx a b with
    | .ok r => pure r
    | .error _ => throwError "kernel_rfl: the kernel failed to check the equation"
  let whnf (e : Expr) : MetaM Expr := do
    match Kernel.whnf env lctx e with
    | .ok e => pure e
    | .error _ => throwError "kernel_rfl: the kernel failed to reduce the equation"
  if let some (α, lhs, rhs) := ty.eq? then
    if ← defEq lhs rhs then
      goal.assign (← mkEqRefl lhs)
    else
      let cl ← canonicalizeWhiskers lhs
      let cr ← canonicalizeWhiskers rhs
      let nl ← whnf cl
      let nr ← whnf cr
      unless ← defEq nl nr do
        throwError "kernel_rfl: the two sides are not definitionally equal"
      let u ← getLevel α
      let step (a b : Expr) : MetaM Expr := do
        mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [u]) α a) (← mkEq a b)
      let trans (h₁ h₂ : Expr) (a b c : Expr) : Expr :=
        mkApp6 (mkConst ``Eq.trans [u]) α a b c h₁ h₂
      let h := trans (← step lhs cl) (trans (← step cl nl) (trans (← step nl cr)
        (← step cr rhs) nl cr rhs) cl nl rhs) lhs cl rhs
      goal.assign h
  else if let some (α, lhs, β, rhs) := ty.heq? then
    unless (← defEq α β) && (← defEq lhs rhs) do
      throwError "kernel_rfl: the two sides are not definitionally equal"
    goal.assign (← mkHEqRefl lhs)
  else
    throwError "kernel_rfl: the goal is not an equation"

/-! ## Tests -/

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) := rfl

example {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (θ : g ⟶ g') :
    η ▷ g ≫ f' ◁ θ = f ◁ θ ≫ η ▷ g' :=
  (whisker_exchange η θ).symm

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom ▷ 𝟙 d ≫ (𝟙 a ≫ f) ◁ (λ_ (g ≫ h)).inv = 𝟙 (f ≫ g ≫ h) := rfl

end TwoCategory

end CategoryTheory
