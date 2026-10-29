import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# `kernel_rfl`

`kernel_rfl` closes a goal `a = b` or `HEq a b` by reflexivity, checked in the kernel rather than
the elaborator. For equations of 2-cells, it first recomputes the implicit 1-cells of whiskerings
from the types of their 2-cells (`KernelRfl.canonicalizeWhiskers`), and compares the weak head
normal forms of both sides.
-/

open CategoryTheory

open Lean Meta in
/-- Recomputes the implicit 1-cells of whiskerings from the types of their explicit 2-cells. They
can differ from these by definitional equality, for example after `IsComma.hom_ext` gives both
sides of an equation the type of one of them, and rules match implicit arguments structurally. -/
def KernelRfl.canonicalizeWhiskers (e : Expr) : MetaM Expr :=
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
their forms with canonical implicit arguments (`KernelRfl.canonicalizeWhiskers`) and the weak
head normal forms of these, computed by the kernel: when it compares two applications of the same
head, it compares their arguments first, which can fail where rewriting both sides would
succeed. -/
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
      let cl ← KernelRfl.canonicalizeWhiskers lhs
      let cr ← KernelRfl.canonicalizeWhiskers rhs
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
