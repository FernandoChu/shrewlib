import Lean

/-!
# Checking definitional equalities in the kernel

Comparing terms that the rules reduce in many steps is slow in the elaborator, which first tries
hard to unify the arguments of applications with the same head, while the kernel is fast. The
tactics `kernel_exact` and `kernel_rfl'` hand such comparisons to the kernel, as `kernel_rfl` in
`Tactic/KernelRfl`.

The kernel makes each comparison once (`KernelTactic.close`): the proof is added as an auxiliary
theorem stating the goal, as `decide +kernel` does, and the kernel compares the two propositions
when it checks this theorem. The goal is closed by the theorem, whose type is the goal
syntactically. Comparing them in the tactic and then assigning the proof to the goal would make
the kernel compare them a second time, when it checks the declaration.
-/

open Lean Meta Elab in
/-- Closes the goal `goal`, whose type is the proposition `ty`, with a proof `v` of a proposition
that the kernel is to check definitionally equal to `ty`: `v` is added as an auxiliary theorem
stating `ty`, in the local context of the goal, and the goal is closed by this theorem. Fails with
`msg` and the error of the kernel if the kernel rejects the theorem. Neither `ty` nor `v` may
contain metavariables. -/
def KernelTactic.close (goal : MVarId) (ty v : Expr) (msg : MessageData) : MetaM Unit := do
  let pf ← try
      withOptions (Elab.async.set · false) <| mkAuxTheorem ty v (zetaDelta := true)
    catch ex =>
      if ex.isRuntime then throw ex
      throwError "{msg}{indentD ex.toMessageData}"
  goal.assign pf

open Lean Meta Elab Tactic in
/-- `kernel_exact e` closes the goal with `e`, elaborated without the goal as expected type: the
kernel checks that the type of `e` is definitionally equal to the goal. If the goal is a `HEq` and
`e` an equation, `e` is turned into a `HEq`. -/
elab "kernel_exact " e:term : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let v ← instantiateMVars (← Term.elabTermAndSynthesize e none)
  if v.hasMVar then
    throwError "kernel_exact: the term contains metavariables"
  let vty ← instantiateMVars (← inferType v)
  let v ← if ty.heq?.isSome && vty.eq?.isSome then mkAppM ``heq_of_eq #[v] else pure v
  let vty ← instantiateMVars (← inferType v)
  if !ty.hasMVar && (← isProp ty) then
    KernelTactic.close goal ty v m!"kernel_exact: the type{indentExpr vty}\nis not{indentExpr ty}"
  else
    -- The goal is not a proposition, or is not known yet: the kernel compares the types here,
    -- and again when it checks the declaration.
    match Kernel.isDefEq (← getEnv) (← instantiateLCtxMVars (← getLCtx)) ty vty with
    | .ok true => goal.assign (← mkExpectedTypeHint v ty)
    | .ok false => throwError "kernel_exact: the type{indentExpr vty}\nis not{indentExpr ty}"
    | .error _ => throwError "kernel_exact: the kernel failed to compare the types"

open Lean Meta Elab Tactic in
/-- Closes a goal `a = b` or `HEq a b` by reflexivity, checked in the kernel. -/
elab "kernel_rfl'" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let msg : MessageData := "kernel_rfl': the two sides are not definitionally equal"
  let defEq (a b : Expr) : MetaM Bool := do
    match Kernel.isDefEq (← getEnv) (← instantiateLCtxMVars (← getLCtx)) a b with
    | .ok r => pure r
    | .error _ => throwError "kernel_rfl': the kernel failed to check the equation"
  if let some (_, lhs, rhs) := ty.eq? then
    if !ty.hasMVar then
      KernelTactic.close goal ty (← mkEqRefl lhs) msg
    else
      unless ← defEq lhs rhs do throwError msg
      goal.assign (← mkExpectedTypeHint (← mkEqRefl lhs) ty)
  else if let some (α, lhs, β, rhs) := ty.heq? then
    if !ty.hasMVar then
      KernelTactic.close goal ty (← mkHEqRefl lhs) msg
    else
      unless (← defEq α β) && (← defEq lhs rhs) do throwError msg
      goal.assign (← mkExpectedTypeHint (← mkHEqRefl lhs) ty)
  else
    throwError "kernel_rfl': the goal is not an equation"
