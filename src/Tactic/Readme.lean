import Tactic.KernelTactic

/-!
# Tactics

* `KernelTactic`: `kernel_exact` and `kernel_rfl'`, which hand definitional equalities that the
  rules reduce in many steps to the kernel, faster than the elaborator.
-/
