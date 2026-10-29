import Tactic.KernelTactic
import Tactic.KernelRfl

/-!
# Tactics

* `KernelTactic`: `kernel_exact` and `kernel_rfl'`, which hand definitional equalities that the
  rules reduce in many steps to the kernel, faster than the elaborator.
* `KernelRfl`: `kernel_rfl`, which also normalizes the implicit 1-cells of whiskerings, for
  equations of 2-cells.
-/
