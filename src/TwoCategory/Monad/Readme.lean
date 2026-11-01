import TwoCategory.Monad.Bicategory
import TwoCategory.Monad.Basic
import TwoCategory.Monad.LaxIdempotent
import TwoCategory.Monad.DistributiveLaw

/-!
# Monads in bicategories and 2-monads

* `Bicategory`: monads in a bicategory (`Bicategory.Monad`, as monoids in `a ⟶ a`, dually to
  Mathlib's comonads).
* `Basic`: strict 2-monads and 2-comonads on a 2-category, whose (co)unit and (co)multiplication
  are 2-natural; their 1-dimensional naturality is a rule, so the 2-dimensional one needs no
  transport. Their strict (co)algebras form 2-categories `Alg M` and `Coalg M`, whose laws hold by
  `rfl`. The unit laws of 2-monads are rules from the end of the file on.
* `DistributiveLaw`: distributive laws of a 2-comonad over a 2-monad, 2-natural transformations
  `L R ⟶ R L` compatible with the (co)units and (co)multiplications, as in AWFSs.
* `LaxIdempotent`: lax idempotent (Kock–Zöberlein) 2-monads, with a modification `δ : Tη ⟶ ηT`.
  Their algebras are the split reflections: an algebra structure on `x` is the same as a split
  retraction of `η_x` left adjoint to `η_x` with identity counit (`LaxIdempotent.algEquiv`).
-/

universe w v u

open CategoryTheory TwoCategory

/-! ## Main results -/

/-- The strict algebras of a 2-monad form a 2-category. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) : TwoCategory M.Alg :=
  inferInstance

/-- The algebras of a lax idempotent 2-monad are the split reflections. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) (K : M.LaxIdempotent) :
    M.Alg ≃ Σ x : C, M.SplitReflection x :=
  K.algEquiv
