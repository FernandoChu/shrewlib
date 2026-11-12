import TwoCategory.Monad.Bicategory
import TwoCategory.Monad.Basic
import TwoCategory.Monad.PseudoAlgebra
import TwoCategory.Monad.LaxIdempotent
import TwoCategory.Monad.ColaxIdempotent
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
* `PseudoAlgebra`: pseudo-algebras of a 2-monad, whose unit and associativity laws hold up to
  coherent invertible 2-cells, and normal pseudo-algebras, whose unit law holds on the nose. The
  associativity law of the 2-monad is a rule there, so the coherence laws need no transport.
* `LaxIdempotent`: lax idempotent (Kock–Zöberlein) 2-monads, with a modification `δ : Tη ⟶ ηT`,
  so that `T η_x ⊣ μ_x`. Their algebra structures on `x` are adjoint to the unit `η_x`:
  pseudo-algebras are left adjoints of `η_x` with invertible counit (`pseudoAlgEquiv`), normal
  pseudo-algebras are left adjoint left inverses (LALIs) of `η_x` (`normalPseudoAlgEquiv`), and
  strict algebras are LALIs `a` with `μ_x ≫ a = T a ≫ a` (`algEquiv`).
* `ColaxIdempotent`: the dual for 2-comonads, reversing the 1-cells. A colax idempotent 2-comonad
  has a modification `θ : Tε ⟶ εT`, so that `δ_x ⊣ T ε_x`, and its strict coalgebras are the
  split right adjoint right inverses (RARIs) `ε_x ⊣ c` of the counits, with identity counit
  (`coalgEquiv`). The counit and coassociativity laws of 2-comonads are rules from there on.
-/

universe w v u

open CategoryTheory TwoCategory

/-! ## Main results -/

/-- The strict algebras of a 2-monad form a 2-category. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) : TwoCategory M.Alg :=
  inferInstance

/-- The pseudo-algebras of a lax idempotent 2-monad are the left adjoints of the units with
invertible counit. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) (K : M.LaxIdempotent) :
    M.PseudoAlg ≃ Σ x : C, M.PseudoReflection x :=
  K.pseudoAlgEquiv

/-- The normal pseudo-algebras of a lax idempotent 2-monad are the LALIs of the units. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) (K : M.LaxIdempotent) :
    M.NormalPseudoAlg ≃ Σ x : C, M.Reflection x :=
  K.normalPseudoAlgEquiv

/-- The strict algebras of a lax idempotent 2-monad are the split LALIs of the units. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoMonad C) (K : M.LaxIdempotent) :
    M.Alg ≃ Σ x : C, M.SplitReflection x :=
  K.algEquiv

/-- The strict coalgebras of a colax idempotent 2-comonad are the split RARIs of the counits. -/
example {C : Type u} [TwoCategory.{w, v} C] (M : TwoComonad C) (K : M.ColaxIdempotent) :
    M.Coalg ≃ Σ x : C, M.SplitCoreflection x :=
  K.coalgEquiv
