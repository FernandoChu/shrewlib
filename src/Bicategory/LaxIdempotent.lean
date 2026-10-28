import Bicategory.Monad
import Bicategory.Adjunction

/-!
# Lax idempotent 2-monads

A 2-monad `M = (T, η, μ)` on a 2-category `C` is *lax idempotent* (or *Kock–Zöberlein*) if it comes
with a modification `δ : Tη ⟶ ηT`, that is 2-cells `δ x : T η_x ⟶ η_{T x}` natural in `x`, with
```
  δ x ▷ μ x = 𝟙 (𝟙 (T x))        η x ◁ δ x = 𝟙 (η x ≫ η (T x))
```
Equivalently, `μ_x ⊣ η_{T x}` with identity counit and unit `δ x`, see Kelly–Lack, *On
property-like structures*. The types of these equations agree by the unit laws of `M` and the
naturality of `η`, which are rules here.

The point of lax idempotence is that algebra structures are adjoint to units. Call a *retraction*
of `η_x` a 1-cell `a : T x ⟶ x` with `η_x ≫ a = 𝟙` (the unit law of an algebra), and *split* if
`μ_x ≫ a = T a ≫ a` (the associativity law). Then:

* a split retraction `a` is left adjoint to `η_x`, with identity counit and unit
  `δ x ▷ T a : 𝟙 = T η_x ≫ T a ⟶ η_{T x} ≫ T a = a ≫ η_x` (`Retraction.adjunction`);
* the adjunction is determined by its counit (`Adjunction.unit_eq_of_counit_eq`), so the strict
  algebras of `M` are the same as split retractions left adjoint to units with identity counit,
  `LaxIdempotent.algEquiv : M.Alg ≃ Σ x, M.SplitReflection x`.

Splitness is not implied by the adjunction: a left adjoint of `η_x` with identity counit is a
normal pseudo-algebra structure, not necessarily a strict one.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {C : Type u} [TwoCategory.{w, v} C]

/-! ## The unit laws as rules -/

namespace PreTwoMonad

variable (M : PreTwoMonad C)

attribute [rewrite_rule] PreTwoMonad.unit_left PreTwoMonad.unit_right

@[rewrite_rule]
theorem unit_left_assoc {x z : C} (k : M.T.obj x ⟶ z) : M.η (M.T.obj x) ≫ M.μ x ≫ k = k :=
  congrArg (· ≫ k) (M.unit_left x)

@[rewrite_rule]
theorem unit_right_assoc {x z : C} (k : M.T.obj x ⟶ z) : M.T.map (M.η x) ≫ M.μ x ≫ k = k :=
  congrArg (· ≫ k) (M.unit_right x)

/-- The naturality of `η`, mapped by `T`: the two normal forms of `T (η x ≫ T m)` agree. -/
@[rewrite_rule]
theorem map_η_naturality {x y : C} (m : x ⟶ y) :
    M.T.map (M.η x) ≫ M.T.map (M.T.map m) = M.T.map m ≫ M.T.map (M.η y) := by
  kernel_exact congrArg M.T.map (M.η_naturality m)

@[rewrite_rule]
theorem map_η_naturality_assoc {x y z : C} (m : x ⟶ y) (k : M.T.obj (M.T.obj y) ⟶ z) :
    M.T.map (M.η x) ≫ M.T.map (M.T.map m) ≫ k = M.T.map m ≫ M.T.map (M.η y) ≫ k :=
  congrArg (· ≫ k) (M.map_η_naturality m)

end PreTwoMonad

namespace TwoMonad

variable (M : TwoMonad C)

/-! ## Lax idempotence -/

/-- A lax idempotent 2-monad: a modification `δ : Tη ⟶ ηT` with `δ ▷ μ = 𝟙` and `η ◁ δ = 𝟙`. -/
structure LaxIdempotent where
  /-- The modification `δ x : T η_x ⟶ η_{T x}`. -/
  δ (x : C) : M.T.map (M.η x) ⟶ M.η (M.T.obj x)
  δ_naturality {x y : C} (m : x ⟶ y) : δ x ▷ M.T.map (M.T.map m) = M.T.map m ◁ δ y
  δ_whiskerRight_μ (x : C) : δ x ▷ M.μ x = 𝟙 (𝟙 (M.T.obj x))
  η_whiskerLeft_δ (x : C) : M.η x ◁ δ x = 𝟙 (M.η x ≫ M.η (M.T.obj x))

/-! ## Retractions of units -/

variable {M}

/-- A retraction of the unit `η_x`: a 1-cell `a : T x ⟶ x` with `η_x ≫ a = 𝟙`. -/
structure Retraction (x : C) where
  /-- The retraction `a`. -/
  act : M.T.obj x ⟶ x
  unit : M.η x ≫ act = 𝟙 x

attribute [rewrite_rule] Retraction.unit

namespace Retraction

variable {x : C} (r : M.Retraction x)

@[rewrite_rule]
theorem unit_assoc {z : C} (k : x ⟶ z) : M.η x ≫ r.act ≫ k = k :=
  congrArg (· ≫ k) r.unit

/-- The unit law, mapped by `T`. -/
@[rewrite_rule]
theorem map_unit : M.T.map (M.η x) ≫ M.T.map r.act = 𝟙 (M.T.obj x) := by
  kernel_exact congrArg M.T.map r.unit

@[rewrite_rule]
theorem map_unit_assoc {z : C} (k : M.T.obj x ⟶ z) :
    M.T.map (M.η x) ≫ M.T.map r.act ≫ k = k :=
  congrArg (· ≫ k) r.map_unit

/-- `η_{T x} ≫ T a ≫ a = a ≫ η_x ≫ a = a`, which the rules do not find, as the result of the
naturality of `η` is not reduced further. -/
@[rewrite_rule]
theorem η_comp_map_act_comp_act : M.η (M.T.obj x) ≫ M.T.map r.act ≫ r.act = r.act :=
  (M.toPreTwoMonad.η_naturality_assoc r.act r.act).trans
    ((congrArg (r.act ≫ ·) r.unit).trans (Category.comp_id _))

/-- The retraction is split: the associativity law of an algebra. -/
def IsSplit : Prop :=
  M.μ x ≫ r.act = M.T.map r.act ≫ r.act

variable (K : M.LaxIdempotent)

/-- The unit `δ x ▷ T a : 𝟙 ⟶ a ≫ η_x` of the adjunction `a ⊣ η_x`. -/
def adjUnit : 𝟙 (M.T.obj x) ⟶ r.act ≫ M.η x :=
  K.δ x ▷ M.T.map r.act

/-- The triangle law involving `η_x`, which holds for every retraction. -/
theorem η_whiskerLeft_adjUnit : M.η x ◁ r.adjUnit K = 𝟙 (M.η x) := by
  kernel_exact congrArg (· ▷ M.T.map r.act) (K.η_whiskerLeft_δ x)

/-- The triangle law involving `a`, which holds when `a` is split: `T a ≫ a = μ_x ≫ a`, and
`δ x ▷ μ_x` is the identity. -/
theorem adjUnit_whiskerRight (h : r.IsSplit) :
    K.δ x ▷ (M.T.map r.act ≫ r.act) = 𝟙 r.act := by
  have h' : K.δ x ▷ (M.μ x ≫ r.act) = 𝟙 r.act := by
    kernel_exact congrArg (· ▷ r.act) (K.δ_whiskerRight_μ x)
  exact eq_of_heq ((whiskerRight_congr (K.δ x) h.symm).trans (heq_of_eq h'))

theorem left_triangle (h : r.IsSplit) :
    leftZigzag (r.adjUnit K) (𝟙 (M.η x ≫ r.act)) = (λ_ r.act).hom ≫ (ρ_ r.act).inv := by
  kernel_exact r.adjUnit_whiskerRight K h

theorem right_triangle :
    rightZigzag (r.adjUnit K) (𝟙 (M.η x ≫ r.act)) = (ρ_ (M.η x)).hom ≫ (λ_ (M.η x)).inv := by
  kernel_exact r.η_whiskerLeft_adjUnit K

/-- For a lax idempotent 2-monad, a split retraction `a` of `η_x` is left adjoint to `η_x`, with
identity counit. -/
def adjunction (h : r.IsSplit) : r.act ⊣ M.η x where
  unit := r.adjUnit K
  counit := 𝟙 _
  left_triangle := r.left_triangle K h
  right_triangle := r.right_triangle K

end Retraction

variable (M) in
/-- A split reflection of `η_x`: a split retraction `a` of `η_x` that is left adjoint to `η_x`
with identity counit. -/
structure SplitReflection (x : C) where
  /-- The retraction `a`. -/
  toRetraction : M.Retraction x
  /-- The adjunction `a ⊣ η_x`. -/
  adj : toRetraction.act ⊣ M.η x
  counit_eq : adj.counit = 𝟙 _
  isSplit : toRetraction.IsSplit

/-! ## Algebras of lax idempotent 2-monads -/

namespace Alg

variable (A : M.Alg)

/-- The action of an algebra, as a retraction of the unit. -/
def toRetraction : M.Retraction A.obj :=
  ⟨A.act, A.unit⟩

theorem toRetraction_isSplit : A.toRetraction.IsSplit :=
  A.assoc

/-- **The action of an algebra of a lax idempotent 2-monad is left adjoint to the unit**, with
identity counit. -/
def adjunction (K : M.LaxIdempotent) : A.act ⊣ M.η A.obj :=
  A.toRetraction.adjunction K A.assoc

end Alg

/-- **The algebras of a lax idempotent 2-monad are the split reflections**: an algebra structure
on `x` is the same as a split retraction of `η_x` left adjoint to `η_x` with identity counit. -/
def LaxIdempotent.algEquiv (K : M.LaxIdempotent) : M.Alg ≃ Σ x : C, M.SplitReflection x where
  toFun A := ⟨A.obj, A.toRetraction, A.adjunction K, rfl, A.assoc⟩
  invFun s := ⟨s.1, s.2.toRetraction.act, s.2.toRetraction.unit, s.2.isSplit⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, r, adj, hε, h⟩
    obtain rfl : adj = r.adjunction K h :=
      Bicategory.Adjunction.ext (Adjunction.unit_eq_of_counit_eq adj (r.adjunction K h) hε) hε
    rfl

end TwoMonad

end CategoryTheory.TwoCategory
