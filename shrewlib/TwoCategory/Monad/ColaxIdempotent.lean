import TwoCategory.Monad.Basic
import TwoCategory.Adjunction

/-!
# Colax idempotent 2-comonads

The dual of lax idempotent 2-monads (`TwoCategory.Monad.LaxIdempotent`), reversing the 1-cells:
a 2-comonad `M = (T, ε, δ)` on a 2-category `C` is *colax idempotent* if it comes with a
modification `θ : Tε ⟶ εT`, that is 2-cells `θ x : T ε_x ⟶ ε_{T x}` natural in `x`, with
```
  δ x ◁ θ x = 𝟙 (𝟙 (T x))        θ x ▷ ε x = 𝟙 (ε_{T x} ≫ ε_x)
```
The types of these equations agree by the counit laws of `M` and the naturality of `ε`, which are
rules from the start of this file. Equivalently, `δ_x ⊣ T ε_x` with identity unit, and counit
`δ_{T x} ◁ T θ_x` (`ColaxIdempotent.δAdjunction`). Reversing the 1-cells exchanges the two sides
of an adjunction: `T η_x ⊣ μ_x` for a lax idempotent 2-monad becomes `δ_x ⊣ T ε_x`.

The point of colax idempotence is that coalgebra structures on `x` are right adjoint to the counit
`ε_x`: a coaction `c : x ⟶ T x` is a *coretraction* of `ε_x`, `c ≫ ε_x = 𝟙` (`Coretraction`, the
counit law of a coalgebra), and for a colax idempotent `M`

* `ε_x ⊣ c` with identity counit and unit `T c ◁ θ_x : 𝟙 ⟶ ε_x ≫ c` as soon as `c` is *split*,
  `c ≫ δ_x = c ≫ T c` (the coassociativity law; `Coretraction.adjunction`);
* so the strict coalgebras are the split right adjoint right inverses (RARIs) of the counits,
  `ε_x ⊣ c` with identity counit (`Coreflection`) and `c` split (`SplitCoreflection`):
  `ColaxIdempotent.coalgEquiv`. The adjunction is determined by its counit.

Only this strict part of `LaxIdempotent` is dualized: pseudo-coalgebras are not defined in this
library.

## The comonad laws as rules

As for 2-monads (`TwoCategory.Monad.Basic`, `TwoCategory.Monad.PseudoAlgebra`), the counit and
coassociativity laws of 2-comonads, their whiskered forms, their images by `T`, and the naturality
of `ε` mapped by `T` are rules from here on. They are declared in this file, rather than in
`Basic`, so that only the files using colax idempotence see them.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {C : Type u} [TwoCategory.{w, v} C]

/-! ## The laws of a 2-comonad, whiskered and mapped by `T` -/

namespace PreTwoComonad

variable (M : PreTwoComonad C)

attribute [rewrite_rule] PreTwoComonad.counit_left PreTwoComonad.counit_right
  PreTwoComonad.coassoc

@[rewrite_rule]
theorem counit_left_assoc {x z : C} (k : M.T.obj x ⟶ z) : M.δ x ≫ M.ε (M.T.obj x) ≫ k = k :=
  congrArg (· ≫ k) (M.counit_left x)

@[rewrite_rule]
theorem counit_right_assoc {x z : C} (k : M.T.obj x ⟶ z) : M.δ x ≫ M.T.map (M.ε x) ≫ k = k :=
  congrArg (· ≫ k) (M.counit_right x)

@[rewrite_rule]
theorem coassoc_assoc {x z : C} (k : M.T.obj (M.T.obj (M.T.obj x)) ⟶ z) :
    M.δ x ≫ M.δ (M.T.obj x) ≫ k = M.δ x ≫ M.T.map (M.δ x) ≫ k :=
  congrArg (· ≫ k) (M.coassoc x)

@[rewrite_rule]
theorem whiskerLeft_coassoc {x z : C} {k k' : M.T.obj (M.T.obj (M.T.obj x)) ⟶ z} (β : k ⟶ k') :
    M.δ x ◁ M.δ (M.T.obj x) ◁ β = M.δ x ◁ M.T.map (M.δ x) ◁ β :=
  eq_of_heq (whiskerLeft_congr (M.coassoc x) β)

@[rewrite_rule]
theorem whiskerRight_coassoc {w x : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.δ x ▷ M.δ (M.T.obj x) = β ▷ M.δ x ▷ M.T.map (M.δ x) :=
  eq_of_heq (whiskerRight_congr β (M.coassoc x))

@[rewrite_rule]
theorem whiskerLeft_counit_left {x z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.δ x ◁ M.ε (M.T.obj x) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.counit_left x) β)

@[rewrite_rule]
theorem whiskerLeft_counit_right {x z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.δ x ◁ M.T.map (M.ε x) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.counit_right x) β)

@[rewrite_rule]
theorem whiskerRight_counit_left {w x : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.δ x ▷ M.ε (M.T.obj x) = β :=
  eq_of_heq (whiskerRight_congr β (M.counit_left x))

@[rewrite_rule]
theorem whiskerRight_counit_right {w x : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.δ x ▷ M.T.map (M.ε x) = β :=
  eq_of_heq (whiskerRight_congr β (M.counit_right x))

/-- The counit law `δ_x ≫ ε_{T x} = 𝟙`, mapped by `T`. -/
@[rewrite_rule]
theorem map_counit_left (x : C) : M.T.map (M.δ x) ≫ M.T.map (M.ε (M.T.obj x)) = 𝟙 _ := by
  kernel_exact congrArg M.T.map (M.counit_left x)

/-- The counit law `δ_x ≫ T ε_x = 𝟙`, mapped by `T`. -/
@[rewrite_rule]
theorem map_counit_right (x : C) : M.T.map (M.δ x) ≫ M.T.map (M.T.map (M.ε x)) = 𝟙 _ := by
  kernel_exact congrArg M.T.map (M.counit_right x)

@[rewrite_rule]
theorem map_counit_left_assoc {x z : C} (k : M.T.obj (M.T.obj x) ⟶ z) :
    M.T.map (M.δ x) ≫ M.T.map (M.ε (M.T.obj x)) ≫ k = k :=
  congrArg (· ≫ k) (M.map_counit_left x)

@[rewrite_rule]
theorem map_counit_right_assoc {x z : C} (k : M.T.obj (M.T.obj x) ⟶ z) :
    M.T.map (M.δ x) ≫ M.T.map (M.T.map (M.ε x)) ≫ k = k :=
  congrArg (· ≫ k) (M.map_counit_right x)

@[rewrite_rule]
theorem whiskerLeft_map_counit_left {x z : C} {k k' : M.T.obj (M.T.obj x) ⟶ z} (β : k ⟶ k') :
    M.T.map (M.δ x) ◁ M.T.map (M.ε (M.T.obj x)) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.map_counit_left x) β)

@[rewrite_rule]
theorem whiskerLeft_map_counit_right {x z : C} {k k' : M.T.obj (M.T.obj x) ⟶ z} (β : k ⟶ k') :
    M.T.map (M.δ x) ◁ M.T.map (M.T.map (M.ε x)) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.map_counit_right x) β)

@[rewrite_rule]
theorem whiskerRight_map_counit_left {w x : C} {u u' : w ⟶ M.T.obj (M.T.obj x)} (β : u ⟶ u') :
    β ▷ M.T.map (M.δ x) ▷ M.T.map (M.ε (M.T.obj x)) = β :=
  eq_of_heq (whiskerRight_congr β (M.map_counit_left x))

@[rewrite_rule]
theorem whiskerRight_map_counit_right {w x : C} {u u' : w ⟶ M.T.obj (M.T.obj x)} (β : u ⟶ u') :
    β ▷ M.T.map (M.δ x) ▷ M.T.map (M.T.map (M.ε x)) = β :=
  eq_of_heq (whiskerRight_congr β (M.map_counit_right x))

/-- The naturality of `ε`, mapped by `T`: the two normal forms of `T (T m ≫ ε y)` agree. -/
@[rewrite_rule]
theorem map_ε_naturality {x y : C} (m : x ⟶ y) :
    M.T.map (M.T.map m) ≫ M.T.map (M.ε y) = M.T.map (M.ε x) ≫ M.T.map m := by
  kernel_exact congrArg M.T.map (M.ε_naturality m)

@[rewrite_rule]
theorem map_ε_naturality_assoc {x y z : C} (m : x ⟶ y) (k : M.T.obj y ⟶ z) :
    M.T.map (M.T.map m) ≫ M.T.map (M.ε y) ≫ k = M.T.map (M.ε x) ≫ M.T.map m ≫ k :=
  congrArg (· ≫ k) (M.map_ε_naturality m)

end PreTwoComonad

namespace TwoComonad

variable (M : TwoComonad C)

/-! ## Colax idempotence -/

/-- A colax idempotent 2-comonad: a modification `θ : Tε ⟶ εT` with `δ ◁ θ = 𝟙` and
`θ ▷ ε = 𝟙`. -/
structure ColaxIdempotent where
  /-- The modification `θ x : T ε_x ⟶ ε_{T x}`. -/
  θ (x : C) : M.T.map (M.ε x) ⟶ M.ε (M.T.obj x)
  θ_naturality {x y : C} (m : x ⟶ y) : M.T.map (M.T.map m) ◁ θ y = θ x ▷ M.T.map m
  δ_whiskerLeft_θ (x : C) : M.δ x ◁ θ x = 𝟙 (𝟙 (M.T.obj x))
  θ_whiskerRight_ε (x : C) : θ x ▷ M.ε x = 𝟙 (M.ε (M.T.obj x) ≫ M.ε x)

variable {M}

namespace ColaxIdempotent

variable (K : M.ColaxIdempotent)

/-! ## `δ_x ⊣ T ε_x` -/

/-- The counit `δ_{T x} ◁ T θ_x : T ε_x ≫ δ_x ⟶ 𝟙` of `δ_x ⊣ T ε_x`. -/
def δCounit (x : C) : M.T.map (M.ε x) ≫ M.δ x ⟶ 𝟙 (M.T.obj (M.T.obj x)) :=
  M.δ (M.T.obj x) ◁ M.T.map₂ (K.θ x)

/-- **`δ_x ⊣ T ε_x`**, with identity unit. -/
def δAdjunction (x : C) : M.δ x ⊣ M.T.map (M.ε x) where
  unit := 𝟙 _
  counit := K.δCounit x
  left_triangle := by
    kernel_exact congrArg (fun θ => M.δ x ◁ M.T.map₂ θ) (K.δ_whiskerLeft_θ x)
  right_triangle := by
    kernel_exact congrArg (fun θ => M.δ (M.T.obj x) ◁ M.T.map₂ θ) (K.θ_whiskerRight_ε x)

end ColaxIdempotent

/-! ## Coretractions of counits -/

/-- A coretraction of the counit `ε_x`: a 1-cell `c : x ⟶ T x` with `c ≫ ε_x = 𝟙` (the counit law
of a coalgebra). -/
structure Coretraction (x : C) where
  /-- The coretraction `c`. -/
  coact : x ⟶ M.T.obj x
  counit : coact ≫ M.ε x = 𝟙 x

namespace Coretraction

variable {x : C} (r : M.Coretraction x)

/-! The counit law is a rule, stated with the counit and the 2-functor of the underlying
`PreTwoComonad`, as for retractions of units (`TwoMonad.Retraction`). So are its whiskered forms,
and its image by `T`. -/

@[rewrite_rule]
theorem counit' : r.coact ≫ M.toPreTwoComonad.ε x = 𝟙 x :=
  r.counit

@[rewrite_rule]
theorem counit_assoc {z : C} (k : x ⟶ z) : r.coact ≫ M.toPreTwoComonad.ε x ≫ k = k :=
  congrArg (· ≫ k) r.counit

@[rewrite_rule]
theorem whiskerLeft_counit {z : C} {k k' : x ⟶ z} (β : k ⟶ k') :
    r.coact ◁ M.toPreTwoComonad.ε x ◁ β = β :=
  eq_of_heq (whiskerLeft_congr r.counit β)

@[rewrite_rule]
theorem whiskerRight_counit {w : C} {u u' : w ⟶ x} (β : u ⟶ u') :
    β ▷ r.coact ▷ M.toPreTwoComonad.ε x = β :=
  eq_of_heq (whiskerRight_congr β r.counit)

/-- The counit law, mapped by `T`. -/
@[rewrite_rule]
theorem map_counit :
    M.toPreTwoComonad.T.map r.coact ≫ M.toPreTwoComonad.T.map (M.toPreTwoComonad.ε x) =
      𝟙 (M.T.obj x) := by
  kernel_exact congrArg M.T.map r.counit

@[rewrite_rule]
theorem map_counit_assoc {z : C} (k : M.T.obj x ⟶ z) :
    M.toPreTwoComonad.T.map r.coact ≫ M.toPreTwoComonad.T.map (M.toPreTwoComonad.ε x) ≫ k = k :=
  congrArg (· ≫ k) r.map_counit

@[rewrite_rule]
theorem whiskerLeft_map_counit {z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.toPreTwoComonad.T.map r.coact ◁ M.toPreTwoComonad.T.map (M.toPreTwoComonad.ε x) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr r.map_counit β)

@[rewrite_rule]
theorem whiskerRight_map_counit {w : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.toPreTwoComonad.T.map r.coact ▷ M.toPreTwoComonad.T.map (M.toPreTwoComonad.ε x) = β :=
  eq_of_heq (whiskerRight_congr β r.map_counit)

/-- The coretraction is split: the coassociativity law of a coalgebra. -/
def IsSplit : Prop :=
  r.coact ≫ M.δ x = r.coact ≫ M.T.map r.coact

end Coretraction

/-- A right adjoint right inverse (RARI) of the counit: a coretraction `c` of `ε_x` that is right
adjoint to `ε_x` with identity counit. -/
structure Coreflection (x : C) where
  /-- The coretraction `c`. -/
  toCoretraction : M.Coretraction x
  /-- The adjunction `ε_x ⊣ c`. -/
  adj : M.ε x ⊣ toCoretraction.coact
  counit_eq : adj.counit = 𝟙 _

/-! ## Strict coalgebras are split right adjoint right inverses of counits -/

namespace Coretraction

variable {x : C} (r : M.Coretraction x) (K : M.ColaxIdempotent)

/-- The unit `T c ◁ θ x : 𝟙 ⟶ ε_x ≫ c` of the adjunction `ε_x ⊣ c`. -/
def adjUnit : 𝟙 (M.T.obj x) ⟶ M.ε x ≫ r.coact :=
  M.T.map r.coact ◁ K.θ x

/-- The triangle law involving `ε_x`, which holds for every coretraction. -/
theorem adjUnit_whiskerRight : r.adjUnit K ▷ M.ε x = 𝟙 (M.ε x) := by
  kernel_exact congrArg (M.T.map r.coact ◁ ·) (K.θ_whiskerRight_ε x)

/-- The triangle law involving `c`, which holds when `c` is split: `c ≫ T c = c ≫ δ_x`, and
`δ_x ◁ θ x` is the identity. -/
theorem whiskerLeft_adjUnit (h : r.IsSplit) :
    (r.coact ≫ M.T.map r.coact) ◁ K.θ x = 𝟙 r.coact := by
  have h' : (r.coact ≫ M.δ x) ◁ K.θ x = 𝟙 r.coact := by
    kernel_exact congrArg (r.coact ◁ ·) (K.δ_whiskerLeft_θ x)
  exact eq_of_heq ((whiskerLeft_congr h.symm (K.θ x)).trans (heq_of_eq h'))

/-- The triangle law involving `ε_x`, in the form of Mathlib's adjunctions. -/
theorem left_triangle :
    leftZigzag (r.adjUnit K) (𝟙 (r.coact ≫ M.ε x)) = (λ_ (M.ε x)).hom ≫ (ρ_ (M.ε x)).inv := by
  kernel_exact r.adjUnit_whiskerRight K

/-- The triangle law involving `c`, in the form of Mathlib's adjunctions. -/
theorem right_triangle (h : r.IsSplit) :
    rightZigzag (r.adjUnit K) (𝟙 (r.coact ≫ M.ε x)) = (ρ_ r.coact).hom ≫ (λ_ r.coact).inv := by
  kernel_exact r.whiskerLeft_adjUnit K h

/-- For a colax idempotent 2-comonad, a split coretraction `c` of `ε_x` is right adjoint to `ε_x`,
with identity counit. -/
def adjunction (h : r.IsSplit) : M.ε x ⊣ r.coact where
  unit := r.adjUnit K
  counit := 𝟙 _
  left_triangle := r.left_triangle K
  right_triangle := r.right_triangle K h

end Coretraction

variable (M) in
/-- A split RARI of the counit: a RARI `c` of `ε_x` that is split, `c ≫ δ_x = c ≫ T c`. -/
structure SplitCoreflection (x : C) extends M.Coreflection x where
  isSplit : toCoretraction.IsSplit

namespace Coalg

variable (A : M.Coalg)

/-- The coaction of a coalgebra, as a coretraction of the counit. -/
def toCoretraction : M.Coretraction A.obj :=
  ⟨A.coact, A.counit⟩

/-- The coaction of a coalgebra is split, by the coassociativity law. -/
theorem toCoretraction_isSplit : A.toCoretraction.IsSplit :=
  A.coassoc

/-- **The coaction of a coalgebra of a colax idempotent 2-comonad is right adjoint to the
counit**, with identity counit. -/
def adjunction (K : M.ColaxIdempotent) : M.ε A.obj ⊣ A.coact :=
  A.toCoretraction.adjunction K A.coassoc

end Coalg

/-- **The coalgebras of a colax idempotent 2-comonad are the split RARIs**: a coalgebra structure
on `x` is the same as a split coretraction of `ε_x` right adjoint to `ε_x` with identity
counit. -/
def ColaxIdempotent.coalgEquiv (K : M.ColaxIdempotent) :
    M.Coalg ≃ Σ x : C, M.SplitCoreflection x where
  toFun A := ⟨A.obj, ⟨A.toCoretraction, A.adjunction K, rfl⟩, A.coassoc⟩
  invFun s := ⟨s.1, s.2.toCoretraction.coact, s.2.toCoretraction.counit, s.2.isSplit⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, ⟨r, adj, hε⟩, h⟩
    change r.IsSplit at h
    obtain rfl : adj = r.adjunction K h :=
      Bicategory.Adjunction.ext (Adjunction.unit_eq_of_counit_eq adj (r.adjunction K h) hε) hε
    rfl

end TwoComonad

end CategoryTheory.TwoCategory
