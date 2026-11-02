import TwoCategory.Monad.Basic

/-!
# Pseudo-algebras of a 2-monad

A *pseudo-algebra* of a 2-monad `M = (T, η, μ)` is an object `x` with an action `a : T x ⟶ x`
satisfying the unit and associativity laws of an algebra up to invertible 2-cells
`ζ : η_x ≫ a ≅ 𝟙` and `α : μ_x ≫ a ≅ T a ≫ a`, subject to coherence laws: the two unit laws
```
  η_{T x} ◁ α ≫ a ◁ ζ = 𝟙 a        T η_x ◁ α ≫ T ζ ▷ a = 𝟙 a
```
and the associativity law, between 2-cells `μ_{T x} ≫ μ_x ≫ a ⟶ T (T a) ≫ T a ≫ a`,
```
  μ_{T x} ◁ α ≫ T (T a) ◁ α = T μ_x ◁ α ≫ T α ▷ a
```
It is *normal* if `ζ` is the identity, that is the action is a retraction of the unit
(`Retraction`) and `α` restricts to identities along `η_{T x}` and `T η_x`. A strict algebra is a
normal pseudo-algebra whose `α` is the identity.

The associativity law of `M` is a rule here, so the two sides of the associativity law of a
pseudo-algebra have the same type: they end at `T (T a) ≫ T a ≫ a`, and start at
`μ_{T x} ≫ μ_x ≫ a` and `T μ_x ≫ μ_x ≫ a`. So are the unit and associativity laws whiskered, and
mapped by `T`, which make the rules confluent.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {C : Type u} [TwoCategory.{w, v} C]

/-! ## The laws of a 2-monad, whiskered and mapped by `T` -/

namespace PreTwoMonad

variable (M : PreTwoMonad C)

attribute [rewrite_rule] PreTwoMonad.assoc

@[rewrite_rule]
theorem assoc_assoc {x z : C} (k : M.T.obj x ⟶ z) :
    M.μ (M.T.obj x) ≫ M.μ x ≫ k = M.T.map (M.μ x) ≫ M.μ x ≫ k :=
  congrArg (· ≫ k) (M.assoc x)

@[rewrite_rule]
theorem whiskerLeft_assoc {x z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.μ (M.T.obj x) ◁ M.μ x ◁ β = M.T.map (M.μ x) ◁ M.μ x ◁ β :=
  eq_of_heq (whiskerLeft_congr (M.assoc x) β)

@[rewrite_rule]
theorem whiskerRight_assoc {w x : C} {u u' : w ⟶ M.T.obj (M.T.obj (M.T.obj x))} (β : u ⟶ u') :
    β ▷ M.μ (M.T.obj x) ▷ M.μ x = β ▷ M.T.map (M.μ x) ▷ M.μ x :=
  eq_of_heq (whiskerRight_congr β (M.assoc x))

@[rewrite_rule]
theorem whiskerLeft_unit_left {x z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.η (M.T.obj x) ◁ M.μ x ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.unit_left x) β)

@[rewrite_rule]
theorem whiskerLeft_unit_right {x z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.T.map (M.η x) ◁ M.μ x ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.unit_right x) β)

@[rewrite_rule]
theorem whiskerRight_unit_left {w x : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.η (M.T.obj x) ▷ M.μ x = β :=
  eq_of_heq (whiskerRight_congr β (M.unit_left x))

@[rewrite_rule]
theorem whiskerRight_unit_right {w x : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.T.map (M.η x) ▷ M.μ x = β :=
  eq_of_heq (whiskerRight_congr β (M.unit_right x))

/-- The unit law `η_{T x} ≫ μ_x = 𝟙`, mapped by `T`. -/
@[rewrite_rule]
theorem map_unit_left (x : C) : M.T.map (M.η (M.T.obj x)) ≫ M.T.map (M.μ x) = 𝟙 _ := by
  kernel_exact congrArg M.T.map (M.unit_left x)

/-- The unit law `T η_x ≫ μ_x = 𝟙`, mapped by `T`. -/
@[rewrite_rule]
theorem map_unit_right (x : C) : M.T.map (M.T.map (M.η x)) ≫ M.T.map (M.μ x) = 𝟙 _ := by
  kernel_exact congrArg M.T.map (M.unit_right x)

@[rewrite_rule]
theorem map_unit_left_assoc {x z : C} (k : M.T.obj (M.T.obj x) ⟶ z) :
    M.T.map (M.η (M.T.obj x)) ≫ M.T.map (M.μ x) ≫ k = k :=
  congrArg (· ≫ k) (M.map_unit_left x)

@[rewrite_rule]
theorem map_unit_right_assoc {x z : C} (k : M.T.obj (M.T.obj x) ⟶ z) :
    M.T.map (M.T.map (M.η x)) ≫ M.T.map (M.μ x) ≫ k = k :=
  congrArg (· ≫ k) (M.map_unit_right x)

@[rewrite_rule]
theorem whiskerLeft_map_unit_left {x z : C} {k k' : M.T.obj (M.T.obj x) ⟶ z} (β : k ⟶ k') :
    M.T.map (M.η (M.T.obj x)) ◁ M.T.map (M.μ x) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.map_unit_left x) β)

@[rewrite_rule]
theorem whiskerLeft_map_unit_right {x z : C} {k k' : M.T.obj (M.T.obj x) ⟶ z} (β : k ⟶ k') :
    M.T.map (M.T.map (M.η x)) ◁ M.T.map (M.μ x) ◁ β = β :=
  eq_of_heq (whiskerLeft_congr (M.map_unit_right x) β)

@[rewrite_rule]
theorem whiskerRight_map_unit_left {w x : C} {u u' : w ⟶ M.T.obj (M.T.obj x)} (β : u ⟶ u') :
    β ▷ M.T.map (M.η (M.T.obj x)) ▷ M.T.map (M.μ x) = β :=
  eq_of_heq (whiskerRight_congr β (M.map_unit_left x))

@[rewrite_rule]
theorem whiskerRight_map_unit_right {w x : C} {u u' : w ⟶ M.T.obj (M.T.obj x)} (β : u ⟶ u') :
    β ▷ M.T.map (M.T.map (M.η x)) ▷ M.T.map (M.μ x) = β :=
  eq_of_heq (whiskerRight_congr β (M.map_unit_right x))

end PreTwoMonad

namespace TwoMonad

variable (M : TwoMonad C)

/-! ## Retractions of units -/

variable {M} in
/-- A retraction of the unit `η_x`: a 1-cell `a : T x ⟶ x` with `η_x ≫ a = 𝟙` (the unit law of an
algebra). -/
structure Retraction (x : C) where
  /-- The retraction `a`. -/
  act : M.T.obj x ⟶ x
  unit : M.η x ≫ act = 𝟙 x

namespace Retraction

variable {M} {x : C} (r : M.Retraction x)

/-! The unit law is a rule, stated with the unit and the 2-functor of the underlying
`PreTwoMonad`: the rules of 2-monads produce these, and a rule stated with the abbreviations `M.η`
and `M.T` would not match them, while rules stated with these also match the abbreviations. So
are its whiskered forms, and its image by `T`. -/

@[rewrite_rule]
theorem unit' : M.toPreTwoMonad.η x ≫ r.act = 𝟙 x :=
  r.unit

@[rewrite_rule]
theorem unit_assoc {z : C} (k : x ⟶ z) : M.toPreTwoMonad.η x ≫ r.act ≫ k = k :=
  congrArg (· ≫ k) r.unit

@[rewrite_rule]
theorem whiskerLeft_unit {z : C} {k k' : x ⟶ z} (β : k ⟶ k') :
    M.toPreTwoMonad.η x ◁ r.act ◁ β = β :=
  eq_of_heq (whiskerLeft_congr r.unit β)

@[rewrite_rule]
theorem whiskerRight_unit {w : C} {u u' : w ⟶ x} (β : u ⟶ u') :
    β ▷ M.toPreTwoMonad.η x ▷ r.act = β :=
  eq_of_heq (whiskerRight_congr β r.unit)

/-- The unit law, mapped by `T`. -/
@[rewrite_rule]
theorem map_unit :
    M.toPreTwoMonad.T.map (M.toPreTwoMonad.η x) ≫ M.toPreTwoMonad.T.map r.act =
      𝟙 (M.T.obj x) := by
  kernel_exact congrArg M.T.map r.unit

@[rewrite_rule]
theorem map_unit_assoc {z : C} (k : M.T.obj x ⟶ z) :
    M.toPreTwoMonad.T.map (M.toPreTwoMonad.η x) ≫ M.toPreTwoMonad.T.map r.act ≫ k = k :=
  congrArg (· ≫ k) r.map_unit

@[rewrite_rule]
theorem whiskerLeft_map_unit {z : C} {k k' : M.T.obj x ⟶ z} (β : k ⟶ k') :
    M.toPreTwoMonad.T.map (M.toPreTwoMonad.η x) ◁ M.toPreTwoMonad.T.map r.act ◁ β = β :=
  eq_of_heq (whiskerLeft_congr r.map_unit β)

@[rewrite_rule]
theorem whiskerRight_map_unit {w : C} {u u' : w ⟶ M.T.obj x} (β : u ⟶ u') :
    β ▷ M.toPreTwoMonad.T.map (M.toPreTwoMonad.η x) ▷ M.toPreTwoMonad.T.map r.act = β :=
  eq_of_heq (whiskerRight_congr β r.map_unit)

/-- The retraction is split: the associativity law of an algebra. -/
def IsSplit : Prop :=
  M.μ x ≫ r.act = M.T.map r.act ≫ r.act

end Retraction

/-! ## Pseudo-algebras -/

/-- A pseudo-algebra of a 2-monad: an object `x` with an action `a : T x ⟶ x` satisfying the unit
and associativity laws up to invertible 2-cells `ζ : η_x ≫ a ≅ 𝟙` and `α : μ_x ≫ a ≅ T a ≫ a`,
which satisfy two unit laws and an associativity law. -/
structure PseudoAlg where
  /-- The underlying object. -/
  obj : C
  /-- The action. -/
  act : M.T.obj obj ⟶ obj
  /-- The unit 2-cell `ζ : η_x ≫ a ≅ 𝟙`. -/
  unitIso : M.η obj ≫ act ≅ 𝟙 obj
  /-- The associativity 2-cell `α : μ_x ≫ a ≅ T a ≫ a`. -/
  assocIso : M.μ obj ≫ act ≅ M.T.map act ≫ act
  unit_left : M.η (M.T.obj obj) ◁ assocIso.hom ≫ act ◁ unitIso.hom = 𝟙 act
  unit_right : M.T.map (M.η obj) ◁ assocIso.hom ≫ M.T.map₂ unitIso.hom ▷ act = 𝟙 act
  assoc : M.μ (M.T.obj obj) ◁ assocIso.hom ≫ M.T.map (M.T.map act) ◁ assocIso.hom =
    M.T.map (M.μ obj) ◁ assocIso.hom ≫ M.T.map₂ assocIso.hom ▷ act

/-- A normal pseudo-algebra of a 2-monad: a pseudo-algebra whose unit 2-cell is the identity, so
its action is a retraction of the unit. -/
structure NormalPseudoAlg where
  /-- The underlying object. -/
  obj : C
  /-- The action, a retraction of `η_x`. -/
  toRetraction : M.Retraction obj
  /-- The associativity 2-cell `α : μ_x ≫ a ≅ T a ≫ a`. -/
  assocIso : M.μ obj ≫ toRetraction.act ≅ M.T.map toRetraction.act ≫ toRetraction.act
  unit_left : M.η (M.T.obj obj) ◁ assocIso.hom = 𝟙 toRetraction.act
  unit_right : M.T.map (M.η obj) ◁ assocIso.hom = 𝟙 toRetraction.act
  assoc : M.μ (M.T.obj obj) ◁ assocIso.hom ≫ M.T.map (M.T.map toRetraction.act) ◁ assocIso.hom =
    M.T.map (M.μ obj) ◁ assocIso.hom ≫ M.T.map₂ assocIso.hom ▷ toRetraction.act

variable {M}

/-- A normal pseudo-algebra is a pseudo-algebra. -/
def NormalPseudoAlg.toPseudoAlg (A : M.NormalPseudoAlg) : M.PseudoAlg where
  obj := A.obj
  act := A.toRetraction.act
  unitIso := Iso.refl (𝟙 A.obj)
  assocIso := A.assocIso
  unit_left := by kernel_exact A.unit_left
  unit_right := by kernel_exact A.unit_right
  assoc := A.assoc

end TwoMonad

end CategoryTheory.TwoCategory
