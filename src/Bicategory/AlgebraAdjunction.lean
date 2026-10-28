import Bicategory.AlgebraicFactorization
import Bicategory.Slice
import Bicategory.LaxIdempotent

/-!
# `R` is lax idempotent; `R`-algebras are split reflections of `Lf` over the codomain

Let `f : A ⟶ B` be a 1-cell of a 2-category with comma objects, factored as `f = Lf ≫ Rf` through
`f/B` (`Bicategory.Factorization`).

## `R` is lax idempotent

The 2-monad `R` is lax idempotent (`rLaxIdempotent`, see `Bicategory.LaxIdempotent`), with
`δ_f = (ζ_f, 𝟙) : R(η_f) ⟶ η_{Rf}`. Here `R(η_f) = (j_f, 𝟙)` where `j_f : f/B ⟶ Rf/B` is induced
by the cone `(q_f ≫ Lf, Rf, ν_f)`, and `ζ_f : j_f ⟶ L(Rf)` is induced by the 2-cells
`τ_f : q_f ≫ Lf ⟶ 𝟙` and `𝟙 Rf`. The laws of `δ` reduce, by the universal property of `Rf/B`, to
the naturality of `τ` and `Lf ◁ τ_f = 𝟙`. So the strict `R`-algebras are the split reflections
of the units `(Lf, 𝟙)` in `Arr B` (`rAlgEquiv`).

## In the slice over the codomain

In the strict slice 2-category over `B`, `Lf` is a 1-cell from `f` to `Rf`. An `R`-algebra
structure on `f` is the same as (`ralgEquiv : RAlg B ≃ Σ f : Arr B, f.SplitReflection`):

* a 1-cell `a : f/B ⟶ A` over `B`, that is with `a ≫ f = Rf`;
* left adjoint to `Lf` in the slice over `B`, with the identity as counit, so `Lf ≫ a = 𝟙 A`;
* and *split*: `π_f ≫ a = commaMap (a, 𝟙) ≫ a`, where `π_f : Rf/B ⟶ f/B` is composition.

The adjunction is the restriction to the slice of the adjunction `(a, 𝟙) ⊣ (Lf, 𝟙)` in `Arr B`
given by lax idempotence: its unit `δ_f ▷ R(a, 𝟙)` has identity codomain component. It is
determined by its counit (`Adjunction.unit_eq_of_counit_eq`).

The splitting condition is the associativity of the algebra and is not implied by the adjunction:
in `Cat`, a left adjoint of `Lf` over `B` with identity counit is a normal cleavage of an
opfibration, which need not be split.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] [HasCommas B]

open HasCommas Arr

namespace Arr

variable (f : Arr B)

/-! ## `Lf` in the slice over the codomain -/

/-- `f` as an object of the slice over its codomain. -/
abbrev toSlice : Slice f.cod :=
  ⟨f.dom, f.hom⟩

/-- `Rf` as an object of the slice over the codomain of `f`. -/
abbrev commaSlice : Slice f.cod :=
  ⟨f.commaObj, (commaCone f.hom (𝟙 f.cod)).right⟩

/-- `Lf` as a 1-cell of the slice over the codomain of `f`. -/
def lSlice : f.toSlice ⟶ f.commaSlice :=
  ⟨f.lMap, rfl⟩

@[rewrite_rule] theorem lSlice_hom : f.lSlice.hom = f.lMap := rfl

/-! ## The 2-cell `ζ_f`

Several equations below are rules only to make the rules confluent: they equate the different
normal forms of a composite, reached by different rules. -/

/-- The 1-cell `j_f : f/B ⟶ Rf/B` induced by the cone `(q_f ≫ Lf, Rf, ν_f)`. -/
def unitMap : f.commaObj ⟶ (R.obj f).commaObj :=
  (isComma (R.obj f).hom (𝟙 f.cod)).lift
    ⟨(commaCone f.hom (𝟙 f.cod)).left ≫ f.lMap, (commaCone f.hom (𝟙 f.cod)).right,
      (commaCone f.hom (𝟙 f.cod)).hom⟩

/-- The 2-cell `ζ_f : j_f ⟶ L(Rf)` of `Rf/B`, induced by `τ_f` and the identity of `Rf`. -/
def unitCell : f.unitMap ⟶ (R.obj f).lMap :=
  (isComma (R.obj f).hom (𝟙 f.cod)).lift₂
    (CommaCone.homMk f.counitCell (𝟙 (commaCone f.hom (𝟙 f.cod)).right) (by kernel_rfl))

@[rewrite_rule]
theorem unitCell_whiskerRight_left :
    f.unitCell ▷ (commaCone (R.obj f).hom (𝟙 f.cod)).left = f.counitCell := by
  kernel_rfl

@[rewrite_rule]
theorem unitCell_whiskerRight_right :
    f.unitCell ▷ (commaCone (R.obj f).hom (𝟙 f.cod)).right =
      𝟙 (commaCone f.hom (𝟙 f.cod)).right := by
  kernel_rfl

/-- `j_f` is a section of the composition `π_f`. -/
@[rewrite_rule]
theorem unitMap_comp_compMap : f.unitMap ≫ f.compMap = 𝟙 f.commaObj := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem unitMap_comp_compMap_assoc {z : B} (k : f.commaObj ⟶ z) :
    f.unitMap ≫ f.compMap ≫ k = k :=
  congrArg (· ≫ k) f.unitMap_comp_compMap

/-- `L(Rf)` is a section of the composition `π_f`: the left unit law of `R`. -/
@[rewrite_rule]
theorem lMap_comp_compMap : (R.obj f).lMap ≫ f.compMap = 𝟙 f.commaObj := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem lMap_comp_compMap_assoc {z : B} (k : f.commaObj ⟶ z) :
    (R.obj f).lMap ≫ f.compMap ≫ k = k :=
  congrArg (· ≫ k) f.lMap_comp_compMap

/-- `ζ_f` is sent to the identity by the composition `π_f`. -/
theorem unitCell_whiskerRight_compMap : f.unitCell ▷ f.compMap = 𝟙 (𝟙 f.commaObj) := by
  comma_ext₂ <;> kernel_rfl

/-- `Lf` whiskered with `τ_f` is the identity, in the normal form of whiskerings. -/
@[rewrite_rule]
theorem lMap_whiskerLeft_counitCell_whiskerRight {z : B} (k : f.commaObj ⟶ z) :
    f.lMap ◁ f.counitCell ▷ k = 𝟙 (f.lMap ≫ k) := by
  kernel_exact congrArg (· ▷ k) f.lMap_whiskerLeft_counitCell

/-- Whiskering with `commaMap m` and the legs of comma objects, from the universal property. -/
@[rewrite_rule]
theorem whiskerRight_commaMap_left {f g : Arr B} (m : f ⟶ g) {x : B} {u v : x ⟶ f.commaObj}
    (θ : u ⟶ v) : θ ▷ commaMap m ▷ (commaCone g.hom (𝟙 g.cod)).left =
      θ ▷ (commaCone f.hom (𝟙 f.cod)).left ▷ m.left := by
  kernel_rfl

@[rewrite_rule]
theorem whiskerRight_commaMap_right {f g : Arr B} (m : f ⟶ g) {x : B} {u v : x ⟶ f.commaObj}
    (θ : u ⟶ v) : θ ▷ commaMap m ▷ (commaCone g.hom (𝟙 g.cod)).right =
      θ ▷ (commaCone f.hom (𝟙 f.cod)).right ▷ m.right := by
  kernel_rfl

/-! ## `R` is lax idempotent -/

/-- `R` applied to the unit `(Lf, 𝟙)` is `j_f`. -/
@[rewrite_rule]
theorem commaMap_rMonad_η : commaMap (rMonad.η f) = f.unitMap := by
  comma_ext; kernel_rfl

/-- `j` is natural: `R` applied to the naturality of `η`. -/
@[rewrite_rule]
theorem unitMap_naturality {g : Arr B} (m : f ⟶ g) :
    f.unitMap ≫ commaMap (R.map m) = commaMap m ≫ g.unitMap := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem unitMap_naturality_assoc {g : Arr B} (m : f ⟶ g) {z : B}
    (k : (R.obj g).commaObj ⟶ z) :
    f.unitMap ≫ commaMap (R.map m) ≫ k = commaMap m ≫ g.unitMap ≫ k := by
  kernel_exact congrArg (· ≫ k) (f.unitMap_naturality m)

/-- `Lf ≫ L(Rf) = Lf ≫ j_f`: the naturality of `η` at `η_f`, which the naturality rule of `L` does
not find as `Lf` is not a projection. -/
@[rewrite_rule]
theorem lMap_comp_lMap : f.lMap ≫ (R.obj f).lMap = f.lMap ≫ f.unitMap := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem lMap_comp_lMap_assoc {z : B} (k : (R.obj f).commaObj ⟶ z) :
    f.lMap ≫ (R.obj f).lMap ≫ k = f.lMap ≫ f.unitMap ≫ k := by
  kernel_exact congrArg (· ≫ k) f.lMap_comp_lMap

/-- The naturality of `L` at `R.map m`, whose left side is `commaMap m`: the matcher does not see
it as the projection `(R.map m).left`. -/
@[rewrite_rule]
theorem commaMap_comp_lMap {g : Arr B} (m : f ⟶ g) :
    commaMap m ≫ (R.obj g).lMap = (R.obj f).lMap ≫ commaMap (R.map m) :=
  lMap_naturality (R.map m)

@[rewrite_rule]
theorem commaMap_comp_lMap_assoc {g : Arr B} (m : f ⟶ g) {z : B}
    (k : (R.obj g).commaObj ⟶ z) :
    commaMap m ≫ (R.obj g).lMap ≫ k = (R.obj f).lMap ≫ commaMap (R.map m) ≫ k := by
  kernel_exact congrArg (· ≫ k) (f.commaMap_comp_lMap m)

/-- `ζ` is natural. -/
theorem unitCell_naturality {g : Arr B} (m : f ⟶ g) :
    f.unitCell ▷ commaMap (R.map m) = commaMap m ◁ g.unitCell := by
  comma_ext₂ <;> kernel_rfl

/-- `Lf ◁ ζ_f` is the identity. -/
theorem lMap_whiskerLeft_unitCell : f.lMap ◁ f.unitCell = 𝟙 (f.lMap ≫ f.unitMap) := by
  comma_ext₂ <;> kernel_rfl

end Arr

/-- **`R` is lax idempotent**, with `δ_f = (ζ_f, 𝟙) : R(η_f) ⟶ η_{Rf}`. -/
def rLaxIdempotent : (rMonad (B := B)).LaxIdempotent where
  δ f := ⟨f.unitCell, 𝟙 (𝟙 f.cod), by kernel_rfl⟩
  δ_naturality {x _} m := Arr.Hom₂.ext (by kernel_exact x.unitCell_naturality m) (by kernel_rfl)
  δ_whiskerRight_μ f := Arr.Hom₂.ext (by kernel_exact f.unitCell_whiskerRight_compMap)
    (by kernel_rfl)
  η_whiskerLeft_δ f := Arr.Hom₂.ext (by kernel_exact f.lMap_whiskerLeft_unitCell) (by kernel_rfl)

/-- The strict `R`-algebras are the split reflections of the units `(Lf, 𝟙) : f ⟶ Rf` in `Arr B`,
by lax idempotence. -/
def rAlgEquiv : RAlg B ≃ Σ f : Arr B, (rMonad (B := B)).SplitReflection f :=
  rLaxIdempotent.algEquiv

namespace Arr

variable (f : Arr B)

/-! ## Retractions of `Lf` over the codomain -/

/-- A retraction of `Lf` over the codomain of `f`: a square `(a, 𝟙) : Rf ⟶ f` with
`Lf ≫ a = 𝟙`. These are the actions satisfying the unit law of an `R`-algebra. -/
structure LRetraction where
  /-- The square `(a, 𝟙) : Rf ⟶ f`. -/
  act : R.obj f ⟶ f
  act_right : act.right = 𝟙 f.cod
  lMap_comp_act_left : f.lMap ≫ act.left = 𝟙 f.dom

attribute [rewrite_rule] LRetraction.act_right LRetraction.lMap_comp_act_left

namespace LRetraction

variable {f} (r : f.LRetraction)

@[rewrite_rule]
theorem lMap_comp_act_left_assoc {z : B} (k : f.dom ⟶ z) : f.lMap ≫ r.act.left ≫ k = k := by
  kernel_exact congrArg (· ≫ k) r.lMap_comp_act_left

/-- `Lf ≫ a ≫ Lf = Lf`, in the normal form of `a ≫ Lf` given by the naturality of `L`. -/
@[rewrite_rule]
theorem lMap_comp_lMap_comp_commaMap_act :
    f.lMap ≫ (R.obj f).lMap ≫ commaMap r.act = f.lMap := by
  comma_ext; kernel_rfl

/-- `a ≫ Lf ≫ a = a`, in the normal form of `a ≫ Lf` given by the naturality of `L`. -/
@[rewrite_rule]
theorem lMap_comp_commaMap_act_comp_act_left :
    (R.obj f).lMap ≫ commaMap r.act ≫ r.act.left = r.act.left :=
  (lMap_naturality_assoc r.act r.act.left).symm.trans
    (congrArg (r.act.left ≫ ·) r.lMap_comp_act_left)

/-- `j_f` is a section of `commaMap (a, 𝟙)`. -/
@[rewrite_rule]
theorem unitMap_comp_commaMap_act : f.unitMap ≫ commaMap r.act = 𝟙 f.commaObj := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem unitMap_comp_commaMap_act_assoc {z : B} (k : f.commaObj ⟶ z) :
    f.unitMap ≫ commaMap r.act ≫ k = k :=
  congrArg (· ≫ k) r.unitMap_comp_commaMap_act

/-- The retraction as a 1-cell `a : Rf ⟶ f` of the slice over the codomain of `f`. -/
def toSlice : f.commaSlice ⟶ f.toSlice :=
  ⟨r.act.left, by kernel_rfl⟩

@[rewrite_rule] theorem toSlice_hom : r.toSlice.hom = r.act.left := rfl

/-- The 1-cell `a` is split: it is compatible with the composition `π_f`. This is the
associativity of the corresponding `R`-algebra. -/
def IsSplit : Prop :=
  rMonad.μ f ≫ r.act = R.map r.act ≫ r.act

/-- The unit `ζ_f ▷ commaMap (a, 𝟙) : 𝟙 ⟶ a ≫ Lf` of the adjunction, in the slice. -/
def unit : 𝟙 f.commaSlice ⟶ r.toSlice ≫ f.lSlice :=
  ⟨f.unitCell ▷ commaMap r.act, by kernel_rfl⟩

@[rewrite_rule] theorem unit_hom : r.unit.hom = f.unitCell ▷ commaMap r.act := rfl

/-- The retraction, as a retraction of the unit `(Lf, 𝟙)` of `R`. -/
def toRetraction : (rMonad (B := B)).Retraction f :=
  ⟨r.act, Arr.Hom.ext (by kernel_rfl) (by kernel_rfl)⟩

/-- The triangle law involving `a`, restricted from the adjunction `(a, 𝟙) ⊣ (Lf, 𝟙)` in `Arr B`
given by lax idempotence. -/
theorem left_triangle (h : r.IsSplit) :
    leftZigzag r.unit (𝟙 (f.lSlice ≫ r.toSlice)) = (λ_ r.toSlice).hom ≫ (ρ_ r.toSlice).inv :=
  Slice.hom₂_ext (by
    kernel_exact congrArg Arr.Hom₂.left (r.toRetraction.adjUnit_whiskerRight rLaxIdempotent h))

/-- The triangle law involving `Lf`, restricted from `Arr B`. -/
theorem right_triangle :
    rightZigzag r.unit (𝟙 (f.lSlice ≫ r.toSlice)) = (ρ_ f.lSlice).hom ≫ (λ_ f.lSlice).inv :=
  Slice.hom₂_ext (by
    kernel_exact congrArg Arr.Hom₂.left (r.toRetraction.η_whiskerLeft_adjUnit rLaxIdempotent))

/-- A split retraction `a` of `Lf` over the codomain is left adjoint to `Lf` in the slice, with
identity counit. -/
def adjunction (h : r.IsSplit) : r.toSlice ⊣ f.lSlice where
  unit := r.unit
  counit := 𝟙 _
  left_triangle := r.left_triangle h
  right_triangle := r.right_triangle

end LRetraction

/-! ## Split reflections -/

/-- A split reflection of `Lf` over the codomain of `f`: a split retraction `a` of `Lf` over the
codomain that is left adjoint to `Lf` in the slice, with identity counit. -/
structure SplitReflection where
  /-- The retraction `a`. -/
  toLRetraction : f.LRetraction
  /-- The adjunction `a ⊣ Lf` in the slice. -/
  adj : toLRetraction.toSlice ⊣ f.lSlice
  counit_eq : adj.counit = 𝟙 _
  isSplit : toLRetraction.IsSplit

end Arr

/-- **`R`-algebras are split reflections over the codomain**: an `R`-algebra structure on `f` is
the same as a left adjoint `a` to `Lf` in the slice over the codomain of `f`, with identity
counit, that is split. -/
def ralgEquiv : RAlg B ≃ Σ f : Arr B, f.SplitReflection where
  toFun A :=
    let r : A.obj.LRetraction :=
      ⟨A.act, by kernel_exact congrArg Arr.Hom.right A.unit,
        by kernel_exact congrArg Arr.Hom.left A.unit⟩
    ⟨A.obj, r, r.adjunction A.assoc, rfl, A.assoc⟩
  invFun s := ⟨s.1, s.2.toLRetraction.act, Arr.Hom.ext (by kernel_rfl) (by kernel_rfl),
    s.2.isSplit⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨f, r, adj, hε, h⟩
    obtain rfl : adj = r.adjunction h :=
      Bicategory.Adjunction.ext
        (Adjunction.unit_eq_of_counit_eq adj (r.adjunction h) hε) hε
    rfl

end CategoryTheory.TwoCategory
