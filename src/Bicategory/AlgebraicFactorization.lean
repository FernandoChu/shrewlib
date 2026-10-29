import Bicategory.Factorization
import Bicategory.TwoMonad

/-!
# The comma factorization is an algebraic factorization

In a 2-category `B` with comma objects, the factorization `f = Lf ≫ Rf` through `f/B`
(`Bicategory.Factorization`) makes `R` a 2-monad and `L` a 2-comonad on the arrow 2-category
`Arr B`:

* the unit `f ⟶ Rf` is the square `(Lf, 𝟙)`, and the multiplication `R(Rf) ⟶ Rf` is the square
  `(π_f, 𝟙)`, where `π_f : Rf/B ⟶ f/B` composes the universal 2-cells of `f/B` and `Rf/B`;
* the counit `Lf ⟶ f` is the square `(𝟙, Rf)`, and the comultiplication `Lf ⟶ L(Lf)` is the square
  `(𝟙, σ_f)`, where `σ_f : f/B ⟶ Lf/(f/B)` is induced by the 2-cell `τ_f : q_f ≫ Lf ⟶ 𝟙`, itself
  induced by the 2-dimensional universal property of `f/B`.

Their (2-)naturality and the (co)monad laws are equations between 1- and 2-cells into comma
objects, which reduce by the universal property of comma objects (`comma_ext`, `comma_ext₂`) to
equations of 1- and 2-cells that hold by `rfl`, checked in the kernel. A few equations about `τ_f`
that do not follow by computation are proved first and made rules.

The 2-categories of strict algebras of `R` and coalgebras of `L` are `RAlg B` and `LCoalg B`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] [HasCommas B]

open HasCommas Arr

/-- Proves an equation of 1- or 2-cells of arrows whose components are 1- or 2-cells into comma
objects: after unfolding the given definitions and the operations of `Arr B`, it reduces by
extensionality to equations that hold by `rfl`, checked in the kernel. The unfolding is needed as
the matcher of rules does not see through these definitions. -/
macro "arr_ext" : tactic =>
  `(tactic| (intros; first
    | (apply Arr.Hom.ext <;> first | kernel_rfl | (comma_ext; kernel_rfl))
    | (apply Arr.Hom₂.ext <;> first | kernel_rfl | (comma_ext₂ <;> kernel_rfl))))

namespace Arr

variable (f : Arr B)

/-! ## The 2-monad `R` -/

/-- Composition in `f/B`: the 1-cell `π_f : Rf/B ⟶ f/B` induced by the composite of the universal
2-cells of `f/B` and `Rf/B`. -/
def compMap : (R.obj f).commaObj ⟶ f.commaObj :=
  (isComma f.hom (𝟙 f.cod)).lift
    ⟨(commaCone (R.obj f).hom (𝟙 f.cod)).left ≫ (commaCone f.hom (𝟙 f.cod)).left,
      (commaCone (R.obj f).hom (𝟙 f.cod)).right,
      (commaCone (R.obj f).hom (𝟙 f.cod)).left ◁ (commaCone f.hom (𝟙 f.cod)).hom ≫
        (commaCone (R.obj f).hom (𝟙 f.cod)).hom⟩

/-! ## The 2-comonad `L` -/

/-- The 2-cell `τ_f : q_f ≫ Lf ⟶ 𝟙` of `f/B`, induced by the 2-dimensional universal property of
`f/B` from the identity of `q_f` and the universal 2-cell `ν_f`. -/
def counitCell :
    (commaCone f.hom (𝟙 f.cod)).left ≫ f.lMap ⟶ 𝟙 f.commaObj :=
  (isComma f.hom (𝟙 f.cod)).lift₂ (u := (commaCone f.hom (𝟙 f.cod)).left ≫ f.lMap)
    (v := 𝟙 f.commaObj)
    (CommaCone.homMk (𝟙 (commaCone f.hom (𝟙 f.cod)).left) (commaCone f.hom (𝟙 f.cod)).hom
      (by kernel_rfl))

/-- `Lf` whiskered with `τ_f` is the identity. -/
@[rewrite_rule]
theorem lMap_whiskerLeft_counitCell : f.lMap ◁ f.counitCell = 𝟙 f.lMap := by
  comma_ext₂ <;> kernel_rfl

/-- `Lf` whiskered with `τ_f` is the identity, in the normal form of whiskerings. -/
@[rewrite_rule]
theorem lMap_whiskerLeft_counitCell_whiskerRight {z : B} (k : f.commaObj ⟶ z) :
    f.lMap ◁ f.counitCell ▷ k = 𝟙 (f.lMap ≫ k) := by
  kernel_exact congrArg (· ▷ k) f.lMap_whiskerLeft_counitCell

/-- `Lf` is natural in squares: the equation of the square `L.map m`, in the form in which it
appears in composites. -/
@[rewrite_rule]
theorem lMap_naturality {f g : Arr B} (m : f ⟶ g) : m.left ≫ g.lMap = f.lMap ≫ commaMap m := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem lMap_naturality_assoc {f g : Arr B} (m : f ⟶ g) {z : B} (k : g.commaObj ⟶ z) :
    m.left ≫ g.lMap ≫ k = f.lMap ≫ commaMap m ≫ k :=
  congrArg (· ≫ k) (lMap_naturality m)

@[rewrite_rule]
theorem lMap_naturality_whiskerLeft {f g : Arr B} (m : f ⟶ g) {z : B} {k k' : g.commaObj ⟶ z}
    (η : k ⟶ k') : m.left ◁ g.lMap ◁ η = f.lMap ◁ commaMap m ◁ η :=
  eq_of_heq (whiskerLeft_congr (lMap_naturality m) η)

@[rewrite_rule]
theorem lMap_naturality_whiskerRight {f g : Arr B} (m : f ⟶ g) {z : B} {u u' : z ⟶ f.dom}
    (θ : u ⟶ u') : θ ▷ m.left ▷ g.lMap = θ ▷ f.lMap ▷ commaMap m :=
  eq_of_heq (whiskerRight_congr θ (lMap_naturality m))

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

/-- `τ` is natural in squares. -/
@[rewrite_rule]
theorem commaMap_whiskerLeft_counitCell {f g : Arr B} (m : f ⟶ g) :
    commaMap m ◁ g.counitCell = f.counitCell ▷ commaMap m := by
  comma_ext₂ <;> kernel_rfl

/-- The 1-cell `σ_f : f/B ⟶ Lf/(f/B)` induced by `τ_f`. -/
def coassocMap : f.commaObj ⟶ (L.obj f).commaObj :=
  (isComma f.lMap (𝟙 f.commaObj)).lift
    ⟨(commaCone f.hom (𝟙 f.cod)).left, 𝟙 f.commaObj, f.counitCell⟩

/-- The comultiplication `Lf ⟶ L(Lf)`, the square `(𝟙, σ_f)`. -/
def coassocHom : L.obj f ⟶ L.obj (L.obj f) :=
  ⟨𝟙 f.dom, f.coassocMap, (isComma _ _).ext (by kernel_rfl)⟩

/-! ### Naturality

The 1-dimensional naturality of `π` and `σ` is a rule, so that their 2-dimensional naturality is
stated without transport. -/

variable {f} {g : Arr B} {m n : f ⟶ g}

@[rewrite_rule]
theorem compMap_naturality (m : f ⟶ g) :
    f.compMap ≫ commaMap m = commaMap (R.map m) ≫ g.compMap := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem coassocMap_naturality (m : f ⟶ g) :
    commaMap m ≫ g.coassocMap = f.coassocMap ≫ commaMap (L.map m) := by
  comma_ext; kernel_rfl

theorem lMap_naturality₂ (α : m ⟶ n) : f.lMap ◁ commaMap₂ α = α.left ▷ g.lMap := by
  comma_ext₂ <;> kernel_rfl

theorem compMap_naturality₂ (α : m ⟶ n) :
    f.compMap ◁ commaMap₂ α = commaMap₂ (R.map₂ α) ▷ g.compMap := by
  comma_ext₂ <;> kernel_rfl

theorem coassocMap_naturality₂ (α : m ⟶ n) :
    commaMap₂ α ▷ g.coassocMap = f.coassocMap ◁ commaMap₂ (L.map₂ α) := by
  comma_ext₂ <;> kernel_rfl

variable (f)

/-- The equation of the comultiplication square, `L(Lf) = Lf ≫ σ_f`. -/
@[rewrite_rule]
theorem lMap_L_obj : (L.obj f).lMap = f.lMap ≫ f.coassocMap := by
  comma_ext; kernel_rfl

/-- `τ_{Lf}` and `τ_f` agree along `σ_f`. -/
@[rewrite_rule]
theorem coassocMap_whiskerLeft_counitCell :
    f.coassocMap ◁ (L.obj f).counitCell = f.counitCell ▷ f.coassocMap := by
  comma_ext₂ <;> kernel_rfl

theorem coassocMap_coassoc :
    f.coassocMap ≫ (L.obj f).coassocMap = f.coassocMap ≫ commaMap f.coassocHom := by
  comma_ext; kernel_rfl

end Arr

set_option maxHeartbeats 2000000 in
-- The laws reduce to equations between large composites, checked in the kernel.
/-- `R` is a 2-monad on the arrow 2-category. -/
def rMonad : TwoMonad (Arr B) where
  toPreTwoMonad :=
    { T := R
      η f := ⟨f.lMap, 𝟙 f.cod, by kernel_rfl⟩
      μ f := ⟨f.compMap, 𝟙 f.cod, by kernel_rfl⟩
      η_naturality := by arr_ext
      μ_naturality := by arr_ext
      unit_left := by arr_ext
      unit_right := by arr_ext
      assoc := by arr_ext }
  η_naturality₂ α := Arr.Hom₂.ext (lMap_naturality₂ α) (by kernel_rfl)
  μ_naturality₂ α := Arr.Hom₂.ext (compMap_naturality₂ α) (by kernel_rfl)

set_option maxHeartbeats 2000000 in
-- The laws reduce to equations between large composites, checked in the kernel.
/-- `L` is a 2-comonad on the arrow 2-category. -/
def lComonad : TwoComonad (Arr B) where
  toPreTwoComonad :=
    { T := L
      ε f := ⟨𝟙 f.dom, (commaCone f.hom (𝟙 f.cod)).right, by kernel_rfl⟩
      δ f := f.coassocHom
      ε_naturality := by arr_ext
      δ_naturality := by arr_ext
      counit_left := by arr_ext
      counit_right := by arr_ext
      coassoc f := Arr.Hom.ext rfl f.coassocMap_coassoc }
  ε_naturality₂ := by arr_ext
  δ_naturality₂ α := Arr.Hom₂.ext (by kernel_rfl) (coassocMap_naturality₂ α)

variable (B)

/-- The 2-category of strict algebras of the 2-monad `R`. -/
abbrev RAlg :=
  (rMonad (B := B)).Alg

/-- The 2-category of strict coalgebras of the 2-comonad `L`. -/
abbrev LCoalg :=
  (lComonad (B := B)).Coalg

end CategoryTheory.TwoCategory
