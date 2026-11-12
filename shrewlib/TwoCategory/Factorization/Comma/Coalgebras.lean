import TwoCategory.Factorization.Comma.AWFS
import TwoCategory.Monad.ColaxIdempotent

/-!
# `L` is colax idempotent; `L`-coalgebras are LARIs

Let `f : A ⟶ B` be a 1-cell of a 2-category with comma objects, factored as `f = Lf ≫ Rf` through
`f/B` (`TwoCategory.Factorization.Comma.Basic`), with legs `q_f : f/B ⟶ A` and `Rf : f/B ⟶ B` and
universal 2-cell `ν_f : q_f ≫ f ⟶ Rf`. This file is dual to `Comma/Algebras.lean`.

## `L` is colax idempotent

The 2-comonad `L` is colax idempotent (`lColaxIdempotent`, see `TwoCategory.Monad.ColaxIdempotent`),
with `θ_f = (𝟙, ξ_f) : L(ε_f) ⟶ ε_{Lf}`. Here `L(ε_f) = (𝟙, commaMap ε_f)`, where
`commaMap ε_f : Lf/(f/B) ⟶ f/B` sends `(a, x, φ : Lf a ⟶ x)` to `(a, Rf x, Rf φ)`, and
`ε_{Lf} = (𝟙, R(Lf))` sends it to `x`; `ξ_f` is induced by `ν_{Lf} ▷ q_f`, the first component of
`φ`, and the identity. The laws of `θ` hold by the universal property of `f/B`, in the kernel; the
naturality of `ε` mapped by `commaMap` is made a rule (`commaMap_L_map_comp_commaMap_ε`), as
`commaMap_comp` splits its two sides differently. So the strict `L`-coalgebras are the split
coreflections of the counits `(𝟙, Rf)` in `Arr B` (`lCoalgEquiv`).

## LARIs

A *left adjoint right inverse* (LARI) of `f` (`Arr.Lari`) is a retraction `r : B ⟶ A`,
`f ≫ r = 𝟙`, with a counit `ε : r ≫ f ⟶ 𝟙` making `f ⊣ r` with identity unit (`Lari.adj`): the
triangle laws are `f ◁ ε = 𝟙` and `ε ▷ r = 𝟙`. As for `Arr.LRetraction`, the equation of 1-cells
is a rule field of a first structure (`Arr.Retraction`), so that the triangle laws are stated
without transport; they are rules too. **An `L`-coalgebra structure on `f` is the same as a LARI**
(`lcoalgEquiv : LCoalg B ≃ Σ f : Arr B, f.Lari`):

* a coaction satisfying the counit law is a square `(𝟙, s) : f ⟶ Lf` with `s ≫ Rf = 𝟙`
  (`Arr.LCoretraction`, whose equations are rules); by the universal property of `f/B`, `s` is a
  cone `(r, 𝟙, ε)`, with `r = s ≫ q_f` and `ε = s ◁ ν_f`;
* the square commuting, `f ≫ s = Lf`, says `f ≫ r = 𝟙` and `f ◁ ε = 𝟙`;
* the coassociativity law, `s ≫ σ_f = s ≫ commaMap (𝟙, s)`, says `s ◁ τ_f = ε ▷ s`, whose first
  component is `ε ▷ r = 𝟙` (`LCoretraction.counit_whiskerRight_r`, `Lari.isSplit`).

Conversely the coalgebra of a LARI (`Lari.toLCoalg`) has coaction `(𝟙, s)`, with `s` induced by
`(r, 𝟙, ε)`. The LARI of the coalgebra of `l` is `l` by `rfl`, and the coalgebra of the LARI of a
coalgebra is that coalgebra since `s` is induced by its own cone.

A square `(u, v) : f' ⟶ f` between LARIs commuting with the retractions, `v ≫ r = r' ≫ u`, and
with the counits, `v ◁ ε = ε' ▷ v`, is a morphism of LARIs (`Lari.Hom`, with the equations as rules,
in two layers), hence of the corresponding `L`-coalgebras (`Lari.Hom.toLCoalgHom`).

The adjunction `f ⊣ r` lives in `B`, while colax idempotence gives `ε_f ⊣ (𝟙, s)` in `Arr B`, whose
codomain component is `Rf ⊣ s`. Their units do not compare componentwise by the rules: the
composite `commaMap (𝟙, s) ≫ commaMap ε_f` of the components of the type of the latter is not
identified with `𝟙`, so the two forms are related through the coalgebras only.
-/
open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B]

open HasCommas Arr

namespace Arr

variable (f : Arr B)

/-! ## Left adjoint right inverses -/

/-- A retraction of `f : A ⟶ B`: a 1-cell `r : B ⟶ A` with `f ≫ r = 𝟙`, which is a rule. -/
structure Retraction where
  /-- The retraction `r`. -/
  r : f.cod ⟶ f.dom
  hom_comp_r : f.hom ≫ r = 𝟙 f.dom

attribute [rewrite_rule] Retraction.hom_comp_r

namespace Retraction

variable {f} (ρ : f.Retraction)

@[rewrite_rule]
theorem hom_comp_r_assoc {z : B} (k : f.dom ⟶ z) : f.hom ≫ ρ.r ≫ k = k :=
  congrArg (· ≫ k) ρ.hom_comp_r

@[rewrite_rule]
theorem whiskerLeft_hom_comp_r {z : B} {k k' : f.dom ⟶ z} (η : k ⟶ k') : f.hom ◁ ρ.r ◁ η = η :=
  eq_of_heq (whiskerLeft_congr ρ.hom_comp_r η)

@[rewrite_rule]
theorem whiskerRight_hom_comp_r {z : B} {u u' : z ⟶ f.dom} (θ : u ⟶ u') :
    θ ▷ f.hom ▷ ρ.r = θ :=
  eq_of_heq (whiskerRight_congr θ ρ.hom_comp_r)

end Retraction

/-- **A left adjoint right inverse (LARI)** `f ⊣ r`: a retraction `r` of `f` with a counit
`ε : r ≫ f ⟶ 𝟙` such that `f ⊣ r` with the identity as unit. The triangle laws `f ◁ ε = 𝟙` and
`ε ▷ r = 𝟙` are stated without transport, as `f ≫ r = 𝟙` is a rule, and are rules too. -/
structure Lari where
  /-- The retraction `r`. -/
  toRetraction : f.Retraction
  /-- The counit `ε : r ≫ f ⟶ 𝟙`. -/
  counit : toRetraction.r ≫ f.hom ⟶ 𝟙 f.cod
  hom_whiskerLeft_counit : f.hom ◁ counit = 𝟙 f.hom
  counit_whiskerRight_r : counit ▷ toRetraction.r = 𝟙 toRetraction.r

attribute [rewrite_rule] Lari.hom_whiskerLeft_counit Lari.counit_whiskerRight_r

namespace Lari

variable {f} (l : f.Lari)

/-- The triangle law `f ◁ ε = 𝟙`, in the normal form of whiskerings. -/
@[rewrite_rule]
theorem hom_whiskerLeft_counit_whiskerRight {z : B} (k : f.cod ⟶ z) :
    f.hom ◁ l.counit ▷ k = 𝟙 (f.hom ≫ k) := by
  kernel_exact congrArg (· ▷ k) l.hom_whiskerLeft_counit

/-- **The adjunction `f ⊣ r`** of a LARI, with the identity as unit. -/
def adj : f.hom ⊣ l.toRetraction.r where
  unit := 𝟙 _
  counit := l.counit
  left_triangle := by kernel_exact l.hom_whiskerLeft_counit
  right_triangle := by kernel_exact l.counit_whiskerRight_r

/-- The unit of the adjunction of a LARI is the identity. -/
theorem adj_unit : l.adj.unit = 𝟙 (𝟙 f.dom) :=
  rfl

/-- The counit of the adjunction of a LARI is its counit. -/
theorem adj_counit : l.adj.counit = l.counit :=
  rfl

/-! ### Morphisms of LARIs -/

/-- The 1-dimensional part of a morphism of LARIs from `l'` to `l`: a square `(u, v) : f' ⟶ f`
commuting with the retractions, `v ≫ r = r' ≫ u`, which is a rule. -/
structure PreHom {f' : Arr B} (l' : f'.Lari) (l : f.Lari) where
  /-- The square `(u, v) : f' ⟶ f`. -/
  sq : f' ⟶ f
  r_comm : sq.right ≫ l.toRetraction.r = l'.toRetraction.r ≫ sq.left

attribute [rewrite_rule] PreHom.r_comm

@[rewrite_rule]
theorem PreHom.r_comm_assoc {f' : Arr B} {l' : f'.Lari} (φ : PreHom l' l) {z : B}
    (k : f.dom ⟶ z) :
    φ.sq.right ≫ l.toRetraction.r ≫ k = l'.toRetraction.r ≫ φ.sq.left ≫ k :=
  congrArg (· ≫ k) φ.r_comm

/-- **A morphism of LARIs** from `l'` to `l`: a square `(u, v) : f' ⟶ f` commuting with the
retractions and with the counits, `v ◁ ε = ε' ▷ v`. The latter is stated without transport by the
rule `v ≫ r = r' ≫ u`, and is a rule too. -/
structure Hom {f' : Arr B} (l' : f'.Lari) (l : f.Lari) where
  /-- The square, commuting with the retractions. -/
  toPreHom : PreHom l' l
  counit_comm : toPreHom.sq.right ◁ l.counit = l'.counit ▷ toPreHom.sq.right

attribute [rewrite_rule] Hom.counit_comm

end Lari

end Arr

variable [HasCommas B]

namespace Arr

variable (f : Arr B)

/-! ## The 2-cell `ξ_f` -/

/-- The 2-cell `ξ_f : commaMap ε_f ⟶ R(Lf)` of `f/B`, between the two 1-cells
`Lf/(f/B) ⟶ f/B` sending `(a, x, φ : Lf a ⟶ x)` to `(a, Rf x, Rf φ)` and to `x`: induced by
`ν_{Lf} ▷ q_f : q_{Lf} ⟶ R(Lf) ≫ q_f` and the identity of `R(Lf) ≫ Rf`. -/
def counitMapCell :
    commaMap (lComonad.ε f) ⟶ (commaCone (L.obj f).hom (𝟙 (L.obj f).cod)).right :=
  (isComma f.hom (𝟙 f.cod)).lift₂ (u := commaMap (lComonad.ε f))
    (v := (commaCone (L.obj f).hom (𝟙 (L.obj f).cod)).right)
    (CommaCone.homMk
      ((commaCone (L.obj f).hom (𝟙 (L.obj f).cod)).hom ▷ (commaCone f.hom (𝟙 f.cod)).left)
      (𝟙 _)
      (by kernel_exact (whisker_exchange (commaCone (L.obj f).hom (𝟙 (L.obj f).cod)).hom
        (commaCone f.hom (𝟙 f.cod)).hom).symm))

/-- The naturality of the counit `ε_f = (𝟙, Rf)`, on the codomains of the squares: `commaMap`
of the two sides of `L m ≫ ε_g = ε_f ≫ m`. The rule `commaMap_comp` splits `commaMap` of each side
into a different composite, which this rule identifies. -/
@[rewrite_rule]
theorem commaMap_L_map_comp_commaMap_ε {g : Arr B} (m : f ⟶ g) :
    commaMap (L.map m) ≫ commaMap (lComonad.ε g) = commaMap (lComonad.ε f) ≫ commaMap m := by
  comma_ext; kernel_rfl

@[rewrite_rule]
theorem commaMap_L_map_comp_commaMap_ε_assoc {g : Arr B} (m : f ⟶ g) {z : B}
    (k : g.commaObj ⟶ z) :
    commaMap (L.map m) ≫ commaMap (lComonad.ε g) ≫ k = commaMap (lComonad.ε f) ≫ commaMap m ≫ k :=
  by kernel_exact congrArg (· ≫ k) (f.commaMap_L_map_comp_commaMap_ε m)

/-- The 2-cell `θ_f = (𝟙, ξ_f) : L(ε_f) ⟶ ε_{Lf}` of squares. -/
def counitMapHom₂ : lComonad.T.map (lComonad.ε f) ⟶ lComonad.ε (lComonad.T.obj f) :=
  ⟨𝟙 (𝟙 f.dom), f.counitMapCell, by comma_ext₂ <;> kernel_rfl⟩

end Arr

/-- **`L` is colax idempotent**, with `θ_f = (𝟙, ξ_f) : L(ε_f) ⟶ ε_{Lf}`. -/
def lColaxIdempotent : (lComonad (B := B)).ColaxIdempotent where
  θ f := f.counitMapHom₂
  θ_naturality := by arr_ext
  δ_whiskerLeft_θ := by arr_ext
  θ_whiskerRight_ε := by arr_ext

/-- The strict `L`-coalgebras are the split coreflections of the counits `(𝟙, Rf) : Lf ⟶ f` in
`Arr B`, by colax idempotence. -/
def lCoalgEquiv : LCoalg B ≃ Σ f : Arr B, (lComonad (B := B)).SplitCoreflection f :=
  lColaxIdempotent.coalgEquiv

omit [HasCommas B] in
/-- Comma cones with the same legs and equal 2-cells are equal. -/
theorem CommaCone.ext_hom {a b c x : B} {f : a ⟶ c} {g : b ⟶ c} (l : x ⟶ a) (r : x ⟶ b)
    {h h' : l ≫ f ⟶ r ≫ g} (e : h = h') : (⟨l, r, h⟩ : CommaCone f g x) = ⟨l, r, h'⟩ := by
  subst e
  rfl

namespace Arr

variable (f : Arr B)

/-! ## Coretractions of `Lf` under the domain -/

/-- A coretraction of `ε_f = (𝟙, Rf) : Lf ⟶ f` under the domain: a square `(𝟙, s) : f ⟶ Lf` with
`s ≫ Rf = 𝟙`. These are the coactions satisfying the counit law of an `L`-coalgebra. -/
structure LCoretraction where
  /-- The square `(𝟙, s) : f ⟶ Lf`. -/
  coact : f ⟶ L.obj f
  coact_left : coact.left = 𝟙 f.dom
  coact_right_comp : coact.right ≫ (commaCone f.hom (𝟙 f.cod)).right = 𝟙 f.cod

attribute [rewrite_rule] LCoretraction.coact_left LCoretraction.coact_right_comp

namespace LCoretraction

variable {f} (c : f.LCoretraction)

@[rewrite_rule]
theorem coact_right_comp_assoc {z : B} (k : f.cod ⟶ z) :
    c.coact.right ≫ (commaCone f.hom (𝟙 f.cod)).right ≫ k = k := by
  kernel_exact congrArg (· ≫ k) c.coact_right_comp

@[rewrite_rule]
theorem whiskerLeft_coact_right_comp {z : B} {k k' : f.cod ⟶ z} (η : k ⟶ k') :
    c.coact.right ◁ (commaCone f.hom (𝟙 f.cod)).right ◁ η = η :=
  eq_of_heq (whiskerLeft_congr c.coact_right_comp η)

/-- `f ≫ s = Lf`, the equation of the square `(𝟙, s)`. It is a rule, as the rule `Arr.Hom.w`
sends `𝟙 ≫ Lf` to `f ≫ s`, while the rule `coact_left` sends it to `Lf`. -/
@[rewrite_rule]
theorem hom_comp_coact_right : f.hom ≫ c.coact.right = f.lMap :=
  c.coact.w.symm.trans (congrArg (· ≫ (L.obj f).hom) c.coact_left)

@[rewrite_rule]
theorem hom_comp_coact_right_assoc {z : B} (k : f.commaObj ⟶ z) :
    f.hom ≫ c.coact.right ≫ k = f.lMap ≫ k := by
  kernel_exact congrArg (· ≫ k) c.hom_comp_coact_right

@[rewrite_rule]
theorem whiskerLeft_hom_comp_coact_right {z : B} {k k' : f.commaObj ⟶ z} (η : k ⟶ k') :
    f.hom ◁ c.coact.right ◁ η = f.lMap ◁ η :=
  eq_of_heq (whiskerLeft_congr c.hom_comp_coact_right η)

/-- The coretraction is split: the coassociativity law of an `L`-coalgebra. -/
def IsSplit : Prop :=
  c.coact ≫ lComonad.δ f = c.coact ≫ L.map c.coact

/-- The retraction `r = s ≫ q_f : B ⟶ A` of `f`. -/
def r : f.cod ⟶ f.dom :=
  c.coact.right ≫ (commaCone f.hom (𝟙 f.cod)).left

/-- The counit `s ◁ ν_f : r ≫ f ⟶ 𝟙`. -/
def counit : c.r ≫ f.hom ⟶ 𝟙 f.cod :=
  c.coact.right ◁ (commaCone f.hom (𝟙 f.cod)).hom

/-- `f ≫ s ≫ q_f = 𝟙`, by the equation of the square `(𝟙, s)`. -/
theorem hom_comp_r : f.hom ≫ c.r = 𝟙 f.dom := by
  kernel_rfl

/-- `f ◁ s ◁ ν_f = 𝟙`, by the equation of the square `(𝟙, s)`. -/
theorem hom_whiskerLeft_counit : f.hom ◁ c.counit = 𝟙 f.hom := by
  kernel_rfl

/-- The coassociativity law, on the codomains, whiskered with the universal 2-cell of `Lf/(f/B)`:
`s ◁ τ_f = s ◁ ν_f ▷ s`. -/
theorem coact_right_whiskerLeft_counitCell (h : c.IsSplit) :
    c.coact.right ◁ f.counitCell = c.counit ▷ c.coact.right := by
  have e : c.coact.right ≫ f.coassocMap = c.coact.right ≫ commaMap c.coact := by
    kernel_exact congrArg Arr.Hom.right h
  kernel_exact eq_of_heq (whiskerLeft_congr e (commaCone (L.obj f).hom (𝟙 (L.obj f).cod)).hom)

/-- The second triangle law, from the coassociativity law. -/
theorem counit_whiskerRight_r (h : c.IsSplit) : c.counit ▷ c.r = 𝟙 c.r := by
  kernel_exact (congrArg (· ▷ (commaCone f.hom (𝟙 f.cod)).left)
    (c.coact_right_whiskerLeft_counitCell h)).symm

end LCoretraction

namespace Lari

variable {f} (l : f.Lari)

/-- The 1-cell `s : B ⟶ f/B` induced by the cone `(r, 𝟙, ε)`: `s b = (r b, b, ε_b)`. -/
def sec : f.cod ⟶ f.commaObj :=
  (isComma f.hom (𝟙 f.cod)).lift ⟨l.toRetraction.r, 𝟙 f.cod, l.counit⟩

/-- The square `(𝟙, s) : f ⟶ Lf`. -/
def coact : f ⟶ L.obj f :=
  ⟨𝟙 f.dom, l.sec, by comma_ext; kernel_rfl⟩

/-- The square `(𝟙, s)`, as a coretraction of `ε_f` under the domain. -/
def toLCoretraction : f.LCoretraction :=
  ⟨l.coact, rfl, by kernel_rfl⟩

/-- `s ◁ τ_f = ε ▷ s`: the coassociativity law, on the codomains, whiskered with the universal
2-cell of `Lf/(f/B)`. -/
theorem sec_whiskerLeft_counitCell :
    l.toLCoretraction.coact.right ◁ f.counitCell =
      l.counit ▷ l.toLCoretraction.coact.right := by
  comma_ext₂ <;> kernel_rfl

/-- **The square `(𝟙, s)` is split**, by the triangle law `ε ▷ r = 𝟙`. -/
theorem isSplit : l.toLCoretraction.IsSplit := by
  refine Arr.Hom.ext (by kernel_rfl) ?_
  comma_ext
  kernel_exact CommaCone.ext_hom (f := f.lMap) (g := 𝟙 f.commaObj) l.toRetraction.r
    l.toLCoretraction.coact.right l.sec_whiskerLeft_counitCell

/-- **The `L`-coalgebra of a LARI**, with coaction `(𝟙, s)`. -/
def toLCoalg : LCoalg B where
  obj := f
  coact := l.toLCoretraction.coact
  counit := Arr.Hom.ext rfl (by kernel_rfl)
  coassoc := l.isSplit

end Lari

namespace LCoretraction

variable {f} (c : f.LCoretraction)

/-- **The LARI of a split coretraction** `(𝟙, s)`: `r = s ≫ q_f` and `ε = s ◁ ν_f`. -/
def toLari (h : c.IsSplit) : f.Lari where
  toRetraction := ⟨c.r, c.hom_comp_r⟩
  counit := c.counit
  hom_whiskerLeft_counit := c.hom_whiskerLeft_counit
  counit_whiskerRight_r := c.counit_whiskerRight_r h

/-- The coretraction of the LARI of a split coretraction is that coretraction: `s` is induced by
its own cone `(s ≫ q_f, 𝟙, s ◁ ν_f)`. -/
theorem toLari_coact (h : c.IsSplit) : (c.toLari h).coact = c.coact :=
  Arr.Hom.ext rfl (by comma_ext; kernel_rfl)

end LCoretraction

namespace Lari

variable {f} {f' : Arr B} {l : f.Lari} {l' : f'.Lari}

/-- **A morphism of LARIs is a morphism of the corresponding `L`-coalgebras.** -/
def Hom.toLCoalgHom (φ : Hom l' l) : l'.toLCoalg ⟶ l.toLCoalg :=
  ⟨φ.toPreHom.sq, Arr.Hom.ext (by kernel_rfl) (by comma_ext; kernel_rfl)⟩

/-- The morphism of coalgebras of a morphism of LARIs is its square. -/
@[simp]
theorem Hom.toLCoalgHom_hom (φ : Hom l' l) : φ.toLCoalgHom.hom = φ.toPreHom.sq :=
  rfl

end Lari

end Arr

namespace TwoComonad.Coalg

variable (c : LCoalg B)

/-- The coaction of an `L`-coalgebra, as a coretraction of the counit under the domain. -/
def toLCoretraction : c.obj.LCoretraction where
  coact := c.coact
  coact_left := by kernel_exact congrArg Arr.Hom.left c.counit
  coact_right_comp := by kernel_exact congrArg Arr.Hom.right c.counit

/-- **The LARI of an `L`-coalgebra.** -/
def toLari : c.obj.Lari :=
  c.toLCoretraction.toLari c.coassoc

end TwoComonad.Coalg

/-- **`L`-coalgebras are LARIs**: an `L`-coalgebra structure on `f : A ⟶ B` is the same as a
retraction `r` of `f` with a counit `ε : r ≫ f ⟶ 𝟙` making `f ⊣ r` with identity unit. -/
def lcoalgEquiv : LCoalg B ≃ Σ f : Arr B, f.Lari where
  toFun c := ⟨c.obj, c.toLari⟩
  invFun l := l.2.toLCoalg
  left_inv c := by
    have e : (c.toLCoretraction.toLari c.coassoc).coact = c.coact :=
      c.toLCoretraction.toLari_coact c.coassoc
    obtain ⟨f, coact, h₁, h₂⟩ := c
    change (⟨f, _, _, _⟩ : LCoalg B) = ⟨f, coact, h₁, h₂⟩
    congr
  right_inv l := by
    obtain ⟨f, l⟩ := l
    rfl


end CategoryTheory.TwoCategory
