import Bicategory.Pullback
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Basic

/-!
# Comma objects in a 2-category

For 1-cells `f : a ⟶ c` and `g : b ⟶ c` of a 2-category `B`, a *comma cone* over `f` and `g` with
apex `x` consists of 1-cells `q₁ : x ⟶ a`, `q₂ : x ⟶ b` and a 2-cell `q₁ ≫ f ⟶ q₂ ≫ g`:
```
   x ──q₂──▶ b
   │    ⇗    │
   q₁        g
   ▼         ▼
   a ──f───▶ c
```
The comma cones with apex `x` form the comma category `CommaCone f g x`, which is Mathlib's
`Comma (postcomp x f) (postcomp x g)`: a morphism is a pair of 2-cells `q₁ ⟶ q₁'`, `q₂ ⟶ q₂'`
compatible with the 2-cells of the cones.

A comma cone `s` with apex `p` induces, for every `x`, the functor
`s.precomposing x : (x ⟶ p) ⥤ CommaCone f g x` sending `u` to the cone `u ≫ s.left`, `u ≫ s.right`,
`u ◁ s.hom`. The cone `s` is a *comma object* (`IsComma s`) if these functors are isomorphisms of
categories, as in Street, *Fibrations and Yoneda's lemma in a 2-category*, that is:

* (1-dimensional) every comma cone `t` with apex `x` is `(s.precomposing x).obj u` for a unique
  `u = lift t : x ⟶ p` (`IsComma.fac`, `IsComma.uniq`);
* (2-dimensional) every morphism of cones `(s.precomposing x).obj u ⟶ (s.precomposing x).obj v`
  is `(s.precomposing x).map θ` for a unique 2-cell `θ = lift₂ φ : u ⟶ v` (`IsComma.fac₂`,
  `IsComma.uniq₂`).

The 1-dimensional universal property is a rule: `lift t ≫ s.left ↦ t.left`,
`lift t ≫ s.right ↦ t.right` and `lift t ◁ s.hom ↦ t.hom`, also reassociated and whiskered. So is
the 2-dimensional one, `lift₂ φ ▷ s.left ↦ φ.left` and `lift₂ φ ▷ s.right ↦ φ.right`.

The apexes of two comma objects over the same cospan are isomorphic in the underlying 1-category
(`IsComma.apexIso`), compatibly with the cones. `HasCommas B` chooses a comma object of every
cospan.

Pasting a pullback (`Bicategory.Pullback`) on the left of a comma object gives a comma object
(`IsComma.pasteLeft`): if `s` is a comma object of `f` and `g`, and `t` is a pullback of `s.left`
along `h : a' ⟶ a`, then `s.pasteLeft t` is a comma object of `h ≫ f` and `g`:
```
   q ──t.snd───▶ p ──s.right──▶ b
   │              │       ⇗      │
 t.fst          s.left           g
   ▼              ▼              ▼
   a' ────h────▶ a ──────f─────▶ c
```

In `Cat`, Mathlib's comma category `Comma L R` is a comma object of `L` and `R`
(`Comma.isComma`).

The laws of the 2-category are rules (`Bicategory.Basic`), so cones are precomposed without
associators: `(s.precomposing x).obj (𝟙 p) = s`, `(s.precomposing x).obj (h ≫ k) =
(precomp h).obj ((s.precomposing y).obj k)`, `precomp (𝟙 x) = 𝟭 _` and
`precomp (h ≫ k) = precomp k ⋙ precomp h` hold by `rfl`, as do the functor laws.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] {a b c : B} (f : a ⟶ c) (g : b ⟶ c)

/-- The comma cones over `f : a ⟶ c` and `g : b ⟶ c` with apex `x`: 1-cells `left : x ⟶ a` and
`right : x ⟶ b` with a 2-cell `hom : left ≫ f ⟶ right ≫ g`. -/
abbrev CommaCone (x : B) :=
  Comma (postcomp x f) (postcomp x g)

namespace CommaCone

variable {f g}

/-- A morphism of comma cones from 2-cells between their legs, compatible with their 2-cells. -/
abbrev homMk {x : B} {s t : CommaCone f g x} (φ₁ : s.left ⟶ t.left) (φ₂ : s.right ⟶ t.right)
    (w : φ₁ ▷ f ≫ t.hom = s.hom ≫ φ₂ ▷ g := by cat_disch) : s ⟶ t :=
  ⟨φ₁, φ₂, w⟩

theorem w' {x : B} {s t : CommaCone f g x} (φ : s ⟶ t) :
    φ.left ▷ f ≫ t.hom = s.hom ≫ φ.right ▷ g :=
  φ.w

/-- Precomposition of comma cones with a 1-cell `u : x ⟶ y`. -/
@[simps]
def precomp {x y : B} (u : x ⟶ y) : CommaCone f g y ⥤ CommaCone f g x where
  obj s :=
    { left := u ≫ s.left
      right := u ≫ s.right
      hom := u ◁ s.hom }
  map φ := homMk (u ◁ φ.left) (u ◁ φ.right) (congrArg (u ◁ ·) φ.w)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem precomp_id (x : B) : precomp (f := f) (g := g) (𝟙 x) = 𝟭 _ :=
  rfl

theorem precomp_comp {x y z : B} (h : x ⟶ y) (k : y ⟶ z) :
    precomp (f := f) (g := g) (h ≫ k) = precomp k ⋙ precomp h :=
  rfl

variable {p : B} (s : CommaCone f g p)

/-- Precomposing a comma cone `s` with apex `p`: the functor `(x ⟶ p) ⥤ CommaCone f g x` sending
`u` to `(precomp u).obj s`, and a 2-cell `θ : u ⟶ v` to its whiskerings with the legs of `s`. -/
@[simps]
def precomposing (x : B) : (x ⟶ p) ⥤ CommaCone f g x where
  obj u := (precomp u).obj s
  map θ := homMk (θ ▷ s.left) (θ ▷ s.right) (whisker_exchange θ s.hom).symm
  map_id _ := rfl
  map_comp _ _ := rfl

theorem precomposing_obj_id : (s.precomposing p).obj (𝟙 p) = s :=
  rfl

theorem precomposing_obj_comp {x y : B} (h : x ⟶ y) (k : y ⟶ p) :
    (s.precomposing x).obj (h ≫ k) = (precomp h).obj ((s.precomposing y).obj k) :=
  rfl

theorem precomposing_map_whiskerLeft {x y : B} (h : x ⟶ y) {k k' : y ⟶ p} (θ : k ⟶ k') :
    (s.precomposing x).map (h ◁ θ) = (precomp h).map ((s.precomposing y).map θ) :=
  rfl

end CommaCone

open CommaCone

variable {f g}

/-- A comma cone `s` over `f` and `g` with apex `p` is a comma object if precomposing with it is an
isomorphism of categories `(x ⟶ p) ≅ CommaCone f g x` for every `x`: it is bijective on objects
(the 1-dimensional universal property) and on morphisms (the 2-dimensional one). -/
structure IsComma {p : B} (s : CommaCone f g p) where
  /-- The 1-cell induced by a comma cone. -/
  lift {x : B} (t : CommaCone f g x) : x ⟶ p
  fac {x : B} (t : CommaCone f g x) : (s.precomposing x).obj (lift t) = t
  uniq {x : B} (t : CommaCone f g x) (u : x ⟶ p) (h : (s.precomposing x).obj u = t) :
    u = lift t
  /-- The 2-cell induced by a morphism of comma cones. -/
  lift₂ {x : B} {u v : x ⟶ p} (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v) : u ⟶ v
  fac₂ {x : B} {u v : x ⟶ p} (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v) :
    (s.precomposing x).map (lift₂ φ) = φ
  uniq₂ {x : B} {u v : x ⟶ p} (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v)
    (θ : u ⟶ v) (h : (s.precomposing x).map θ = φ) : θ = lift₂ φ

namespace IsComma

attribute [simp] fac fac₂

variable {p : B} {s : CommaCone f g p} (hs : IsComma s)

include hs

/-! The 1-dimensional universal property is a rule: composites of the induced 1-cell with the legs
compute, also reassociated and whiskered, and so does its whiskering with the 2-cell of `s`. -/

@[rewrite_rule]
theorem lift_comp_left {x : B} (t : CommaCone f g x) : hs.lift t ≫ s.left = t.left :=
  congrArg Comma.left (hs.fac t)

@[rewrite_rule]
theorem lift_comp_right {x : B} (t : CommaCone f g x) : hs.lift t ≫ s.right = t.right :=
  congrArg Comma.right (hs.fac t)

@[rewrite_rule]
theorem lift_comp_left_assoc {x d : B} (t : CommaCone f g x) (k : a ⟶ d) :
    hs.lift t ≫ s.left ≫ k = t.left ≫ k :=
  congrArg (· ≫ k) (hs.lift_comp_left t)

@[rewrite_rule]
theorem lift_comp_right_assoc {x d : B} (t : CommaCone f g x) (k : b ⟶ d) :
    hs.lift t ≫ s.right ≫ k = t.right ≫ k :=
  congrArg (· ≫ k) (hs.lift_comp_right t)

@[rewrite_rule]
theorem lift_whiskerLeft_left {x d : B} (t : CommaCone f g x) {k k' : a ⟶ d} (η : k ⟶ k') :
    hs.lift t ◁ s.left ◁ η = t.left ◁ η :=
  eq_of_heq (whiskerLeft_congr (hs.lift_comp_left t) η)

@[rewrite_rule]
theorem lift_whiskerLeft_right {x d : B} (t : CommaCone f g x) {k k' : b ⟶ d} (η : k ⟶ k') :
    hs.lift t ◁ s.right ◁ η = t.right ◁ η :=
  eq_of_heq (whiskerLeft_congr (hs.lift_comp_right t) η)

@[rewrite_rule]
theorem whiskerRight_lift_left {x y : B} (t : CommaCone f g x) {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ hs.lift t ▷ s.left = θ ▷ t.left :=
  eq_of_heq (whiskerRight_congr θ (hs.lift_comp_left t))

@[rewrite_rule]
theorem whiskerRight_lift_right {x y : B} (t : CommaCone f g x) {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ hs.lift t ▷ s.right = θ ▷ t.right :=
  eq_of_heq (whiskerRight_congr θ (hs.lift_comp_right t))

@[rewrite_rule]
theorem lift_whiskerLeft_hom {x : B} (t : CommaCone f g x) : hs.lift t ◁ s.hom = t.hom :=
  eq_of_heq (congr_arg_heq Comma.hom (hs.fac t))

@[rewrite_rule]
theorem lift_whiskerLeft_hom_whiskerRight {x d : B} (t : CommaCone f g x) (k : c ⟶ d) :
    hs.lift t ◁ s.hom ▷ k = t.hom ▷ k :=
  congrArg (· ▷ k) (hs.lift_whiskerLeft_hom t)

/-- Whiskered twice on the right, as for the 2-cells induced by composite squares: whiskerings by
composite 1-cells are split into chains, which the rule above does not reach. -/
@[rewrite_rule]
theorem lift_whiskerLeft_hom_whiskerRight_whiskerRight {x d e : B} (t : CommaCone f g x)
    (k : c ⟶ d) (k' : d ⟶ e) : hs.lift t ◁ (s.hom ▷ k ▷ k') = t.hom ▷ k ▷ k' := by
  rw [← hs.lift_whiskerLeft_hom_whiskerRight t k]
  kernel_rfl

/-- 1-cells into a comma object are determined by their precompositions with it. -/
theorem ext {x : B} {u v : x ⟶ p} (h : (s.precomposing x).obj u = (s.precomposing x).obj v) :
    u = v :=
  (hs.uniq _ u h).trans (hs.uniq _ v rfl).symm

@[simp]
theorem lift_precomposing {x : B} (u : x ⟶ p) : hs.lift ((s.precomposing x).obj u) = u :=
  (hs.uniq _ u rfl).symm

@[rewrite_rule]
theorem lift₂_whiskerRight_left {x : B} {u v : x ⟶ p}
    (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v) : hs.lift₂ φ ▷ s.left = φ.left :=
  congrArg CommaMorphism.left (hs.fac₂ φ)

@[rewrite_rule]
theorem lift₂_whiskerRight_right {x : B} {u v : x ⟶ p}
    (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v) : hs.lift₂ φ ▷ s.right = φ.right :=
  congrArg CommaMorphism.right (hs.fac₂ φ)

/-- 2-cells into a comma object are determined by their whiskerings with the legs. -/
theorem hom_ext {x : B} {u v : x ⟶ p} {θ θ' : u ⟶ v} (h₁ : θ ▷ s.left = θ' ▷ s.left)
    (h₂ : θ ▷ s.right = θ' ▷ s.right) : θ = θ' :=
  (hs.uniq₂ _ θ (Comma.hom_ext _ ((s.precomposing x).map θ') h₁ h₂)).trans
    (hs.uniq₂ _ θ' rfl).symm

@[simp]
theorem lift₂_precomposing {x : B} {u v : x ⟶ p} (θ : u ⟶ v) :
    hs.lift₂ ((s.precomposing x).map θ) = θ :=
  (hs.uniq₂ _ θ rfl).symm

@[simp]
theorem lift₂_id {x : B} (u : x ⟶ p) : hs.lift₂ (𝟙 ((s.precomposing x).obj u)) = 𝟙 u :=
  hs.lift₂_precomposing (𝟙 u)

@[simp]
theorem lift₂_comp {x : B} {u v w : x ⟶ p} (φ : (s.precomposing x).obj u ⟶ (s.precomposing x).obj v)
    (ψ : (s.precomposing x).obj v ⟶ (s.precomposing x).obj w) :
    hs.lift₂ (φ ≫ ψ) = hs.lift₂ φ ≫ hs.lift₂ ψ :=
  hs.hom_ext ((hs.lift₂_whiskerRight_left _).trans
      (congrArg₂ (· ≫ ·) (hs.lift₂_whiskerRight_left φ) (hs.lift₂_whiskerRight_left ψ)).symm)
    ((hs.lift₂_whiskerRight_right _).trans
      (congrArg₂ (· ≫ ·) (hs.lift₂_whiskerRight_right φ) (hs.lift₂_whiskerRight_right ψ)).symm)

theorem faithful (x : B) : (s.precomposing x).Faithful where
  map_injective {u v} θ θ' h := by
    rw [hs.uniq₂ _ θ h, hs.lift₂_precomposing]

theorem full (x : B) : (s.precomposing x).Full where
  map_surjective φ := ⟨hs.lift₂ φ, hs.fac₂ φ⟩

/-- Precomposing with a comma object is an equivalence of categories (indeed an isomorphism). -/
theorem isEquivalence (x : B) : (s.precomposing x).IsEquivalence where
  faithful := hs.faithful x
  full := hs.full x
  essSurj.mem_essImage t := ⟨hs.lift t, ⟨eqToIso (hs.fac t)⟩⟩

/-- The 2-isomorphism induced by an isomorphism of comma cones. -/
@[simps]
def liftIso₂ {x : B} {u v : x ⟶ p} (φ : (s.precomposing x).obj u ≅ (s.precomposing x).obj v) :
    u ≅ v where
  hom := hs.lift₂ φ.hom
  inv := hs.lift₂ φ.inv
  hom_inv_id := by rw [← lift₂_comp, φ.hom_inv_id, lift₂_id]
  inv_hom_id := by rw [← lift₂_comp, φ.inv_hom_id, lift₂_id]

/-- The 1-cell induced by a cone precomposed with `h` is the induced 1-cell precomposed with `h`. -/
theorem lift_precomp {x y : B} (h : x ⟶ y) (t : CommaCone f g y) :
    hs.lift ((precomp h).obj t) = h ≫ hs.lift t :=
  (hs.uniq _ _ (by rw [precomposing_obj_comp, hs.fac])).symm

variable {q : B} {t : CommaCone f g q} (ht : IsComma t)

/-- The composite of the 1-cells induced between two comma objects over the same cospan is the
identity. -/
theorem lift_comp_lift : ht.lift s ≫ hs.lift t = 𝟙 p :=
  hs.ext (by rw [precomposing_obj_comp, hs.fac, ← CommaCone.precomposing_obj, ht.fac]; rfl)

/-- Comma objects over the same cospan have isomorphic apexes, by the induced 1-cells. -/
@[simps]
def apexIso : p ≅ q where
  hom := ht.lift s
  inv := hs.lift t
  hom_inv_id := hs.lift_comp_lift ht
  inv_hom_id := ht.lift_comp_lift hs

/-- The isomorphism between the apexes of two comma objects is compatible with the cones. -/
theorem precomposing_apexIso_hom : (t.precomposing p).obj (hs.apexIso ht).hom = s :=
  ht.fac s

end IsComma

/-! ## Pasting a pullback on the left -/

namespace CommaCone

variable {a' : B} (h : a' ⟶ a)

/-- Comma cones over `h ≫ f` and `g` as comma cones over `f` and `g`, by composing the left leg
with `h`. -/
@[simps]
def compLeft (x : B) : CommaCone (h ≫ f) g x ⥤ CommaCone f g x where
  obj r :=
    { left := r.left ≫ h
      right := r.right
      hom := r.hom }
  map φ := homMk (φ.left ▷ h) φ.right φ.w
  map_id _ := rfl
  map_comp _ _ := rfl

variable {h}

/-- A comma cone over `h ≫ f` and `g` is determined by its left leg and its composite with `h`. -/
theorem ext_of_compLeft {x : B} {r r' : CommaCone (h ≫ f) g x} (e₁ : r.left = r'.left)
    (e : (compLeft h x).obj r = (compLeft h x).obj r') : r = r' := by
  obtain ⟨r₁, r₂, r₃⟩ := r
  obtain ⟨r₁', r₂', r₃'⟩ := r'
  cases e₁
  injection e with _ e₂ e₃
  cases e₂
  cases eq_of_heq e₃
  rfl

variable {p : B}

/-- A pullback cone of the left leg of `s` along `h : a' ⟶ a`, pasted on the left of `s`. -/
@[simps]
def pasteLeft (s : CommaCone f g p) (t : Limits.PullbackCone h s.left) :
    CommaCone (h ≫ f) g t.pt where
  left := t.fst
  right := t.snd ≫ s.right
  hom := t.snd ◁ s.hom

theorem compLeft_obj_precomposing_pasteLeft (s : CommaCone f g p)
    (t : Limits.PullbackCone h s.left) {x : B} (u : x ⟶ t.pt) :
    (compLeft h x).obj (((s.pasteLeft t).precomposing x).obj u) =
      (s.precomposing x).obj (u ≫ t.snd) :=
  rfl

theorem compLeft_map_precomposing_pasteLeft (s : CommaCone f g p)
    (t : Limits.PullbackCone h s.left) {x : B} {u v : x ⟶ t.pt} (θ : u ⟶ v) :
    (compLeft h x).map (((s.pasteLeft t).precomposing x).map θ) =
      (s.precomposing x).map (θ ▷ t.snd) :=
  rfl

end CommaCone

/-- Pasting a pullback on the left of a comma object gives a comma object: if `s` is a comma
object of `f` and `g`, and `t` is a pullback of `s.left` along `h`, then `s.pasteLeft t` is a comma
object of `h ≫ f` and `g`. -/
def IsComma.pasteLeft {a' : B} {h : a' ⟶ a} {p : B} {s : CommaCone f g p}
    {t : Limits.PullbackCone h s.left} (hs : IsComma s) (ht : IsPullback t) :
    IsComma (s.pasteLeft t) where
  lift r := Limits.PullbackCone.IsLimit.lift ht.toIsLimit r.left
    (hs.lift ((compLeft h _).obj r)) (hs.lift_comp_left ((compLeft h _).obj r)).symm
  fac r := ext_of_compLeft rfl (hs.fac ((compLeft h _).obj r))
  uniq _ _ e := ht.hom_ext (congrArg Comma.left e)
    (hs.uniq _ _ (congrArg (compLeft h _).obj e))
  lift₂ {_ u v} φ :=
    let ψ : (s.precomposing _).obj (u ≫ t.snd) ⟶ (s.precomposing _).obj (v ≫ t.snd) :=
      (compLeft h _).map φ
    ht.lift₂ φ.left (hs.lift₂ ψ) (by kernel_rfl)
  fac₂ {_ u v} φ :=
    let ψ : (s.precomposing _).obj (u ≫ t.snd) ⟶ (s.precomposing _).obj (v ≫ t.snd) :=
      (compLeft h _).map φ
    Comma.hom_ext _ _ (ht.lift₂_fst _ _ _)
      ((congrArg (· ▷ s.right) (ht.lift₂_snd φ.left (hs.lift₂ ψ) _)).trans
        (hs.lift₂_whiskerRight_right ψ))
  uniq₂ {_ u v} φ _ e :=
    let ψ : (s.precomposing _).obj (u ≫ t.snd) ⟶ (s.precomposing _).obj (v ≫ t.snd) :=
      (compLeft h _).map φ
    ht.hom_ext₂ ((congrArg CommaMorphism.left e).trans (ht.lift₂_fst _ _ _).symm)
      ((hs.uniq₂ ψ _ (congrArg (compLeft h _).map e)).trans
        (ht.lift₂_snd φ.left (hs.lift₂ ψ) _).symm)

/-! ## Chosen comma objects -/

variable (B) in
/-- A 2-category with chosen comma objects of all cospans. -/
class HasCommas where
  /-- The apex of the chosen comma object of `f` and `g`. -/
  comma {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : B
  /-- The chosen comma cone of `f` and `g`. -/
  commaCone {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : CommaCone f g (comma f g)
  /-- The chosen comma cone is a comma object. -/
  isComma {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : IsComma (commaCone f g)

/-! ## Extensionality for chosen comma objects -/

open Lean Meta Elab Tactic in
/-- Applies `IsComma.ext` to an equation of 1-cells into a chosen comma object `comma f g`,
reading `f` and `g` off the goal. -/
elab "comma_ext" : tactic => withMainContext do
  let some (ty, _, _) := (← whnfR (← getMainTarget)).eq? |
    throwError "comma_ext: the goal is not an equation"
  let some P ← whnfUntil ty.appArg! ``HasCommas.comma |
    throwError "comma_ext: not a 1-cell into a chosen comma object"
  let f ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 2))
  let g ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 1))
  evalTactic (← `(tactic| refine (HasCommas.isComma $f $g).ext ?_))

open Lean Meta Elab Tactic in
/-- Applies `IsComma.hom_ext` to an equation of 2-cells between 1-cells into a chosen comma object
`comma f g`, reading `f` and `g` off the goal. -/
elab "comma_ext₂" : tactic => withMainContext do
  let some (ty, _, _) := (← whnfR (← getMainTarget)).eq? |
    throwError "comma_ext₂: the goal is not an equation"
  let some (_, _, u, v) := (← whnfR ty).app4? ``Quiver.Hom |
    throwError "comma_ext₂: not an equation of 2-cells"
  let oneCell ← whnfR (← inferType u)
  let some P ← whnfUntil oneCell.appArg! ``HasCommas.comma |
    throwError "comma_ext₂: not a 2-cell into a chosen comma object"
  let f ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 2))
  let g ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 1))
  let u ← Term.exprToSyntax u
  let v ← Term.exprToSyntax v
  evalTactic (← `(tactic| refine (HasCommas.isComma $f $g).hom_ext (u := $u) (v := $v) ?_ ?_))

end CategoryTheory.TwoCategory

/-! ## Comma objects in `Cat` -/

namespace CategoryTheory

namespace Comma

open TwoCategory

variable {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C] (L : A ⥤ C)
  (R : B ⥤ C)

/-- The comma category `Comma L R`, as a comma cone over `L` and `R` in `Cat`. -/
def commaCone : CommaCone L.toCatHom R.toCatHom (Cat.of (Comma L R)) where
  left := (fst L R).toCatHom
  right := (snd L R).toCatHom
  hom := (natTrans L R).toCatHom₂

/-- The comma category `Comma L R` is a comma object of `L` and `R` in `Cat`. The universal
property holds on the nose: `fac`, `uniq`, `fac₂` and `uniq₂` are `rfl` up to the structure eta of
functors, natural transformations and comma objects and morphisms. -/
def isComma : IsComma (commaCone L R) where
  lift t := Cat.Hom.ofFunctor
    { obj X := ⟨t.left.toFunctor.obj X, t.right.toFunctor.obj X, t.hom.toNatTrans.app X⟩
      map k := ⟨t.left.toFunctor.map k, t.right.toFunctor.map k, t.hom.toNatTrans.naturality k⟩ }
  fac _ := rfl
  uniq _ _ h := by cases h; rfl
  lift₂ φ := Cat.Hom₂.ofNatTrans
    { app X := ⟨φ.left.toNatTrans.app X, φ.right.toNatTrans.app X,
        congrArg (fun θ ↦ θ.toNatTrans.app X) φ.w⟩
      naturality X Y k := by
        apply Comma.hom_ext
        · exact φ.left.toNatTrans.naturality k
        · exact φ.right.toNatTrans.naturality k }
  fac₂ _ := rfl
  uniq₂ _ _ h := by cases h; rfl

end Comma

end CategoryTheory
