import TwoCategory.Factorization.AWFS

/-!
# Chosen lifts in an AWFS

In an AWFS `(L, R)` on a 2-category `B` (`TwoCategory.Factorization.AWFS`), every square `m : f ⟶ g`
from an `L`-coalgebra `c` to an `R`-algebra `a` has a chosen diagonal filler (Bourke–Garner,
*AWFS I*, §2.4):
```
   x ──m.left──▶ z
   │          ↗  │
   f   lift    g
   ▼  ╱          ▼
   y ──m.right─▶ w
```
the composite `lift c a m : y ⟶ E f ⟶ E g ⟶ z` of

* the nontrivial component `s : y ⟶ E f` of the coaction `(𝟙, s) : f ⟶ L f` of `c`,
* the middle map `E m = (R m).left : E f ⟶ E g` of the factorization of the square `m`,
* the nontrivial component `p : E g ⟶ z` of the action `(p, 𝟙) : R g ⟶ g` of `a`.

The counit law of `c` says that the coaction is `(𝟙, s)` with `s ≫ R f = 𝟙`, and the unit law of `a`
that the action is `(p, 𝟙)` with `L g ≫ p = 𝟙`. So the filler makes both triangles commute
(`hom_comp_lift`, `lift_comp_hom`): `f ≫ s = L f` by the equation of the coaction square, and
`L f ≫ E m = m.left ≫ L g` by that of `L m`, which `p` cancels; dually below.

The chosen fillers are functorial: precomposing the square with a morphism of coalgebras
`h : c' ⟶ c` and postcomposing it with a morphism of algebras `k : a ⟶ a'` precomposes and
postcomposes the filler with `h.right` and `k.left` (`lift_comp_algHom`, `coalgHom_comp_lift`,
`lift_comp`), since `h.right ≫ s = s' ≫ E h` and `p ≫ k.left = E k ≫ p'` are the equations of
the morphisms.

The components of the (co)actions and of the equations of their morphisms are extracted with
`congrArg Arr.Hom.left` and `congrArg Arr.Hom.right`: the operations of `Arr B` are computed
componentwise by rules, as are the equations of objects and 1-cells of the AWFS.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B]

namespace AWFS

variable (A : AWFS B)

/-- The 2-comonad `L` of an AWFS. -/
abbrev L : TwoComonad (Arr B) :=
  A.toPreAWFS.toAWFSData.L

/-- The 2-monad `R` of an AWFS. -/
abbrev R : TwoMonad (Arr B) :=
  A.toPreAWFS.toAWFSData.R

variable {A}

/-! ## The components of coalgebras and algebras -/

/-- The equation of the square `L m`, `m.left ≫ L g = L f ≫ E m`. The rules for the components of
`L m` turn the equation of `L m` itself into a tautology, so it is restated here with `m.left`. -/
theorem lMap_naturality {f g : Arr B} (m : f ⟶ g) :
    m.left ≫ (A.L.T.obj g).hom = (A.L.T.obj f).hom ≫ (A.R.T.map m).left :=
  (congrArg (· ≫ (A.L.T.obj g).hom) (A.toPreAWFS.L_map_left m)).symm.trans (A.L.T.map m).w

/-- The equation of the square `R m`, `E m ≫ R g = R f ≫ m.right`. -/
theorem rMap_naturality {f g : Arr B} (m : f ⟶ g) :
    (A.R.T.map m).left ≫ (A.R.T.obj g).hom = (A.R.T.obj f).hom ≫ m.right :=
  (A.R.T.map m).w.trans (congrArg ((A.R.T.obj f).hom ≫ ·) (A.toPreAWFS.R_map_right m))

section Components

variable (c : A.L.Coalg) (a : A.R.Alg)

/-- The coaction of an `L`-coalgebra is the identity on the domain, by the counit law. -/
theorem coact_left : c.coact.left = 𝟙 c.obj.dom := by
  kernel_exact congrArg Arr.Hom.left c.counit

/-- The nontrivial component `s` of the coaction is a section of `R f`, by the counit law. -/
theorem coact_right_comp : c.coact.right ≫ (A.R.T.obj c.obj).hom = 𝟙 c.obj.cod := by
  kernel_exact congrArg Arr.Hom.right c.counit

/-- `f ≫ s = L f`: the equation of the coaction square. -/
theorem hom_comp_coact_right : c.obj.hom ≫ c.coact.right = (A.L.T.obj c.obj).hom := by
  have h : c.coact.left ≫ (A.L.T.obj c.obj).hom = c.obj.hom ≫ c.coact.right := c.coact.w
  rw [coact_left] at h
  kernel_exact h.symm

/-- The action of an `R`-algebra is the identity on the codomain, by the unit law. -/
theorem act_right : a.act.right = 𝟙 a.obj.cod := by
  kernel_exact congrArg Arr.Hom.right a.unit

/-- The nontrivial component `p` of the action is a retraction of `L g`, by the unit law. -/
theorem lMap_comp_act_left : (A.L.T.obj a.obj).hom ≫ a.act.left = 𝟙 a.obj.dom := by
  kernel_exact congrArg Arr.Hom.left a.unit

/-- `p ≫ g = R g`: the equation of the action square. -/
theorem act_left_comp_hom : a.act.left ≫ a.obj.hom = (A.R.T.obj a.obj).hom := by
  have h : a.act.left ≫ a.obj.hom = (A.R.T.obj a.obj).hom ≫ a.act.right := a.act.w
  rw [act_right] at h
  kernel_exact h

/-- The equation of a morphism of `L`-coalgebras, on the codomains: `h.right ≫ s = s' ≫ E h`. -/
theorem coalgHom_right_comp {c c' : A.L.Coalg} (h : c' ⟶ c) :
    h.hom.right ≫ c.coact.right = c'.coact.right ≫ (A.R.T.map h.hom).left := by
  kernel_exact congrArg Arr.Hom.right h.w

/-- The equation of a morphism of `R`-algebras, on the domains: `p ≫ k.left = E k ≫ p'`. -/
theorem act_left_comp_algHom {a a' : A.R.Alg} (k : a ⟶ a') :
    a.act.left ≫ k.hom.left = (A.R.T.map k.hom).left ≫ a'.act.left := by
  kernel_exact congrArg Arr.Hom.left k.w

end Components

/-! ## The chosen fillers -/

/-- **The chosen filler** of a square `m : f ⟶ g` from an `L`-coalgebra to an `R`-algebra: the
composite `s ≫ E m ≫ p` of the nontrivial components of the coaction and of the action with the
middle map of the factorization of `m`. -/
def lift (c : A.L.Coalg) (a : A.R.Alg) (m : c.obj ⟶ a.obj) : c.obj.cod ⟶ a.obj.dom :=
  c.coact.right ≫ (A.R.T.map m).left ≫ a.act.left

variable (c : A.L.Coalg) (a : A.R.Alg) (m : c.obj ⟶ a.obj)

/-- **The upper triangle**: `f ≫ lift c a m = m.left`. -/
theorem hom_comp_lift : c.obj.hom ≫ lift c a m = m.left := by
  have h₁ : c.obj.hom ≫ c.coact.right ≫ (A.R.T.map m).left ≫ a.act.left =
      (A.L.T.obj c.obj).hom ≫ (A.R.T.map m).left ≫ a.act.left := by
    kernel_exact congrArg (· ≫ (A.R.T.map m).left ≫ a.act.left) (hom_comp_coact_right c)
  have h₂ : (A.L.T.obj c.obj).hom ≫ (A.R.T.map m).left ≫ a.act.left =
      m.left ≫ (A.L.T.obj a.obj).hom ≫ a.act.left := by
    kernel_exact (congrArg (· ≫ a.act.left) (lMap_naturality m)).symm
  have h₃ : m.left ≫ (A.L.T.obj a.obj).hom ≫ a.act.left = m.left := by
    kernel_exact congrArg (m.left ≫ ·) (lMap_comp_act_left a)
  kernel_exact h₁.trans (h₂.trans h₃)

/-- **The lower triangle**: `lift c a m ≫ g = m.right`. -/
theorem lift_comp_hom : lift c a m ≫ a.obj.hom = m.right := by
  have h₁ : c.coact.right ≫ (A.R.T.map m).left ≫ a.act.left ≫ a.obj.hom =
      c.coact.right ≫ (A.R.T.map m).left ≫ (A.R.T.obj a.obj).hom := by
    kernel_exact congrArg (fun k => c.coact.right ≫ (A.R.T.map m).left ≫ k)
      (act_left_comp_hom a)
  have h₂ : c.coact.right ≫ (A.R.T.obj c.obj).hom ≫ m.right = m.right := by
    kernel_exact congrArg (· ≫ m.right) (coact_right_comp c)
  kernel_exact h₁.trans h₂

/-- The upper triangle, followed by a 1-cell. -/
theorem hom_comp_lift_assoc {z : B} (k : a.obj.dom ⟶ z) :
    c.obj.hom ≫ lift c a m ≫ k = m.left ≫ k := by
  rw [← Category.assoc, hom_comp_lift]

/-- The lower triangle, followed by a 1-cell. -/
theorem lift_comp_hom_assoc {z : B} (k : a.obj.cod ⟶ z) :
    lift c a m ≫ a.obj.hom ≫ k = m.right ≫ k := by
  rw [← Category.assoc, lift_comp_hom]

/-! ## Functoriality -/

/-- **The chosen fillers are natural in the algebra**: postcomposing with a morphism of algebras
`k : a ⟶ a'` postcomposes the filler with `k.left`. -/
theorem lift_comp_algHom {a' : A.R.Alg} (k : a ⟶ a') :
    lift c a m ≫ k.hom.left = lift c a' (m ≫ k.hom) := by
  kernel_exact congrArg (c.coact.right ≫ (A.R.T.map m).left ≫ ·) (act_left_comp_algHom k)

/-- **The chosen fillers are natural in the coalgebra**: precomposing with a morphism of
coalgebras `h : c' ⟶ c` precomposes the filler with `h.right`. -/
theorem coalgHom_comp_lift {c' : A.L.Coalg} (h : c' ⟶ c) :
    h.hom.right ≫ lift c a m = lift c' a (h.hom ≫ m) := by
  kernel_exact congrArg (· ≫ (A.R.T.map m).left ≫ a.act.left) (coalgHom_right_comp h)

/-- **The chosen fillers are functorial**: for morphisms of coalgebras `h : c' ⟶ c` and of algebras
`k : a ⟶ a'`, the filler of `h ≫ m ≫ k` is `h.right ≫ lift c a m ≫ k.left`. -/
theorem lift_comp {c' : A.L.Coalg} {a' : A.R.Alg} (h : c' ⟶ c) (k : a ⟶ a') :
    lift c' a' (h.hom ≫ m ≫ k.hom) = h.hom.right ≫ lift c a m ≫ k.hom.left := by
  rw [lift_comp_algHom, coalgHom_comp_lift]

/-- **Functoriality, for squares that agree**: if `h ≫ m = m' ≫ k`, the fillers of `m` and `m'`
are related by `h.right ≫ lift c a m = lift c' a' m' ≫ k.left`. This is the form used for stability
under substitution, where `m'` is the reindexing of `m`. -/
theorem coalgHom_comp_lift_eq {c' : A.L.Coalg} {a' : A.R.Alg} (h : c' ⟶ c) (k : a' ⟶ a)
    (m' : c'.obj ⟶ a'.obj) (e : h.hom ≫ m = m' ≫ k.hom) :
    h.hom.right ≫ lift c a m = lift c' a' m' ≫ k.hom.left := by
  rw [coalgHom_comp_lift, lift_comp_algHom, e]

end AWFS

end CategoryTheory.TwoCategory
