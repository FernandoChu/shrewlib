import Nfib.D2SFib.Category
import Nfib.Displayed.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# `Φ`: the dependent 2-sided Grothendieck construction

Milestone **M8** of `PLAN.md`. Given `F : ∫(Bᵈᵒ) ⥤ Cat`, we build a doubly displayed category
`D2SGC F` over `B` (Def. `def:D2SGC` of the paper), equip it with a `D2SFib` structure, and
assemble the whole thing into a functor `D2SGCFunctor : (B.dualOp.Total ⥤ Cat) ⥤ D2SFibCat B`.

The objects of `D2SGC F` over `b : B.Ob a` are the objects of `F.obj ⟨a, b⟩`, and a morphism over
`g : B.Hom α b b'` from `c` to `c'` is a morphism

`(F.map (dualHoriz α b)).obj c ⟶ (F.map (dualVert (B.factor g))).obj c'`

of `F.obj ⟨a', B.transp α b⟩`, exactly the paper's `hom_{C(a', B(α)b)}(C(α,id)c, C(id,β)c')`.

Since such a hom-type mentions two `F.map`s, all the coherence work is organized through an
auxiliary "two-sided hom" `D2SGC.GHom F u v c c'` (a hom `(F.map u).obj c ⟶ (F.map v).obj c'` for a
*pair* of `∫(Bᵈᵒ)`-morphisms with common codomain) together with three operations — `reindex`
(along equalities of `u`/`v`), `push` (along a further `k : z ⟶ t`) and `trans` (composition along
a shared middle datum). Composition in `D2SGC F` is built from these, and each coherence law
reduces to an equality of `∫(Bᵈᵒ)`-morphisms plus the `≍`-algebra of the three operations.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A} [SplitOpfib B]

namespace D2SGC

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃})

noncomputable section

/-! ### `F` as a (strict) reindexing calculus -/

/-- `F` applied to a morphism of `∫(Bᵈᵒ)`, as an honest functor (rather than a `Cat.Hom`). -/
def fmap {x y : B.dualOp.Total} (u : x ⟶ y) : F.obj x ⥤ F.obj y := (F.map u).toFunctor

@[simp]
theorem fmap_id (x : B.dualOp.Total) : fmap F (𝟙 x) = 𝟭 (F.obj x) := by
  rw [fmap, F.map_id, Cat.Hom.id_toFunctor]

@[simp]
theorem fmap_comp {x y z : B.dualOp.Total} (u : x ⟶ y) (v : y ⟶ z) :
    fmap F (u ≫ v) = fmap F u ⋙ fmap F v := by
  rw [fmap, F.map_comp, Cat.Hom.comp_toFunctor]; rfl

/-- `F.map` of a composite, read off on objects. -/
theorem fmap_obj_comp {x y z : B.dualOp.Total} (u : x ⟶ y) (v : y ⟶ z) (c : F.obj x) :
    (fmap F (u ≫ v)).obj c = (fmap F v).obj ((fmap F u).obj c) := by rw [fmap_comp]; rfl

/-- Reindexing along an equality of `∫(Bᵈᵒ)`-morphisms, on objects. -/
theorem fmap_congr_obj {x y : B.dualOp.Total} {u v : x ⟶ y} (h : u = v) (c : F.obj x) :
    (fmap F u).obj c = (fmap F v).obj c := by rw [h]

@[simp]
theorem fmap_id_obj (x : B.dualOp.Total) (c : F.obj x) : (fmap F (𝟙 x)).obj c = c := by
  rw [fmap_id]; rfl

theorem fmap_id_map_heq (x : B.dualOp.Total) {c c' : F.obj x} (θ : c ⟶ c') :
    (fmap F (𝟙 x)).map θ ≍ θ := by
  rw [Functor.congr_hom (fmap_id F x) θ]; simp

/-- `F.map` of an `eqToHom` of `∫(Bᵈᵒ)` acts trivially on objects. -/
theorem fmap_eqToHom_obj_heq {x y : B.dualOp.Total} (h : x = y) (c : F.obj x) :
    (fmap F (eqToHom h)).obj c ≍ c := by subst h; simp

/-- `F.map` of an `eqToHom` of `∫(Bᵈᵒ)` acts trivially on morphisms. -/
theorem fmap_eqToHom_map_heq {x y : B.dualOp.Total} (h : x = y) {c c' : F.obj x} (θ : c ⟶ c') :
    (fmap F (eqToHom h)).map θ ≍ θ := by
  subst h
  refine HEq.trans ?_ (fmap_id_map_heq F x θ)
  rw [eqToHom_refl]

/-- `fmap` is a congruence for `≍` of morphisms with propositionally equal endpoints. -/
theorem fmap_map_heq {x y : B.dualOp.Total} (u : x ⟶ y) {c c' d d' : F.obj x}
    (hc : c = d) (hc' : c' = d') {θ : c ⟶ c'} {ψ : d ⟶ d'} (h : θ ≍ ψ) :
    (fmap F u).map θ ≍ (fmap F u).map ψ := by
  subst hc; subst hc'; obtain rfl := eq_of_heq h; rfl

/-- Fully general congruence for `fmap` on morphisms: the indexing morphism, its endpoints and the
morphism itself may all vary up to `≍`. This is the workhorse for comparing `fmap`-images that live
in propositionally — but not definitionally — equal ambient fibers. -/
theorem fmap_map_heq_of_heq {x x₂ y y₂ : B.dualOp.Total} {v : x ⟶ y} {v₂ : x₂ ⟶ y₂}
    (hx : x = x₂) (hy : y = y₂) (hv : v ≍ v₂) {c c' : F.obj x} {d d' : F.obj x₂}
    (hc : c ≍ d) (hc' : c' ≍ d') {ξ : c ⟶ c'} {ξ₂ : d ⟶ d'} (h : ξ ≍ ξ₂) :
    (fmap F v).map ξ ≍ (fmap F v₂).map ξ₂ := by
  subst hx; subst hy
  obtain rfl := eq_of_heq hv
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hc'
  obtain rfl := eq_of_heq h
  rfl

/-- Two successive `fmap`-images agree with the `fmap`-image along the composite. -/
theorem fmap_map_map_heq {x y z : B.dualOp.Total} (u : x ⟶ y) (v : y ⟶ z) {c c' : F.obj x}
    (θ : c ⟶ c') : (fmap F v).map ((fmap F u).map θ) ≍ (fmap F (u ≫ v)).map θ := by
  rw [Functor.congr_hom (fmap_comp F u v) θ]; simp

/-! ### Two-sided homs -/

/-- A *two-sided hom*: a morphism of `F.obj z` from the `u`-image of `c` to the `v`-image of `c'`,
for a pair of `∫(Bᵈᵒ)`-morphisms `u : x ⟶ z`, `v : y ⟶ z` with common codomain. This is the shape
of every hom-type of `D2SGC F`. -/
def GHom {x y z : B.dualOp.Total} (u : x ⟶ z) (v : y ⟶ z) (c : F.obj x) (c' : F.obj y) : Type v₃ :=
  (fmap F u).obj c ⟶ (fmap F v).obj c'

namespace GHom

variable {F}

/-- The two-sided hom determined by an equality of the two images. Every `eqToHom`-shaped
two-sided hom (in particular the identity of `D2SGC F`) is of this form. -/
def ofEq {x y z : B.dualOp.Total} {u : x ⟶ z} {v : y ⟶ z} {c : F.obj x} {c' : F.obj y}
    (h : (fmap F u).obj c = (fmap F v).obj c') : GHom F u v c c' := eqToHom h

/-- Composition of two-sided homs along a shared middle datum, which need only agree
*propositionally* (the discrepancy is absorbed by an `eqToHom`). -/
def trans {x y z w : B.dualOp.Total} {u : x ⟶ w} {v v' : y ⟶ w} {t : z ⟶ w} {c : F.obj x}
    {c' : F.obj y} {c'' : F.obj z} (θ : GHom F u v c c') (h : v = v')
    (θ' : GHom F v' t c' c'') : GHom F u t c c'' :=
  (θ : (fmap F u).obj c ⟶ (fmap F v).obj c') ≫ eqToHom (fmap_congr_obj F h c')
    ≫ (θ' : (fmap F v').obj c' ⟶ (fmap F t).obj c'')

/-- Reindexing a two-sided hom along equalities of its indexing morphisms. -/
def reindex {x y z : B.dualOp.Total} {u u₂ : x ⟶ z} {v v₂ : y ⟶ z} {c : F.obj x} {c' : F.obj y}
    (θ : GHom F u v c c') (hu : u = u₂) (hv : v = v₂) : GHom F u₂ v₂ c c' :=
  eqToHom (fmap_congr_obj F hu.symm c) ≫ (θ : (fmap F u).obj c ⟶ (fmap F v).obj c')
    ≫ eqToHom (fmap_congr_obj F hv c')

/-- Pushing a two-sided hom forward along `k : z ⟶ t`. -/
def push {x y z t : B.dualOp.Total} {u : x ⟶ z} {v : y ⟶ z} {c : F.obj x} {c' : F.obj y}
    (θ : GHom F u v c c') (k : z ⟶ t) : GHom F (u ≫ k) (v ≫ k) c c' :=
  eqToHom (fmap_obj_comp F u k c)
    ≫ (fmap F k).map (θ : (fmap F u).obj c ⟶ (fmap F v).obj c')
    ≫ eqToHom (fmap_obj_comp F v k c').symm

section Lemmas

variable {x y z t s : B.dualOp.Total} {u u₂ : x ⟶ z} {v v₂ : y ⟶ z} {c : F.obj x} {c' : F.obj y}

theorem reindex_heq (θ : GHom F u v c c') (hu : u = u₂) (hv : v = v₂) : θ.reindex hu hv ≍ θ := by
  subst hu; subst hv; simp [reindex]

theorem push_heq_map (θ : GHom F u v c c') (k : z ⟶ t) :
    θ.push k ≍ (fmap F k).map (θ : (fmap F u).obj c ⟶ (fmap F v).obj c') := by
  simp only [push]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- `push` along an `eqToHom` is heterogeneously trivial. -/
theorem push_eqToHom_heq (θ : GHom F u v c c') (h : z = t) : θ.push (eqToHom h) ≍ θ :=
  (θ.push_heq_map (eqToHom h)).trans (fmap_eqToHom_map_heq F h _)

/-- `push` along any morphism that happens to be an `eqToHom` is heterogeneously trivial. -/
theorem push_heq_of_eq_eqToHom (θ : GHom F u v c c') {k : z ⟶ t} (h : z = t)
    (hk : k = eqToHom h) : θ.push k ≍ θ := by subst hk; exact θ.push_eqToHom_heq h

/-- `push` is a congruence for `≍`. -/
theorem push_heq {u' : x ⟶ z} {v' : y ⟶ z} {θ : GHom F u v c c'} {θ' : GHom F u' v' c c'}
    {k k' : z ⟶ t} (hu : u = u') (hv : v = v') (hk : k = k') (h : θ ≍ θ') :
    θ.push k ≍ θ'.push k' := by
  subst hu; subst hv; subst hk; obtain rfl := eq_of_heq h; rfl

/-- `trans` is a congruence for `≍`. -/
theorem trans_heq {w : B.dualOp.Total} {c'' : F.obj t} {u₁ u₁' : x ⟶ w}
    {v₁ v₁' v₂ v₂' : y ⟶ w} {r r' : t ⟶ w}
    {θ : GHom F u₁ v₁ c c'} {θ₂ : GHom F u₁' v₂ c c'}
    {ψ : GHom F v₁' r c' c''} {ψ₂ : GHom F v₂' r' c' c''}
    {h : v₁ = v₁'} {h₂ : v₂ = v₂'}
    (hu : u₁ = u₁') (hv : v₁ = v₂) (hr : r = r') (hθ : θ ≍ θ₂) (hψ : ψ ≍ ψ₂) :
    θ.trans h ψ ≍ θ₂.trans h₂ ψ₂ := by
  subst hu; subst hv; subst hr
  obtain rfl := h.symm.trans h₂
  obtain rfl := eq_of_heq hθ; obtain rfl := eq_of_heq hψ; rfl

/-- `trans` is a congruence for `≍` *across a change of ambient fiber*. -/
theorem trans_heq' {w w₂ : B.dualOp.Total} {c'' : F.obj t} {u₁ : x ⟶ w} {v₁ v₁' : y ⟶ w}
    {r : t ⟶ w} {u₂ : x ⟶ w₂} {v₂ v₂' : y ⟶ w₂} {r₂ : t ⟶ w₂}
    {θ : GHom F u₁ v₁ c c'} {θ₂ : GHom F u₂ v₂ c c'}
    {ψ : GHom F v₁' r c' c''} {ψ₂ : GHom F v₂' r₂ c' c''}
    {h : v₁ = v₁'} {h₂ : v₂ = v₂'}
    (hw : w = w₂) (hu : u₁ ≍ u₂) (hv : v₁ ≍ v₂) (hr : r ≍ r₂) (hθ : θ ≍ θ₂) (hψ : ψ ≍ ψ₂) :
    θ.trans h ψ ≍ θ₂.trans h₂ ψ₂ := by
  subst hw
  obtain rfl := eq_of_heq hu
  obtain rfl := eq_of_heq hv
  obtain rfl := eq_of_heq hr
  obtain rfl := h.symm.trans h₂
  obtain rfl := eq_of_heq hθ
  obtain rfl := eq_of_heq hψ
  rfl

/-- `trans` with an `ofEq` on the left is heterogeneously trivial. -/
theorem ofEq_trans_heq {w : B.dualOp.Total} {c'' : F.obj t} {u₁ : x ⟶ w} {v₁ v₁' : y ⟶ w}
    {r : t ⟶ w} (h₁ : (fmap F u₁).obj c = (fmap F v₁).obj c') (h : v₁ = v₁')
    (ψ : GHom F v₁' r c' c'') : (ofEq h₁).trans h ψ ≍ ψ := by
  simp only [trans, ofEq]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)

/-- `trans` with an `ofEq` on the right is heterogeneously trivial. -/
theorem trans_ofEq_heq {w : B.dualOp.Total} {c'' : F.obj t} {u₁ : x ⟶ w} {v₁ v₁' : y ⟶ w}
    {r : t ⟶ w} (θ : GHom F u₁ v₁ c c') (h : v₁ = v₁')
    (h₁ : (fmap F v₁').obj c' = (fmap F r).obj c'') : θ.trans h (ofEq h₁) ≍ θ := by
  simp only [trans, ofEq, eqToHom_trans]
  exact comp_eqToHom_heq _ _

/-- `push` of an `ofEq` two-sided hom is again an `ofEq`. -/
theorem ofEq_push (h₁ : (fmap F u).obj c = (fmap F v).obj c') (k : z ⟶ t) :
    (ofEq h₁).push k = ofEq (by rw [fmap_obj_comp, fmap_obj_comp, h₁]) := by
  simp [push, ofEq, eqToHom_map]

/-- Any two `ofEq` two-sided homs with heterogeneously equal sources are heterogeneously equal. -/
theorem ofEq_heq {x₂ y₂ z₂ : B.dualOp.Total} {u₂ : x₂ ⟶ z₂} {v₂ : y₂ ⟶ z₂} {c₂ : F.obj x₂}
    {c'₂ : F.obj y₂} (h : (fmap F u).obj c = (fmap F v).obj c')
    (h₂ : (fmap F u₂).obj c₂ = (fmap F v₂).obj c'₂) (hz : z = z₂)
    (hs : (fmap F u).obj c ≍ (fmap F u₂).obj c₂) :
    (ofEq h : GHom F u v c c') ≍ (ofEq h₂ : GHom F u₂ v₂ c₂ c'₂) := by
  subst hz
  simp only [ofEq]
  refine (eqToHom_heq_id_dom _ _ h).trans (HEq.trans ?_ (eqToHom_heq_id_dom _ _ h₂).symm)
  rw [eq_of_heq hs]

/-- Two `GHom` types with a common ambient fiber and heterogeneously equal endpoints agree. -/
theorem type_eq {x₂ y₂ z₂ : B.dualOp.Total} {u₂ : x₂ ⟶ z₂} {v₂ : y₂ ⟶ z₂} {c₂ : F.obj x₂}
    {c'₂ : F.obj y₂} (hz : z = z₂) (hdom : (fmap F u).obj c ≍ (fmap F u₂).obj c₂)
    (hcod : (fmap F v).obj c' ≍ (fmap F v₂).obj c'₂) :
    GHom F u v c c' = GHom F u₂ v₂ c₂ c'₂ := by
  subst hz
  simp only [GHom]
  rw [eq_of_heq hdom, eq_of_heq hcod]

/-- `push` of a composite is the composite of `push`es. -/
theorem push_push_heq (θ : GHom F u v c c') (k : z ⟶ t) (l : t ⟶ s) :
    (θ.push k).push l ≍ θ.push (k ≫ l) :=
  ((θ.push k).push_heq_map l).trans <|
    (fmap_map_heq F l (fmap_obj_comp F u k c) (fmap_obj_comp F v k c')
      ((θ.push_heq_map k).trans HEq.rfl) |>.trans
      (fmap_map_map_heq F k l _)).trans (θ.push_heq_map (k ≫ l)).symm

/-- `push` distributes over `trans`. -/
theorem push_trans {w : B.dualOp.Total} {c'' : F.obj w} {v' : y ⟶ z} {r : w ⟶ z}
    (θ : GHom F u v c c') (h : v = v') (ψ : GHom F v' r c' c'') (k : z ⟶ t) :
    (θ.trans h ψ).push k = (θ.push k).trans (by rw [h]) (ψ.push k) := by
  simp [push, trans, Functor.map_comp, eqToHom_map]

/-- `trans` is associative. -/
theorem trans_assoc {w w' : B.dualOp.Total} {c'' : F.obj w} {c''' : F.obj w'} {v' : y ⟶ z}
    {r r' : w ⟶ z} {s : w' ⟶ z} (θ : GHom F u v c c') (h : v = v') (ψ : GHom F v' r c' c'')
    (h' : r = r') (χ : GHom F r' s c'' c''') :
    (θ.trans h ψ).trans h' χ = θ.trans h (ψ.trans h' χ) := by simp [trans]

end Lemmas

end GHom

/-! ### The comparison morphisms of `∫(Bᵈᵒ)`

Composition in `D2SGC` pushes the two factors into the common ambient fiber
`F.obj ⟨a'', B.transp (α ≫ α') b⟩` along the two morphisms `horizComp` and `vertComp` of
`∫(Bᵈᵒ)`. The five lemmas below are the whole geometric content of `D2SGC`'s coherence laws. -/

section Comparison

variable {a a' a'' a''' : A}

/-- The comparison morphism of `∫(Bᵈᵒ)` used for the "horizontal" half of composition. -/
def horizComp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    B.dualOp.tot (B.transp α b) ⟶ B.dualOp.tot (B.transp (α ≫ α') b) :=
  dualHoriz α' (B.transp α b) ≫ dualVert (eqToHom (B.transp_comp α α' b))

/-- The comparison morphism of `∫(Bᵈᵒ)` used for the "vertical" half of composition. -/
def vertComp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    (β : (B.transp α b : B.Fiber a') ⟶ b') :
    B.dualOp.tot (B.transp α' b') ⟶ B.dualOp.tot (B.transp (α ≫ α') b) :=
  dualVert (eqToHom (B.transp_comp α α' b) ≫ B.transpMap α' β)

/-- The comparison morphism of `∫(Bᵈᵒ)` mediating the two bracketings of a triple base composite.
It *is* an `eqToHom` (`assocCmp_eq_eqToHom`), but presenting it as a `dualVert` keeps it inside the
`dualHoriz`/`dualVert` calculus that `simp` can compute with. -/
def assocCmp (α : a ⟶ a') (α' : a' ⟶ a'') (α'' : a'' ⟶ a''') (b : B.Ob a) :
    B.dualOp.tot (B.transp (α ≫ α' ≫ α'') b)
      ⟶ B.dualOp.tot (B.transp ((α ≫ α') ≫ α'') b) :=
  dualVert (eqToHom (congrArg (fun m : a ⟶ a''' => B.transp m b) (Category.assoc α α' α'')))

theorem assocCmp_eq_eqToHom (α : a ⟶ a') (α' : a' ⟶ a'') (α'' : a'' ⟶ a''') (b : B.Ob a) :
    assocCmp α α' α'' b
      = eqToHom (congrArg (fun m : a ⟶ a''' => B.dualOp.tot (B.transp m b))
          (Category.assoc α α' α'').symm) :=
  dualVert_eqToHom _

/-- The chosen horizontal morphism absorbs `horizComp` (splitness of `∫(Bᵈᵒ)`). -/
@[reassoc]
theorem dualHoriz_comp_horizComp (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    dualHoriz α b ≫ horizComp α α' b = dualHoriz (α ≫ α') b :=
  dualHoriz_comp α α' b

/-- Pushing a vertical morphism past `horizComp` produces `vertComp`. -/
@[reassoc]
theorem dualVert_comp_horizComp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} {b' : B.Ob a'}
    (β : (B.transp α b : B.Fiber a') ⟶ b') :
    dualVert β ≫ horizComp α α' b = dualHoriz α' b' ≫ vertComp α α' β := by
  rw [horizComp, vertComp, dualVert_comp, ← Category.assoc, dualVert_comp_dualHoriz,
    Category.assoc]

/-- `vertComp` absorbs the next vertical morphism, producing the factorization of the composite. -/
@[reassoc]
theorem dualVert_comp_vertComp {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') :
    dualVert (B.factor g') ≫ vertComp α α' (B.factor g) = dualVert (B.factor (g ≫ᵈ g')) := by
  simp only [vertComp, B.factor_comp g g', dualVert_comp, Category.assoc]

/-- Associativity of the horizontal comparison morphisms. -/
theorem horizComp_comp_horizComp (α : a ⟶ a') (α' : a' ⟶ a'') (α'' : a'' ⟶ a''') (b : B.Ob a) :
    horizComp α α' b ≫ horizComp (α ≫ α') α'' b
      = horizComp α (α' ≫ α'') b ≫ assocCmp α α' α'' b :=
  dualOp_hom_ext (by simp [horizComp, assocCmp])
    (by simp [horizComp, assocCmp, transpMap_id_vert])

/-- Compatibility of the vertical and horizontal comparison morphisms. -/
theorem vertComp_comp_horizComp (α : a ⟶ a') (α' : a' ⟶ a'') (α'' : a'' ⟶ a''') {b : B.Ob a}
    {b' : B.Ob a'} (β : (B.transp α b : B.Fiber a') ⟶ b') :
    vertComp α α' β ≫ horizComp (α ≫ α') α'' b
      = (horizComp α' α'' b' ≫ vertComp α (α' ≫ α'') β) ≫ assocCmp α α' α'' b :=
  dualOp_hom_ext (by simp [horizComp, vertComp, assocCmp])
    (by simp [horizComp, vertComp, assocCmp, transpMap_id, transpMap_id_vert,
      transpMap_comp_vert, transpMap_comp])

/-- Associativity of the vertical comparison morphisms. -/
theorem vertComp_comp_vertComp {α : a ⟶ a'} {α' : a' ⟶ a''} {α'' : a'' ⟶ a'''} {b : B.Ob a}
    {b' : B.Ob a'} {b'' : B.Ob a''} (g : b ⟶[α] b') (g' : b' ⟶[α'] b'') :
    vertComp (α ≫ α') α'' (B.factor (g ≫ᵈ g'))
      = (vertComp α' α'' (B.factor g') ≫ vertComp α (α' ≫ α'') (B.factor g))
          ≫ assocCmp α α' α'' b :=
  dualOp_hom_ext (by simp [vertComp, assocCmp])
    (by simp [vertComp, assocCmp, B.factor_comp g g', transpMap_id,
      transpMap_comp_vert, transpMap_comp])

/-- The vertical comparison morphism for an identity first factor is an `eqToHom`. -/
theorem vertComp_factor_id (α : a ⟶ a') (b : B.Ob a) :
    vertComp (𝟙 a) α (B.factor (B.id b))
      = eqToHom (congrArg (fun m : a ⟶ a' => B.dualOp.tot (B.transp m b))
          (Category.id_comp α).symm) := by
  have h : eqToHom (B.transp_comp (𝟙 a) α b) ≫ B.transpMap α (B.factor (B.id b))
      = eqToHom (congrArg (fun m : a ⟶ a' => B.transp m b) (Category.id_comp α)) := by simp
  rw [vertComp, h]
  exact dualVert_eqToHom _

/-- The horizontal comparison morphism for an identity second factor is an `eqToHom`. -/
theorem horizComp_id_right (α : a ⟶ a') (b : B.Ob a) :
    horizComp α (𝟙 a') b
      = eqToHom (congrArg (fun m : a ⟶ a' => B.dualOp.tot (B.transp m b))
          (Category.comp_id α).symm) := by
  have h : eqToHom (B.transp_comp α (𝟙 a') b) ≫ eqToHom (B.transp_id (B.transp α b))
      = eqToHom (congrArg (fun m : a ⟶ a' => B.transp m b) (Category.comp_id α)) := by simp
  rw [horizComp, dualHoriz_id, ← dualVert_comp, h]
  exact dualVert_eqToHom _

end Comparison

/-! ### The doubly displayed category `D2SGC F` -/

section Construction

variable {a a' a'' a''' : A}

/-- Objects of `D2SGC F` over `b : B.Ob a`. -/
abbrev Ob (b : B.Ob a) : Type u₃ := F.obj (B.dualOp.tot b)

/-- Morphisms of `D2SGC F` over `g : B.Hom α b b'`: the paper's
`hom_{C(a', B(α)b)}(C(α,id)c, C(id,β)c')`. -/
abbrev Hom {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[α] b')
    (c : Ob F b) (c' : Ob F b') : Type v₃ :=
  GHom F (dualHoriz α b) (dualVert (B.factor g)) c c'

/-- Over an identity base morphism, the chosen horizontal morphism of `∫(Bᵈᵒ)` coincides with the
vertical morphism given by the factorization of `B.id b`. -/
theorem dualHoriz_id_eq (b : B.Ob a) : dualHoriz (𝟙 a) b = dualVert (B.factor (B.id b)) := by
  rw [dualHoriz_id, B.factor_id]

/-- The identity of `D2SGC F`: an `eqToHom` conjugate of `𝟙 c`. -/
def id' {b : B.Ob a} (c : Ob F b) : Hom F (B.id b) c c :=
  GHom.ofEq (fmap_congr_obj F (dualHoriz_id_eq b) c)

/-- Composition in `D2SGC F` (the paper's `γ ≔ C(α',id)θ ≫ C(id, B(α')β)θ'`): push both factors
into the fiber over `⟨a'', B.transp (α ≫ α') b⟩` and compose there. -/
def comp' {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}
    {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'') : Hom F (g ≫ᵈ g') c c'' :=
  ((θ.push (horizComp α α' b)).trans (dualVert_comp_horizComp α α' (B.factor g))
      (θ'.push (vertComp α α' (B.factor g)))).reindex
    (dualHoriz_comp_horizComp α α' b) (dualVert_comp_vertComp g g')

variable {α : a ⟶ a'} {α' : a' ⟶ a''} {α'' : a'' ⟶ a'''} {b : B.Ob a} {b' : B.Ob a'}
  {b'' : B.Ob a''} {b''' : B.Ob a'''} {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''}
  {g'' : b'' ⟶[α''] b'''}

/-- `comp'` in `push`/`trans` normal form. -/
theorem comp'_heq {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''} (θ : Hom F g c c')
    (θ' : Hom F g' c' c'') :
    comp' F θ θ' ≍ (θ.push (horizComp α α' b)).trans
      (dualVert_comp_horizComp α α' (B.factor g)) (θ'.push (vertComp α α' (B.factor g))) :=
  GHom.reindex_heq _ _ _

/-- `push` of a composite, in normal form. -/
theorem push_comp'_heq {t : B.dualOp.Total} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'')
    (k : B.dualOp.tot (B.transp (α ≫ α') b) ⟶ t) :
    (comp' F θ θ').push k
      ≍ (θ.push (horizComp α α' b ≫ k)).trans
        (dualVert_comp_horizComp_assoc α α' (B.factor g) k)
        (θ'.push (vertComp α α' (B.factor g) ≫ k)) := by
  refine (GHom.push_heq (dualHoriz_comp_horizComp α α' b).symm
    (dualVert_comp_vertComp g g').symm rfl (comp'_heq F θ θ')).trans ?_
  rw [GHom.push_trans]
  exact GHom.trans_heq (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
    (GHom.push_push_heq _ _ _) (GHom.push_push_heq _ _ _)

theorem id_comp'' {c : Ob F b} {c' : Ob F b'} (θ : Hom F g c c') :
    comp' F (id' F c) θ ≍ θ := by
  refine (comp'_heq F (id' F c) θ).trans ?_
  rw [id', GHom.ofEq_push]
  refine (GHom.ofEq_trans_heq _ _ _).trans ?_
  exact θ.push_heq_of_eq_eqToHom _ (vertComp_factor_id α b)

theorem comp_id'' {c : Ob F b} {c' : Ob F b'} (θ : Hom F g c c') :
    comp' F θ (id' F c') ≍ θ := by
  refine (comp'_heq F θ (id' F c')).trans ?_
  rw [id', GHom.ofEq_push]
  refine (GHom.trans_ofEq_heq _ _ _).trans ?_
  exact θ.push_heq_of_eq_eqToHom _ (horizComp_id_right α b)

/-- The normal form of a triple composite: three factors pushed into a common ambient fiber and
composed there. Both bracketings of `comp'` reduce to this shape. -/
def tripleNF {t : B.dualOp.Total} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''} {c''' : Ob F b'''}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'') (θ'' : Hom F g'' c'' c''')
    (k : B.dualOp.tot (B.transp α b) ⟶ t) (l : B.dualOp.tot (B.transp α' b') ⟶ t)
    (r : B.dualOp.tot (B.transp α'' b'') ⟶ t)
    (h₁ : dualVert (B.factor g) ≫ k = dualHoriz α' b' ≫ l)
    (h₂ : dualVert (B.factor g') ≫ l = dualHoriz α'' b'' ≫ r) :
    GHom F (dualHoriz α b ≫ k) (dualVert (B.factor g'') ≫ r) c c''' :=
  (θ.push k).trans h₁ ((θ'.push l).trans h₂ (θ''.push r))

theorem tripleNF_push {t s : B.dualOp.Total} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    {c''' : Ob F b'''} (θ : Hom F g c c') (θ' : Hom F g' c' c'') (θ'' : Hom F g'' c'' c''')
    {k : B.dualOp.tot (B.transp α b) ⟶ t} {l : B.dualOp.tot (B.transp α' b') ⟶ t}
    {r : B.dualOp.tot (B.transp α'' b'') ⟶ t} (h₁ h₂) (e : t ⟶ s) {h₁' h₂'} :
    (tripleNF F θ θ' θ'' k l r h₁ h₂).push e
      ≍ tripleNF F θ θ' θ'' (k ≫ e) (l ≫ e) (r ≫ e) h₁' h₂' := by
  simp only [tripleNF]
  rw [GHom.push_trans, GHom.push_trans]
  exact GHom.trans_heq (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
    (GHom.push_push_heq _ _ _)
    (GHom.trans_heq (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
      (GHom.push_push_heq _ _ _) (GHom.push_push_heq _ _ _))

/-- Transport of a triple normal form along the three comparison identities: if the three ambient
morphisms of one normal form factor through those of another followed by a common `eqToHom`, the two
normal forms are heterogeneously equal. This is the single step that turns associativity of `∫(Bᵈᵒ)`
into associativity of `D2SGC F`. -/
theorem tripleNF_assoc {t s : B.dualOp.Total} {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    {c''' : Ob F b'''} (θ : Hom F g c c') (θ' : Hom F g' c' c'') (θ'' : Hom F g'' c'' c''')
    {k : B.dualOp.tot (B.transp α b) ⟶ s} {l : B.dualOp.tot (B.transp α' b') ⟶ s}
    {r : B.dualOp.tot (B.transp α'' b'') ⟶ s}
    {k₂ : B.dualOp.tot (B.transp α b) ⟶ t} {l₂ : B.dualOp.tot (B.transp α' b') ⟶ t}
    {r₂ : B.dualOp.tot (B.transp α'' b'') ⟶ t}
    (h₁ : dualVert (B.factor g) ≫ k = dualHoriz α' b' ≫ l)
    (h₂ : dualVert (B.factor g') ≫ l = dualHoriz α'' b'' ≫ r)
    (h₁₂ : dualVert (B.factor g) ≫ k₂ = dualHoriz α' b' ≫ l₂)
    (h₂₂ : dualVert (B.factor g') ≫ l₂ = dualHoriz α'' b'' ≫ r₂)
    {he : t = s} {e : t ⟶ s} (hee : e = eqToHom he)
    (hk : k = k₂ ≫ e) (hl : l = l₂ ≫ e) (hr : r = r₂ ≫ e) :
    tripleNF F θ θ' θ'' k l r h₁ h₂ ≍ tripleNF F θ θ' θ'' k₂ l₂ r₂ h₁₂ h₂₂ := by
  subst hk; subst hl; subst hr
  refine (tripleNF_push F θ θ' θ'' h₁₂ h₂₂ e).symm.trans ?_
  exact GHom.push_heq_of_eq_eqToHom _ he hee

theorem assoc'' {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''} {c''' : Ob F b'''}
    (θ : Hom F g c c') (θ' : Hom F g' c' c'') (θ'' : Hom F g'' c'' c''') :
    comp' F (comp' F θ θ') θ'' ≍ comp' F θ (comp' F θ' θ'') := by
  -- the left bracketing, in triple normal form
  have hleft : comp' F (comp' F θ θ') θ''
      ≍ tripleNF F θ θ' θ'' (horizComp α α' b ≫ horizComp (α ≫ α') α'' b)
        (vertComp α α' (B.factor g) ≫ horizComp (α ≫ α') α'' b)
        (vertComp (α ≫ α') α'' (B.factor (g ≫ᵈ g')))
        (dualVert_comp_horizComp_assoc α α' (B.factor g) (horizComp (α ≫ α') α'' b))
        ((dualVert_comp_vertComp_assoc g g' (horizComp (α ≫ α') α'' b)).trans
          (dualVert_comp_horizComp (α ≫ α') α'' (B.factor (g ≫ᵈ g')))) := by
    refine (comp'_heq F (comp' F θ θ') θ'').trans ?_
    simp only [tripleNF]
    rw [← GHom.trans_assoc]
    exact GHom.trans_heq
      (dualHoriz_comp_horizComp_assoc α α' b (horizComp (α ≫ α') α'' b)).symm
      (dualVert_comp_vertComp_assoc g g' (horizComp (α ≫ α') α'' b)).symm rfl
      (push_comp'_heq F θ θ' (horizComp (α ≫ α') α'' b)) HEq.rfl
  -- the right bracketing, in triple normal form
  have hright : comp' F θ (comp' F θ' θ'')
      ≍ tripleNF F θ θ' θ'' (horizComp α (α' ≫ α'') b)
        (horizComp α' α'' b' ≫ vertComp α (α' ≫ α'') (B.factor g))
        (vertComp α' α'' (B.factor g') ≫ vertComp α (α' ≫ α'') (B.factor g))
        ((dualVert_comp_horizComp α (α' ≫ α'') (B.factor g)).trans
          (dualHoriz_comp_horizComp_assoc α' α'' b'
            (vertComp α (α' ≫ α'') (B.factor g))).symm)
        (dualVert_comp_horizComp_assoc α' α'' (B.factor g')
          (vertComp α (α' ≫ α'') (B.factor g))) := by
    refine (comp'_heq F θ (comp' F θ' θ'')).trans ?_
    simp only [tripleNF]
    exact GHom.trans_heq rfl rfl
      (dualVert_comp_vertComp_assoc g' g'' (vertComp α (α' ≫ α'') (B.factor g))).symm HEq.rfl
      (push_comp'_heq F θ' θ'' (vertComp α (α' ≫ α'') (B.factor g)))
  refine hleft.trans (HEq.trans ?_ hright.symm)
  exact tripleNF_assoc F θ θ' θ'' _ _ _ _ (assocCmp_eq_eqToHom α α' α'' b)
    (horizComp_comp_horizComp α α' α'' b)
    (vertComp_comp_horizComp α α' α'' (B.factor g)) (vertComp_comp_vertComp g g')

/-! ### Congruence and `ofEq` calculus for `comp'` -/

/-- `comp'` is a congruence for `≍` when only the middle object varies. -/
theorem comp'_congr_mid {c : Ob F b} {m₁ m₂ : Ob F b'} {c'' : Ob F b''} (hm : m₁ = m₂)
    {θ₁ : Hom F g c m₁} {θ₂ : Hom F g c m₂} (hθ : θ₁ ≍ θ₂)
    {ψ₁ : Hom F g' m₁ c''} {ψ₂ : Hom F g' m₂ c''} (hψ : ψ₁ ≍ ψ₂) :
    comp' F θ₁ ψ₁ ≍ comp' F θ₂ ψ₂ := by
  subst hm; obtain rfl := eq_of_heq hθ; obtain rfl := eq_of_heq hψ; rfl

/-- The object equality underlying a composite of two `ofEq` morphisms. -/
theorem comp'_ofEq_obj {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    (h : (fmap F (dualHoriz α b)).obj c = (fmap F (dualVert (B.factor g))).obj c')
    (h' : (fmap F (dualHoriz α' b')).obj c' = (fmap F (dualVert (B.factor g'))).obj c'') :
    (fmap F (dualHoriz (α ≫ α') b)).obj c
      = (fmap F (dualVert (B.factor (g ≫ᵈ g')))).obj c'' := by
  rw [← dualHoriz_comp_horizComp α α' b, fmap_obj_comp, h, ← fmap_obj_comp,
    dualVert_comp_horizComp, fmap_obj_comp, h', ← fmap_obj_comp, dualVert_comp_vertComp]

/-- A composite of two `ofEq` morphisms is again an `ofEq` (any proof of the resulting equality
will do, `eqToHom`s being proof-irrelevant). -/
theorem comp'_ofEq {c : Ob F b} {c' : Ob F b'} {c'' : Ob F b''}
    (h : (fmap F (dualHoriz α b)).obj c = (fmap F (dualVert (B.factor g))).obj c')
    (h' : (fmap F (dualHoriz α' b')).obj c' = (fmap F (dualVert (B.factor g'))).obj c'')
    (h'' : (fmap F (dualHoriz (α ≫ α') b)).obj c
      = (fmap F (dualVert (B.factor (g ≫ᵈ g')))).obj c'') :
    comp' F (GHom.ofEq h) (GHom.ofEq h') = GHom.ofEq h'' := by
  simp only [comp', GHom.trans, GHom.reindex, GHom.push, GHom.ofEq, eqToHom_map, eqToHom_trans]

end Construction

/-! ### The `D2SFib` structure on `D2SGC F` -/

section Fib

variable {a a' a'' : A}

/-- `fmap` on objects is a congruence for `≍`. -/
theorem fmap_obj_heq {x z z₂ : B.dualOp.Total} {u : x ⟶ z} {u₂ : x ⟶ z₂} (hz : z = z₂)
    (hu : u ≍ u₂) {c c₂ : F.obj x} (hc : c = c₂) :
    (fmap F u).obj c ≍ (fmap F u₂).obj c₂ := by
  subst hz; obtain rfl := eq_of_heq hu; subst hc; rfl

omit [SplitOpfib B] in
/-- Transfer of a unique-existence statement along a map that is heterogeneously the identity. -/
theorem existsUnique_of_heq_id {T T' : Type v₃} (hT : T = T') {φ : T → T'} (hφ : ∀ x, φ x ≍ x)
    (y : T') : ∃! x, φ x = y := by
  subst hT
  have h : ∀ x, φ x = x := fun x => eq_of_heq (hφ x)
  exact ⟨y, h y, fun z hz => by rw [← hz, h]⟩

/-- The chosen cartesian pullback of `D2SGC F` (paper: `(a, b, C(id,β)c)`). -/
def pull {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b') : Ob F b :=
  (fmap F (dualVert β)).obj c

/-- The chosen opcartesian pushforward of `D2SGC F` (paper: `(a', B(α)b, C(α,id)c)`). -/
def push (α : a ⟶ a') {b : B.Ob a} (c : Ob F b) : Ob F (B.transp α b) :=
  (fmap F (dualHoriz α b)).obj c

theorem pullLift_obj {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b') :
    (fmap F (dualHoriz (𝟙 a) b)).obj (pull F β c)
      = (fmap F (dualVert (B.factor β))).obj c := by
  rw [pull, dualHoriz_id, ← fmap_obj_comp, ← dualVert_comp, B.factor_vert]

/-- The chosen cartesian lift of `D2SGC F` (paper: `(id, β, id)`). -/
def pullLift {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b') :
    Hom F β (pull F β c) c := GHom.ofEq (pullLift_obj F β c)

theorem pushLift_obj (α : a ⟶ a') {b : B.Ob a} (c : Ob F b) :
    (fmap F (dualHoriz α b)).obj c
      = (fmap F (dualVert (B.factor (B.olift α b)))).obj (push F α c) := by
  rw [push, B.factor_olift, dualVert_id]; simp

/-- The chosen opcartesian lift of `D2SGC F` (paper: `(α, id, id)`). -/
def pushLift (α : a ⟶ a') {b : B.Ob a} (c : Ob F b) :
    Hom F (B.olift α b) c (push F α c) := GHom.ofEq (pushLift_obj F α c)

theorem pull_id {b : B.Ob a} (c : Ob F b) : pull F (B.id b) c = c := by
  have h : dualVert (B.id b) = 𝟙 (B.dualOp.tot b) := dualVert_id b
  rw [pull, h]; simp

theorem pull_comp {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'') (c : Ob F b'') :
    pull F (β ≫ γ) c = pull F β (pull F γ c) := by
  rw [pull, pull, pull, dualVert_comp, fmap_obj_comp]

theorem push_id {b : B.Ob a} (c : Ob F b) : push F (𝟙 a) c ≍ c := by
  rw [push, dualHoriz_id, dualVert_eqToHom]
  exact fmap_eqToHom_obj_heq F _ c

theorem push_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : Ob F b) :
    push F (α ≫ α') c ≍ push F α' (push F α c) := by
  rw [push, ← dualHoriz_comp α α' b, fmap_obj_comp, fmap_obj_comp, dualVert_eqToHom]
  exact fmap_eqToHom_obj_heq F _ _

theorem push_pull (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b') :
    push F α (pull F β c) = pull F (B.transpMap α β) (push F α c) := by
  rw [push, pull, pull, push, ← fmap_obj_comp, ← fmap_obj_comp, dualVert_comp_dualHoriz]

theorem pullLift_id {b : B.Ob a} (c : Ob F b) : pullLift F (B.id b) c ≍ id' F c :=
  GHom.ofEq_heq _ _ rfl
    (fmap_obj_heq F rfl HEq.rfl (pull_id F c))

theorem pullLift_comp {b b' b'' : B.Fiber a} (β : b ⟶ b') (γ : b' ⟶ b'') (c : Ob F b'') :
    pullLift F (β ≫ γ) c ≍ comp' F (pullLift F β (pull F γ c)) (pullLift F γ c) := by
  have hz : B.dualOp.tot (B.transp (𝟙 a) b) = B.dualOp.tot (B.transp (𝟙 a ≫ 𝟙 a) b) :=
    congrArg (fun m : a ⟶ a => B.dualOp.tot (B.transp m b)) (Category.comp_id (𝟙 a)).symm
  rw [pullLift, pullLift, pullLift,
    comp'_ofEq F (pullLift_obj F β (pull F γ c)) (pullLift_obj F γ c)
      (comp'_ofEq_obj F (pullLift_obj F β (pull F γ c)) (pullLift_obj F γ c))]
  exact GHom.ofEq_heq _ _ hz
    (fmap_obj_heq F hz (dualHoriz_heq (Category.comp_id (𝟙 a)).symm b) (pull_comp F β γ c))

theorem pushLift_id {b : B.Ob a} (c : Ob F b) : pushLift F (𝟙 a) c ≍ id' F c :=
  GHom.ofEq_heq _ _ rfl HEq.rfl

theorem pushLift_comp (α : a ⟶ a') (α' : a' ⟶ a'') {b : B.Ob a} (c : Ob F b) :
    pushLift F (α ≫ α') c ≍ comp' F (pushLift F α c) (pushLift F α' (push F α c)) := by
  rw [pushLift, pushLift, pushLift,
    comp'_ofEq F (pushLift_obj F α c) (pushLift_obj F α' (push F α c))
      (comp'_ofEq_obj F (pushLift_obj F α c) (pushLift_obj F α' (push F α c)))]
  exact D2SGC.GHom.ofEq_heq _ _ rfl HEq.rfl

/-- `factor` of a chosen opcartesian lift followed by an arbitrary displayed morphism. -/
theorem factor_olift_comp (α : a ⟶ a') (f' : a' ⟶ a'') {b : B.Ob a} {b'' : B.Ob a''}
    (g' : (B.transp α b) ⟶[f'] b'') :
    B.factor (B.olift α b ≫ᵈ g') = eqToHom (B.transp_comp α f' b) ≫ B.factor g' := by
  rw [B.factor_comp, B.factor_olift, transpMap_id_vert, Category.id_comp]

/-- The vertical comparison morphism attached to a chosen opcartesian lift is an `eqToHom`. -/
theorem vertComp_factor_olift (α : a ⟶ a') (f' : a' ⟶ a'') (b : B.Ob a) :
    vertComp α f' (B.factor (B.olift α b))
      = eqToHom (congrArg (B.dualOp.tot (a := a'')) (B.transp_comp α f' b).symm) := by
  rw [vertComp, B.factor_olift, transpMap_id_vert, Category.comp_id]
  exact dualVert_eqToHom _

/-- Postcomposition with `pullLift` is heterogeneously the identity. -/
theorem comp'_pullLift_heq {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b')
    {β₀ : b₀ ⟶[𝟙 a] b} {c₀ : Ob F b₀} (ξ : Hom F β₀ c₀ (pull F β c)) :
    comp' F ξ (pullLift F β c) ≍ ξ := by
  refine (comp'_heq F ξ (pullLift F β c)).trans ?_
  rw [pullLift, GHom.ofEq_push]
  refine (GHom.trans_ofEq_heq _ _ _).trans ?_
  exact ξ.push_heq_of_eq_eqToHom _ (horizComp_id_right (𝟙 a) b₀)

/-- Precomposition with `pushLift` is heterogeneously the identity. -/
theorem pushLift_comp'_heq (α : a ⟶ a') {b : B.Ob a} (c : Ob F b) {f' : a' ⟶ a''}
    {b'' : B.Ob a''} {g' : (B.transp α b) ⟶[f'] b''} {c'' : Ob F b''}
    (ψ : Hom F g' (push F α c) c'') : comp' F (pushLift F α c) ψ ≍ ψ := by
  refine (comp'_heq F (pushLift F α c) ψ).trans ?_
  rw [pushLift, GHom.ofEq_push]
  refine (GHom.ofEq_trans_heq _ _ _).trans ?_
  exact ψ.push_heq_of_eq_eqToHom _ (vertComp_factor_olift α f' b)

theorem pullLift_cartesian {b b' b₀ : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b')
    (β₀ : b₀ ⟶[𝟙 a] b) (c₀ : Ob F b₀) (χ : Hom F (β₀ ≫ᵈ β) c₀ c) :
    ∃! ξ : Hom F β₀ c₀ (pull F β c), comp' F ξ (pullLift F β c) = χ := by
  have hz : B.dualOp.tot (B.transp (𝟙 a) b₀) = B.dualOp.tot (B.transp (𝟙 a ≫ 𝟙 a) b₀) :=
    congrArg (fun m : a ⟶ a => B.dualOp.tot (B.transp m b₀)) (Category.comp_id (𝟙 a)).symm
  refine existsUnique_of_heq_id (GHom.type_eq hz
    (fmap_obj_heq F hz (dualHoriz_heq (Category.comp_id (𝟙 a)).symm b₀) rfl) ?_)
    (fun ξ => comp'_pullLift_heq F β c ξ) χ
  refine HEq.symm ?_
  rw [← dualVert_comp_vertComp β₀ β, fmap_obj_comp, ← pullLift_obj, ← fmap_obj_comp,
    ← dualVert_comp_horizComp, fmap_obj_comp, horizComp_id_right]
  exact fmap_eqToHom_obj_heq F _ _

theorem pushLift_opcartesian (α : a ⟶ a') {b : B.Ob a} (c : Ob F b) {f' : a' ⟶ a''}
    {b'' : B.Ob a''} (g' : (B.transp α b) ⟶[f'] b'') (c'' : Ob F b'')
    (χ : Hom F (B.olift α b ≫ᵈ g') c c'') :
    ∃! ψ : Hom F g' (push F α c) c'', comp' F (pushLift F α c) ψ = χ := by
  refine existsUnique_of_heq_id (GHom.type_eq
    (congrArg (B.dualOp.tot (a := a'')) (B.transp_comp α f' b).symm)
    (push_comp F α f' c).symm ?_) (fun ψ => pushLift_comp'_heq F α c ψ) χ
  refine HEq.symm ?_
  rw [factor_olift_comp, dualVert_comp, fmap_obj_comp, dualVert_eqToHom]
  exact fmap_eqToHom_obj_heq F _ _

theorem pushLift_pullLift (α : a ⟶ a') {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : Ob F b')
    (δ : Hom F (B.olift α b) (pull F β c) (pull F (B.transpMap α β) (push F α c)))
    (hδ : δ ≍ pushLift F α (pull F β c)) :
    comp' F (pullLift F β c) (pushLift F α c)
      ≍ comp' F δ (pullLift F (B.transpMap α β) (push F α c)) := by
  have h : (fmap F (dualHoriz (𝟙 a') (B.transp α b))).obj (push F α (pull F β c))
      = (fmap F (dualVert (B.factor (B.transpMap α β)))).obj (push F α c) := by
    rw [push_pull]; exact pullLift_obj F (B.transpMap α β) (push F α c)
  have hψ : (GHom.ofEq h : Hom F (B.transpMap α β) (push F α (pull F β c)) (push F α c))
      ≍ pullLift F (B.transpMap α β) (push F α c) :=
    GHom.ofEq_heq _ _ rfl
      (fmap_obj_heq F rfl HEq.rfl (push_pull F α β c))
  refine HEq.trans ?_ (comp'_congr_mid F (push_pull F α β c) hδ.symm hψ)
  have hbase : (𝟙 a ≫ α) = (α ≫ 𝟙 a') := by simp
  have hz : B.dualOp.tot (B.transp (𝟙 a ≫ α) b) = B.dualOp.tot (B.transp (α ≫ 𝟙 a') b) :=
    congrArg (fun m : a ⟶ a' => B.dualOp.tot (B.transp m b)) hbase
  rw [pullLift, pushLift, comp'_ofEq F (pullLift_obj F β c) (pushLift_obj F α c)
      (comp'_ofEq_obj F (pullLift_obj F β c) (pushLift_obj F α c)),
    pushLift, comp'_ofEq F (pushLift_obj F α (pull F β c)) h
      (comp'_ofEq_obj F (pushLift_obj F α (pull F β c)) h)]
  exact GHom.ofEq_heq _ _ hz (fmap_obj_heq F hz (dualHoriz_heq hbase b) rfl)

end Fib

end

end D2SGC

/-- **The dependent 2-sided Grothendieck construction** (Def. `def:D2SGC` of the paper): the doubly
displayed category over `B` associated with a functor `F : ∫(Bᵈᵒ) ⥤ Cat`. -/
noncomputable def D2SGC (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : DoubleDisplayed B where
  Ob := fun {_} b => D2SGC.Ob F b
  Hom := fun g c c' => D2SGC.Hom F g c c'
  id := fun c => D2SGC.id' F c
  comp := fun θ θ' => D2SGC.comp' F θ θ'
  -- The laws are `castHom` equations; `castHom_eq_iff_heq` converts the `HEq` calculations of the
  -- `D2SGC` namespace, whose heterogeneity is over the `Cat`-valued fibers of `F`.
  id_comp := fun θ => (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr (D2SGC.id_comp'' F θ)
  comp_id := fun θ => (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr (D2SGC.comp_id'' F θ)
  assoc := fun θ θ' θ'' =>
    (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr (D2SGC.assoc'' F θ θ' θ'')

/-- The `D2SFib` structure on the D2S Grothendieck construction: items 1–4 of the paper's
proposition after Def. `def:D2SGC`. -/
noncomputable instance D2SGC.instD2SFib (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) :
    D2SFib (D2SGC F) where
  pull := D2SGC.pull F
  pullLift := D2SGC.pullLift F
  pullLift_cartesian := D2SGC.pullLift_cartesian F
  pull_id := D2SGC.pull_id F
  pullLift_id := by
    intro a b c
    exact (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr
      ((DoubleDisplayed.eqToHom_comp_heq' _ _ _).trans (D2SGC.pullLift_id F c))
  pull_comp := D2SGC.pull_comp F
  pullLift_comp := by
    intro a b b' b'' β γ c
    exact (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr
      ((DoubleDisplayed.eqToHom_comp_heq' _ _ _).trans (D2SGC.pullLift_comp F β γ c))
  push := D2SGC.push F
  pushLift := D2SGC.pushLift F
  pushLift_opcartesian := by
    intro a a' α b c
    exact D2SGC.pushLift_opcartesian F α c
  push_id := by
    intro a b c
    exact (DoubleDisplayedStruct.castObj_eq_iff_heq _ _).mpr (D2SGC.push_id F c)
  pushLift_id := by
    intro a b c
    refine (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr ?_
    have h1 : D2SGC.pushLift F (𝟙 a) c
        ≫ᵈᵈ (D2SGC F).eqToHomBase (D2SGC.push F (𝟙 a) c) (B.transp_id b)
        ≍ D2SGC.pushLift F (𝟙 a) c :=
      DoubleDisplayed.comp_eqToHomBase_heq _ _ _ _
    refine h1.trans ?_
    refine (D2SGC.pushLift_id F c).trans ?_
    refine HEq.symm ?_
    exact DoubleDisplayedStruct.eqToHom_heq_id _ _
  push_comp := by
    intro a a' a'' α α' b c
    exact (DoubleDisplayedStruct.castObj_eq_iff_heq _ _).mpr (D2SGC.push_comp F α α' c)
  pushLift_comp := by
    intro a a' a'' α α' b c
    refine (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr ?_
    exact ((DoubleDisplayed.comp_eqToHom_heq' _ _ _).trans
      (DoubleDisplayed.comp_eqToHomBase_heq _ _ _ _)).trans (D2SGC.pushLift_comp F α α' c)
  push_pull := D2SGC.push_pull F
  pushLift_pullLift := by
    intro a a' α b b' β c
    refine (DoubleDisplayedStruct.castHom_eq_iff_heq _ _ _).mpr ?_
    have hδ : (D2SGC.push_pull F α β c ▸ D2SGC.pushLift F α (D2SGC.pull F β c))
        ≍ D2SGC.pushLift F α (D2SGC.pull F β c) := eqRec_heq_self _ _
    refine (D2SGC.pushLift_pullLift F α β c _ hδ).trans ?_
    refine DoubleDisplayedStruct.heq_comp_left (D2SGC F).toDoubleDisplayedStruct
      (ψ := D2SGC.pullLift F (B.transpMap α β) (D2SGC.push F α c))
      (by simp) rfl (B.comp_id_heq _).symm HEq.rfl ?_
    refine hδ.trans ?_
    refine HEq.symm ?_
    exact DoubleDisplayed.comp_eqToHom_heq' _ _ _

namespace D2SGC

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃})

noncomputable section

/-! ### The fibers of `D2SGC F`

Both indexing morphisms of a *vertical* hom of `D2SGC F` are the same `eqToHom` of `∫(Bᵈᵒ)`
(`dualHoriz_id_eq`), so composition in the fiber `(D2SGC F).Fiber b` is ordinary composition in
`F.obj ⟨a, B.transp (𝟙 a) b⟩` after the `eqToHom` identifying them. This is what makes M9's unit
component a functor. -/

section Fiber

variable {a : A}

/-- Composition in a fiber of `D2SGC F` is a `GHom.trans` along `dualHoriz_id_eq`. -/
theorem fiber_comp_eq {b : B.Ob a} {c c' c'' : (D2SGC F).Fiber b} (ξ : c ⟶ c') (ψ : c' ⟶ c'') :
    (ξ ≫ ψ) = GHom.trans (F := F) ξ (dualHoriz_id_eq b).symm ψ := by
  refine eq_of_heq (((D2SGC F).castHom_heq _ _ _).trans ?_)
  refine (comp'_heq F ξ ψ).trans ?_
  refine GHom.trans_heq' (congrArg (fun m : a ⟶ a => B.dualOp.tot (B.transp m b))
      (Category.comp_id (𝟙 a)))
    (by rw [horizComp_id_right]; exact comp_eqToHom_heq _ _)
    (by rw [horizComp_id_right]; exact comp_eqToHom_heq _ _)
    (by rw [vertComp_factor_id]; exact comp_eqToHom_heq _ _)
    (ξ.push_heq_of_eq_eqToHom _ (horizComp_id_right (𝟙 a) b))
    (ψ.push_heq_of_eq_eqToHom _ (vertComp_factor_id (𝟙 a) b))

/-- **The unit component of M9**, forward direction: `F.obj ⟨a, b⟩` maps to the fiber of `D2SGC F`
over `b` by the identity on objects and an `eqToHom`-conjugation on morphisms. -/
def unitFiberFunctor (b : B.Ob a) : F.obj (B.dualOp.tot b) ⥤ (D2SGC F).Fiber b where
  obj c := c
  map θ := GHom.reindex (F := F) ((fmap F (dualHoriz (𝟙 a) b)).map θ) rfl (dualHoriz_id_eq b)
  map_id c := by
    change GHom.reindex (F := F) ((fmap F (dualHoriz (𝟙 a) b)).map (𝟙 c)) rfl _ = id' F c
    simp [GHom.reindex, id', GHom.ofEq]
  map_comp θ θ' := by
    rw [fiber_comp_eq]
    change GHom.reindex (F := F) ((fmap F (dualHoriz (𝟙 a) b)).map (θ ≫ θ')) rfl _ = _
    simp [GHom.reindex, GHom.trans, Functor.map_comp]

@[simp] theorem unitFiberFunctor_obj (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    (unitFiberFunctor F b).obj c = c := rfl

@[simp] theorem unitFiberFunctor_map (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    (unitFiberFunctor F b).map θ
      = GHom.reindex (F := F) ((fmap F (dualHoriz (𝟙 a) b)).map θ) rfl (dualHoriz_id_eq b) := rfl

/-- The object equality behind the chosen horizontal morphism over an identity. -/
theorem totIdOb (b : B.Ob a) :
    B.dualOp.tot b = B.dualOp.tot (B.transp (𝟙 a) b) :=
  congrArg (B.dualOp.tot (a := a)) (B.transp_id b).symm

/-- The chosen horizontal morphism over an identity is literally an `eqToHom` of `∫(Bᵈᵒ)`. -/
theorem dualHoriz_id_eqToHom (b : B.Ob a) : dualHoriz (𝟙 a) b = eqToHom (totIdOb (B := B) b) := by
  rw [dualHoriz_id]; exact dualVert_eqToHom _

/-- Reindexing back along `totIdOb` undoes the `dualHoriz`-reindexing, on objects. -/
theorem unitFiberInv_obj (b : B.Ob a) (c : F.obj (B.dualOp.tot b)) :
    (fmap F (eqToHom (totIdOb (B := B) b).symm)).obj ((fmap F (dualHoriz (𝟙 a) b)).obj c) = c := by
  rw [← fmap_obj_comp, dualHoriz_id_eqToHom, eqToHom_trans, eqToHom_refl, fmap_id_obj]

/-- **The unit component of M9**, backward direction. -/
def unitFiberInv (b : B.Ob a) : (D2SGC F).Fiber b ⥤ F.obj (B.dualOp.tot b) where
  obj c := c
  map {c c'} ξ :=
    eqToHom (unitFiberInv_obj F b c).symm
      ≫ (fmap F (eqToHom (totIdOb (B := B) b).symm)).map
          (ξ ≫ eqToHom (fmap_congr_obj F (dualHoriz_id_eq b).symm c'))
      ≫ eqToHom (unitFiberInv_obj F b c')
  map_id c := by
    change eqToHom _ ≫ (fmap F _).map (id' F c ≫ eqToHom _) ≫ eqToHom _ = _
    simp [id', GHom.ofEq]
  map_comp {c c' c''} ξ ψ := by
    rw [fiber_comp_eq]
    simp only [GHom.trans, Category.assoc, eqToHom_trans, Functor.map_comp, eqToHom_map]
    simp

@[simp] theorem unitFiberInv_obj_eq (b : B.Ob a) (c : (D2SGC F).Fiber b) :
    (unitFiberInv F b).obj c = c := rfl

/-- Reindexing forward along `dualHoriz (𝟙 a) b` and back is heterogeneously trivial. -/
theorem fmap_dualHoriz_id_roundtrip (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    (fmap F (eqToHom (totIdOb (B := B) b).symm)).map ((fmap F (dualHoriz (𝟙 a) b)).map θ) ≍ θ := by
  refine (fmap_map_map_heq F (dualHoriz (𝟙 a) b) (eqToHom (totIdOb (B := B) b).symm) θ).trans ?_
  rw [dualHoriz_id_eqToHom, eqToHom_trans, eqToHom_refl]
  exact fmap_id_map_heq F _ θ

theorem unitFiberFunctor_map_heq (b : B.Ob a) {c c' : F.obj (B.dualOp.tot b)} (θ : c ⟶ c') :
    (unitFiberFunctor F b).map θ ≍ (fmap F (dualHoriz (𝟙 a) b)).map θ :=
  GHom.reindex_heq _ rfl (dualHoriz_id_eq b)

theorem unitFiberInv_map_heq (b : B.Ob a) {c c' : (D2SGC F).Fiber b} (ξ : c ⟶ c') :
    (unitFiberInv F b).map ξ ≍ (fmap F (eqToHom (totIdOb (B := B) b).symm)).map ξ := by
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
  exact fmap_map_heq F _ rfl (fmap_congr_obj F (dualHoriz_id_eq b) c')
    (comp_eqToHom_heq _ _)

/-- The two directions of the unit component are strictly inverse. -/
theorem unitFiber_comp (b : B.Ob a) : unitFiberFunctor F b ⋙ unitFiberInv F b = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun c c' θ => ?_)
  refine (conj_eqToHom_iff_heq _ _ rfl rfl).mpr ?_
  refine (unitFiberInv_map_heq F b _).trans ?_
  refine HEq.trans ?_ (fmap_dualHoriz_id_roundtrip F b θ)
  exact fmap_map_heq F _ rfl (fmap_congr_obj F (dualHoriz_id_eq b).symm c')
    (unitFiberFunctor_map_heq F b θ)

/-- The other round trip of the unit component. -/
theorem unitFiber_inv_comp (b : B.Ob a) : unitFiberInv F b ⋙ unitFiberFunctor F b = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun c c' ξ => ?_)
  refine (conj_eqToHom_iff_heq _ _ rfl rfl).mpr ?_
  refine (unitFiberFunctor_map_heq F b _).trans ?_
  refine ((fmap_map_heq F (dualHoriz (𝟙 a) b) (unitFiberInv_obj F b c).symm
    ((unitFiberInv_obj F b c').symm.trans (congrArg
      (fmap F (eqToHom (totIdOb (B := B) b).symm)).obj (fmap_congr_obj F (dualHoriz_id_eq b) c')))
    (unitFiberInv_map_heq F b ξ)).trans ?_)
  refine (fmap_map_map_heq F (eqToHom (totIdOb (B := B) b).symm) (dualHoriz (𝟙 a) b) ξ).trans ?_
  have hk : eqToHom (totIdOb (B := B) b).symm ≫ dualHoriz (𝟙 a) b
      = 𝟙 (B.dualOp.tot (B.transp (𝟙 a) b)) := by
    rw [dualHoriz_id_eqToHom, eqToHom_trans, eqToHom_refl]
  rw [hk]
  exact fmap_id_map_heq F _ ξ

/-- The unit component of M9 as an isomorphism of `Cat`. -/
def unitFiberIso (b : B.Ob a) : F.obj (B.dualOp.tot b) ≅ Cat.of ((D2SGC F).Fiber b) where
  hom := (unitFiberFunctor F b).toCatHom
  inv := (unitFiberInv F b).toCatHom
  hom_inv_id := Cat.ext (unitFiber_comp F b)
  inv_hom_id := Cat.ext (unitFiber_inv_comp F b)

/-! `D2SGC F`'s fiberwise `pushMap` and `pullMap` are defined by universal properties, but because
composing with `pushLift`/`pullLift` is heterogeneously the identity they are simply `F.map`-images
along the comparison morphisms `horizComp`/`vertComp`. These are the computations M9's naturality
square needs. -/

/-- The pushforward action on fiber morphisms is `F.map` along `horizComp`. -/
theorem pushMap_heq {a' : A} (α : a ⟶ a') {b : B.Ob a} {c c' : (D2SGC F).Fiber b} (f : c ⟶ c') :
    D2SFib.pushMap α f ≍ (fmap F (horizComp (𝟙 a) α b)).map f := by
  refine (pushLift_comp'_heq F α c (D2SFib.pushMap α f)).symm.trans ?_
  refine (heq_of_eq (D2SFib.pushLift_pushMap α f)).trans ?_
  refine ((D2SGC F).castHom_heq _ _ _).trans ?_
  refine (comp'_heq F f (pushLift F α c')).trans ?_
  rw [pushLift, GHom.ofEq_push]
  refine (GHom.trans_ofEq_heq _ _ _).trans ?_
  exact f.push_heq_map (horizComp (𝟙 a) α b)

/-- The pullback action on fiber morphisms is `F.map` along `vertComp`. -/
theorem pullMap_heq {d d' : B.Ob a} (β : d ⟶[𝟙 a] d')
    {e e' : (D2SGC F).Fiber d'} (f : e ⟶ e') :
    D2SFib.pullMap β f ≍ (fmap F (vertComp (𝟙 a) (𝟙 a) (B.factor β))).map f := by
  refine (comp'_pullLift_heq F β e' (D2SFib.pullMap β f)).symm.trans ?_
  refine (heq_of_eq (D2SFib.pullMap_pullLift β f)).trans ?_
  refine ((D2SGC F).castHom_heq _ _ _).trans ?_
  refine (comp'_heq F (pullLift F β e) f).trans ?_
  rw [pullLift, GHom.ofEq_push]
  refine (GHom.ofEq_trans_heq _ _ _).trans ?_
  exact f.push_heq_map (vertComp (𝟙 a) (𝟙 a) (B.factor β))

/-! ### Naturality of the unit component

The two comparison morphisms `horizComp`/`vertComp` land in ambient fibers that are only
*propositionally* the ones `pushMap`/`pullMap` live in, so we bolt the mediating `eqToHom` onto each
of them (`pushCmp`, `pullCmp`); the resulting pair composes on the nose. -/

section Naturality

variable {a' : A}

theorem pushCmpFib (α : a ⟶ a') (b : B.Ob a) :
    B.transp (𝟙 a') (B.transp α b) = B.transp (𝟙 a ≫ α) b :=
  (B.transp_id (B.transp α b)).trans
    (congrArg (fun m : a ⟶ a' => B.transp m b) (Category.id_comp α)).symm

/-- `pushMap`'s comparison morphism, retyped to land in `pushMap`'s ambient fiber. -/
def pushCmp (α : a ⟶ a') (b : B.Ob a) :
    B.dualOp.tot (B.transp (𝟙 a) b) ⟶ B.dualOp.tot (B.transp (𝟙 a') (B.transp α b)) :=
  horizComp (𝟙 a) α b ≫ dualVert (eqToHom (pushCmpFib (B := B) α b))

theorem pullCmpFib (b' : B.Ob a') : B.transp (𝟙 a') b' = B.transp (𝟙 a' ≫ 𝟙 a') b' :=
  (congrArg (fun m : a' ⟶ a' => B.transp m b') (Category.comp_id (𝟙 a'))).symm

/-- `pullMap`'s comparison morphism, retyped to land in `pullMap`'s ambient fiber. -/
def pullCmp {b : B.Ob a} (α : a ⟶ a') {b' : B.Ob a'} (β : b' ⟶[𝟙 a'] (B.transp α b)) :
    B.dualOp.tot (B.transp (𝟙 a') (B.transp α b)) ⟶ B.dualOp.tot (B.transp (𝟙 a') b') :=
  vertComp (𝟙 a') (𝟙 a') (B.factor β) ≫ dualVert (eqToHom (pullCmpFib (B := B) b'))

theorem horizComp_heq_pushCmp (α : a ⟶ a') (b : B.Ob a) :
    horizComp (𝟙 a) α b ≍ pushCmp α b := by
  rw [pushCmp, dualVert_eqToHom]; exact (comp_eqToHom_heq _ _).symm

theorem vertComp_heq_pullCmp {b : B.Ob a} (α : a ⟶ a') {b' : B.Ob a'}
    (β : b' ⟶[𝟙 a'] (B.transp α b)) :
    vertComp (𝟙 a') (𝟙 a') (B.factor β) ≍ pullCmp α β := by
  rw [pullCmp, dualVert_eqToHom]; exact (comp_eqToHom_heq _ _).symm

theorem pushMap_heq' (α : a ⟶ a') {b : B.Ob a} {c c' : (D2SGC F).Fiber b} (f : c ⟶ c') :
    D2SFib.pushMap α f ≍ (fmap F (pushCmp α b)).map f :=
  (pushMap_heq F α f).trans
    (fmap_map_heq_of_heq F rfl (congrArg (B.dualOp.tot (a := a')) (pushCmpFib (B := B) α b).symm)
      (horizComp_heq_pushCmp α b) HEq.rfl HEq.rfl HEq.rfl)

theorem pullMap_heq' {b : B.Ob a} (α : a ⟶ a') {b' : B.Ob a'}
    (β : b' ⟶[𝟙 a'] (B.transp α b)) {e e' : (D2SGC F).Fiber (B.transp α b)} (f : e ⟶ e') :
    D2SFib.pullMap β f ≍ (fmap F (pullCmp α β)).map f :=
  (pullMap_heq F β f).trans
    (fmap_map_heq_of_heq F rfl (congrArg (B.dualOp.tot (a := a')) (pullCmpFib (B := B) b').symm)
      (vertComp_heq_pullCmp α β) HEq.rfl HEq.rfl HEq.rfl)

set_option linter.flexible false in
/-- The `push` half of the naturality identity. -/
theorem dualHoriz_comp_pushCmp (α : a ⟶ a') (b : B.Ob a) :
    dualHoriz (𝟙 a) b ≫ pushCmp α b = dualHoriz α b ≫ dualHoriz (𝟙 a') (B.transp α b) := by
  refine Total.hom_ext _ (by simp [pushCmp, horizComp]) ?_
  simp [pushCmp, horizComp, transpMap_id_vert]
  exact (eqToHom_heq_id_dom _ _ _).trans (eqToHom_heq_id_dom _ _ _).symm

set_option linter.flexible false in
/-- **The naturality identity of `∫(Bᵈᵒ)` behind M9's unit** (the paper's
`C(α, β) = C(id, β) ∘ C(α, id)`). -/
theorem unitNat_eq {b : B.Ob a} {b' : B.Ob a'} (u : B.dualOp.tot b ⟶ B.dualOp.tot b') :
    dualHoriz (𝟙 a) b ≫ pushCmp u.base b ≫ pullCmp u.base u.fiber
      = u ≫ dualHoriz (𝟙 a') b' := by
  refine Total.hom_ext _ (by simp [pushCmp, pullCmp, horizComp, vertComp]) ?_
  simp [pushCmp, pullCmp, horizComp, vertComp, transpMap_id, transpMap_id_vert,
    transpMap_comp_vert, Displayed.factor_vert]
  refine ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans (HEq.symm ?_)
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The naturality square of the unit, as an equality of functors. -/
theorem unitFiber_naturality {b : B.Ob a} {b' : B.Ob a'}
    (u : B.dualOp.tot b ⟶ B.dualOp.tot b') :
    fmap F u ⋙ unitFiberFunctor F b'
      = unitFiberFunctor F b ⋙ (D2SFib.pushFunctor (C := D2SGC F) u.base b
          ⋙ D2SFib.pullFunctor (C := D2SGC F) u.fiber) := by
  have hobj : ∀ c : F.obj (B.dualOp.tot b), (fmap F u).obj c
      = D2SFib.pull (C := D2SGC F) u.fiber (D2SFib.push (C := D2SGC F) u.base c) := by
    intro c
    rw [show D2SFib.pull (C := D2SGC F) u.fiber (D2SFib.push (C := D2SGC F) u.base c)
        = (fmap F (dualHoriz u.base b ≫ dualVert u.fiber)).obj c from
      (fmap_obj_comp F (dualHoriz u.base b) (dualVert u.fiber) c).symm, ← dual_factor]
    rfl
  -- the source object comparison, from `dualHoriz_comp_pushCmp`
  have hcs : ∀ c : F.obj (B.dualOp.tot b),
      (fmap F (dualHoriz (𝟙 a') (B.transp u.base b))).obj (D2SFib.push (C := D2SGC F) u.base c)
        = (fmap F (dualHoriz (𝟙 a) b ≫ pushCmp u.base b)).obj c := fun c =>
    (fmap_obj_comp F (dualHoriz u.base b) (dualHoriz (𝟙 a') (B.transp u.base b)) c).symm.trans
      (fmap_congr_obj F (dualHoriz_comp_pushCmp u.base b).symm c)
  refine CategoryTheory.Functor.hext hobj (fun c c' θ => ?_)
  have hpush : D2SFib.pushMap (C := D2SGC F) u.base ((unitFiberFunctor F b).map θ)
      ≍ (fmap F (dualHoriz (𝟙 a) b ≫ pushCmp u.base b)).map θ :=
    (pushMap_heq' F u.base _).trans
      ((fmap_map_heq_of_heq F rfl rfl HEq.rfl HEq.rfl
          (heq_of_eq (fmap_congr_obj F (dualHoriz_id_eq b).symm c'))
          (unitFiberFunctor_map_heq F b θ)).trans
        (fmap_map_map_heq F (dualHoriz (𝟙 a) b) (pushCmp u.base b) θ))
  refine HEq.trans ((unitFiberFunctor_map_heq F b' _).trans
    (fmap_map_map_heq F u (dualHoriz (𝟙 a') b') θ)) (HEq.symm ?_)
  refine (pullMap_heq' F u.base u.fiber _).trans ?_
  refine (fmap_map_heq_of_heq F rfl rfl HEq.rfl (heq_of_eq (hcs c))
    (heq_of_eq ((fmap_congr_obj F (dualHoriz_id_eq (B.transp u.base b)).symm
      (D2SFib.push (C := D2SGC F) u.base c')).trans (hcs c'))) hpush).trans ?_
  refine (fmap_map_map_heq F (dualHoriz (𝟙 a) b ≫ pushCmp u.base b)
    (pullCmp u.base u.fiber) θ).trans ?_
  rw [Category.assoc, unitNat_eq]
  rfl

end Naturality

end Fiber

end

end D2SGC

namespace D2SGC

variable {F F' : B.dualOp.Total ⥤ Cat.{v₃, u₃}}

noncomputable section

/-! ### `Φ` on morphisms -/

/-- The component of a natural transformation `κ : F ⟶ F'`, as an honest functor. -/
def kapp (κ : F ⟶ F') (x : B.dualOp.Total) : F.obj x ⥤ F'.obj x := (κ.app x).toFunctor

/-- Naturality of `κ`, as an equality of functors. -/
theorem kapp_naturality (κ : F ⟶ F') {x y : B.dualOp.Total} (u : x ⟶ y) :
    fmap F u ⋙ kapp κ y = kapp κ x ⋙ fmap F' u := by
  have h := congrArg Cat.Hom.toFunctor (κ.naturality u)
  rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor] at h
  exact h

/-- Naturality of `κ`, read off on objects. -/
theorem kapp_obj_nat (κ : F ⟶ F') {x y : B.dualOp.Total} (u : x ⟶ y) (c : F.obj x) :
    (kapp κ y).obj ((fmap F u).obj c) = (fmap F' u).obj ((kapp κ x).obj c) :=
  Functor.congr_obj (kapp_naturality κ u) c

/-- The action of `κ` on two-sided homs. -/
def gmap (κ : F ⟶ F') {x y z : B.dualOp.Total} {u : x ⟶ z} {v : y ⟶ z} {c : F.obj x}
    {c' : F.obj y} (θ : GHom F u v c c') :
    GHom F' u v ((kapp κ x).obj c) ((kapp κ y).obj c') :=
  eqToHom (kapp_obj_nat κ u c).symm
    ≫ (kapp κ z).map (θ : (fmap F u).obj c ⟶ (fmap F v).obj c')
    ≫ eqToHom (kapp_obj_nat κ v c')

section GmapLemmas

variable (κ : F ⟶ F') {x y z t : B.dualOp.Total} {u u₂ : x ⟶ z} {v v₂ : y ⟶ z} {c : F.obj x}
  {c' : F.obj y}

theorem gmap_ofEq (h : (fmap F u).obj c = (fmap F v).obj c')
    (h' : (fmap F' u).obj ((kapp κ x).obj c) = (fmap F' v).obj ((kapp κ y).obj c')) :
    gmap κ (GHom.ofEq h) = GHom.ofEq h' := by
  simp [gmap, GHom.ofEq, eqToHom_map]

theorem gmap_reindex (θ : GHom F u v c c') (hu : u = u₂) (hv : v = v₂) :
    gmap κ (θ.reindex hu hv) = (gmap κ θ).reindex hu hv := by
  subst hu; subst hv; simp [gmap, GHom.reindex]

theorem gmap_trans {w : B.dualOp.Total} {c'' : F.obj w} {v' : y ⟶ z} {r : w ⟶ z}
    (θ : GHom F u v c c') (h : v = v') (ψ : GHom F v' r c' c'') :
    gmap κ (θ.trans h ψ) = (gmap κ θ).trans h (gmap κ ψ) := by
  subst h; simp [gmap, GHom.trans, Functor.map_comp]

theorem gmap_push (θ : GHom F u v c c') (k : z ⟶ t) :
    gmap κ (θ.push k) = (gmap κ θ).push k := by
  have key := Functor.congr_hom (kapp_naturality κ k)
    (θ : (fmap F u).obj c ⟶ (fmap F v).obj c')
  simp only [Functor.comp_map] at key
  simp only [gmap, GHom.push, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  rw [key]
  simp

/-- `gmap` is heterogeneously just the action of `κ`'s component. -/
theorem gmap_heq_map (θ : GHom F u v c c') :
    gmap κ θ ≍ (kapp κ z).map (θ : (fmap F u).obj c ⟶ (fmap F v).obj c') := by
  simp only [gmap]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The object equality underlying `gmap` of an `ofEq`. -/
theorem gmap_ofEq_obj (h : (fmap F u).obj c = (fmap F v).obj c') :
    (fmap F' u).obj ((kapp κ x).obj c) = (fmap F' v).obj ((kapp κ y).obj c') :=
  (kapp_obj_nat κ u c).symm.trans ((congrArg (kapp κ z).obj h).trans (kapp_obj_nat κ v c'))

end GmapLemmas

/-- `κ`'s component is a congruence for `≍` of morphisms with propositionally equal endpoints. -/
theorem kapp_map_heq (κ : F ⟶ F') {z : B.dualOp.Total} {d d' e e' : F.obj z} (hd : d = e)
    (hd' : d' = e') {θ : d ⟶ d'} {ψ : e ⟶ e'} (h : θ ≍ ψ) :
    (kapp κ z).map θ ≍ (kapp κ z).map ψ := by
  subst hd; subst hd'; obtain rfl := eq_of_heq h; rfl

/-- `gmap` along the identity natural transformation is heterogeneously trivial. -/
theorem gmap_id_heq {x y z : B.dualOp.Total} {u : x ⟶ z} {v : y ⟶ z} {c : F.obj x} {c' : F.obj y}
    (θ : GHom F u v c c') : gmap (𝟙 F) θ ≍ θ := gmap_heq_map (𝟙 F) θ

/-- `gmap` is functorial in the natural transformation. -/
theorem gmap_comp_heq {F'' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F') (κ' : F' ⟶ F'')
    {x y z : B.dualOp.Total} {u : x ⟶ z} {v : y ⟶ z} {c : F.obj x} {c' : F.obj y}
    (θ : GHom F u v c c') : gmap (κ ≫ κ') θ ≍ gmap κ' (gmap κ θ) := by
  refine ((gmap_heq_map (κ ≫ κ') θ).trans ?_).trans (gmap_heq_map κ' (gmap κ θ)).symm
  exact (kapp_map_heq κ' (kapp_obj_nat κ u c).symm (kapp_obj_nat κ v c').symm
    (gmap_heq_map κ θ)).symm

/-- The action of `κ` on `D2SGC`-morphisms commutes with composition. -/
theorem gmap_comp' (κ : F ⟶ F') {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''} {b : B.Ob a}
    {b' : B.Ob a'} {b'' : B.Ob a''} {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : Ob F b}
    {c' : Ob F b'} {c'' : Ob F b''} (θ : Hom F g c c') (θ' : Hom F g' c' c'') :
    gmap κ (comp' F θ θ') = comp' F' (gmap κ θ) (gmap κ θ') := by
  simp only [comp', gmap_reindex, gmap_trans, gmap_push]

end

end D2SGC

/-- Bundled form: the object of `D2SFibCat B` carried by the D2S Grothendieck construction. -/
noncomputable def D2SGCFib (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : D2SFibCat B := ⟨D2SGC F⟩

/-- `Φ` on morphisms: a natural transformation `κ : F ⟶ F'` induces a morphism of D2SFibs. Its
underlying vertical functor is `κ`'s component functor on objects and `D2SGC.gmap κ` on morphisms;
preservation of the chosen lifts is `κ`'s naturality at `dualVert`/`dualHoriz`. -/
noncomputable def D2SGCMap {F F' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F') :
    D2SGCFib F ⟶ D2SGCFib F' where
  obj := fun {_} {b} c => (D2SGC.kapp κ (B.dualOp.tot b)).obj c
  map := fun θ => D2SGC.gmap κ θ
  map_id := fun c => by
    change D2SGC.gmap κ (D2SGC.id' F c) = D2SGC.id' F' _
    exact D2SGC.gmap_ofEq κ _ _
  map_comp := fun θ θ' => D2SGC.gmap_comp' κ θ θ'
  obj_pull := fun β c => by
    change (D2SGC.kapp κ _).obj (D2SGC.pull F β c) = D2SGC.pull F' β _
    exact D2SGC.kapp_obj_nat κ (dualVert β) c
  map_pullLift := fun β c => by
    change D2SGC.gmap κ (D2SGC.pullLift F β c) ≍ D2SGC.pullLift F' β _
    rw [D2SGC.pullLift, D2SGC.gmap_ofEq κ (D2SGC.pullLift_obj F β c)
      (D2SGC.gmap_ofEq_obj κ (D2SGC.pullLift_obj F β c)), D2SGC.pullLift]
    exact D2SGC.GHom.ofEq_heq _ _ rfl
      (heq_of_eq (congrArg (D2SGC.fmap F' (dualHoriz (𝟙 _) _)).obj
        (D2SGC.kapp_obj_nat κ (dualVert β) c)))
  obj_push := by
    intro a a' α b c
    change (D2SGC.kapp κ _).obj (D2SGC.push F α c) = D2SGC.push F' α _
    exact D2SGC.kapp_obj_nat κ (dualHoriz α b) c
  map_pushLift := by
    intro a a' α b c
    change D2SGC.gmap κ (D2SGC.pushLift F α c) ≍ D2SGC.pushLift F' α _
    rw [D2SGC.pushLift, D2SGC.gmap_ofEq κ (D2SGC.pushLift_obj F α c)
      (D2SGC.gmap_ofEq_obj κ (D2SGC.pushLift_obj F α c)), D2SGC.pushLift]
    exact D2SGC.GHom.ofEq_heq _ _ rfl HEq.rfl

/-- **`Φ`**: the D2S Grothendieck construction as a functor into `D2SFib(A, B)`. -/
noncomputable def D2SGCFunctor : (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ⥤ D2SFibCat B where
  obj F := D2SGCFib F
  map κ := D2SGCMap κ
  map_id _ := D2SFibHom.ext (DoubleDisplayed.VertFunctor.ext (fun _ => rfl)
    (fun θ => D2SGC.gmap_id_heq θ))
  map_comp κ κ' := D2SFibHom.ext (DoubleDisplayed.VertFunctor.ext (fun _ => rfl)
    (fun θ => D2SGC.gmap_comp_heq κ κ' θ))

end Nfib
