import Displayed.Opfibration.OpcartesianFunctor
import Displayed.Displayed.Section
import TwoCategory.Factorization.Comma.Cat

/-!
# Split opfibrations are algebras of the comma AWFS on `Cat`

The comma AWFS on `Cat.{u, u}` (`TwoCategory.Factorization.Comma.Cat`) factors a functor
`π : T ⥤ E` through the comma category `π/E = Comma π (𝟭 E)` of the triples `(x, e, f : π x ⟶ e)`.
An action of its 2-monad `R` on `π` is a functor `π/E ⥤ T` over `E`, which pushes `x` forward
along `f`.

## The algebra of a split opfibration

For a split opfibration `D` over `E` (both with objects and morphisms in `Type u`), the projection
`π : D.Total ⥤ E` (`πArr`) is an `R`-algebra (`ralg`), with action
```
  (x, e, f) ↦ push f x                                              (actObj)
  (α, β) : (x, e, f) ⟶ (x', e', f')  ↦  olift β (push f x) ≫ desc   (actMap)
```
where `desc : push (f ≫ β) x ⟶ push f' x'` is the factorization of `α ≫ olift f' x'` through
`olift (f ≫ β) x`. The equation `α ≫ f' = f ≫ β` of the comma morphism is only propositional, so
`α ≫ olift f' x'`, which lies over `α ≫ f'`, is transported to `f ≫ β` (`castBase`). The image of
`(α, β)` is characterized by `olift f x ≫ actMap (α, β) = α ≫ olift f' x'` up to this transport
(`olift_comp_actMap`), and morphisms out of `push f x` are determined by their composites with
`olift f x` (`actObj_hom_ext`), which proves the functor laws and the associativity law. The unit
law holds by `rfl`, checked in the kernel: `push (𝟙 _) x = x`, and the factorization of a morphism
through a chosen lift is the morphism itself, both by the rules of split opfibrations.

The `R`-algebra structures on `π` (`RAlgStr`) are the actions satisfying the unit and
associativity laws. A split opfibration structure on `D` is determined by its `R`-algebra
structure (`SplitOpfib.toRAlgStr_injective`): the chosen pushforward of `x` along `f` is the action
at `(x, a', f)`, and the chosen lift its action at `(𝟙, f) : (x, a, 𝟙) ⟶ (x, a', f)`. Every
`R`-algebra structure on `π` comes from a split opfibration, which gives an equivalence
(`splitOpfibEquiv`, `Opfibration/RAlgebraEquiv`).

## Opcartesian functors

An opcartesian functor `H` over `u` (`OpcartesianFunctor`), sending chosen lifts to chosen lifts,
is a morphism of `R`-algebras `(H, u) : π_D ⟶ π_{D'}` (`OpcartesianFunctor.ralgHom`), since it
preserves the chosen lifts and the factorizations through them.

## The chosen lifts of the AWFS

The chosen lift (`AWFS.lift`) of a square `(S, 𝟙) : f ⟶ π`, against the `L`-coalgebra of a left
adjoint right inverse `f ⊣ r` with counit `ε` (`Arr.Lari`), where `S` is a section of the
reindexing of `D` along `f` (`sectionSq`), sends `e` to `push ε_e (S (r e))` by `rfl`
(`lift_sectionSq_obj`): the AWFS lift is the transport of `S` along the counit.

This file has no dual in `Fibration/`: split fibrations are the algebras of the dual AWFS, through
the comma objects `B/f`, which is not formalized.
-/

universe u

open CategoryTheory TwoCategory

namespace Displayed

open scoped Displayed

variable {E : Cat.{u, u}} (D : Displayed.{u, u} E)

/-- The projection `π : D.Total ⥤ E` of the total category, as an arrow of `Cat`. -/
def πArr : Arr Cat.{u, u} :=
  ⟨Cat.of D.Total, E, D.π.toCatHom⟩

/-- Transport of a displayed morphism along an equality of base morphisms. -/
def castBase {a a' : E} {f g : a ⟶ a'} (h : f = g) {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    x ⟶[g] y :=
  h ▸ φ

/-- The transport of a displayed morphism along an equality of base morphisms is
heterogeneously equal to it. -/
theorem castBase_heq {a a' : E} {f g : a ⟶ a'} (h : f = g) {x : D.Ob a} {y : D.Ob a'}
    (φ : x ⟶[f] y) : D.castBase h φ ≍ φ := by
  subst h
  rfl

variable {D} in
/-- Composites of heterogeneously equal morphisms over equal base morphisms, with a morphism on
the right, are heterogeneously equal. -/
theorem comp_heq_of_heq_left {a a' a'' : E} {f f' : a ⟶ a'} (hf : f = f') {g : a' ⟶ a''}
    {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''} {φ : x ⟶[f] y} {φ' : x ⟶[f'] y} (h : φ ≍ φ')
    (ψ : y ⟶[g] z) : φ ≫ᵈ ψ ≍ φ' ≫ᵈ ψ := by
  subst hf
  cases h
  rfl

variable {D} in
/-- Composites of heterogeneously equal morphisms over equal base morphisms, with a morphism on
the left, are heterogeneously equal. -/
theorem comp_heq_of_heq_right {a a' a'' : E} {f : a ⟶ a'} {g g' : a' ⟶ a''} (hg : g = g')
    {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''} (φ : x ⟶[f] y) {ψ : y ⟶[g] z} {ψ' : y ⟶[g'] z}
    (h : ψ ≍ ψ') : φ ≫ᵈ ψ ≍ φ ≫ᵈ ψ' := by
  subst hg
  cases h
  rfl

variable {D} in
/-- Displayed functors respect heterogeneous equality of morphisms over equal base morphisms. -/
theorem DispFunctor.map_heq {E' : Cat.{u, u}} {D' : Displayed.{u, u} E'} {u : E ⟶ E'}
    {G : DispFunctor u.toFunctor D D'} {a a' : E} {f f' : a ⟶ a'}
    (hf : f = f') {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y} {φ' : x ⟶[f'] y} (h : φ ≍ φ') :
    G.map φ ≍ G.map φ' := by
  subst hf
  cases h
  rfl

variable [SplitOpfib D]

/-! ## The algebra of a split opfibration -/

/-- The action on objects: `(x, e, f : π x ⟶ e) ↦ push f x`. -/
def actObj (c : Comma D.π (𝟭 E)) : D.Total :=
  ⟨c.right, D.push c.hom c.left.2⟩

/-- The action on morphisms: `(α, β) : (x, e, f) ⟶ (x', e', f')` goes to the morphism over `β`
from `push f x` to `push f' x'`, the chosen lift of `β` followed by the factorization of
`α ≫ olift f' x'` through `olift (f ≫ β) x`. -/
def actMap {c c' : Comma D.π (𝟭 E)} (φ : c ⟶ c') : D.actObj c ⟶ D.actObj c' :=
  ⟨φ.right, D.olift φ.right (D.push c.hom c.left.2) ≫ᵈ
    D.opcartesianFactor (f := c.hom ≫ φ.right) (D.castBase (g := c.hom ≫ φ.right) φ.w
      (φ.left.fiber ≫ᵈ D.olift c'.hom c'.left.2))⟩

/-- The defining property of `actMap φ`: precomposed with `olift f x`, it is `α ≫ olift f' x'`,
transported along the equation of `φ`. -/
theorem olift_comp_actMap {c c' : Comma D.π (𝟭 E)} (φ : c ⟶ c') :
    D.olift c.hom c.left.2 ≫ᵈ (D.actMap φ).fiber =
      D.castBase (g := c.hom ≫ φ.right) φ.w (φ.left.fiber ≫ᵈ D.olift c'.hom c'.left.2) := by
  let χ := D.castBase (g := c.hom ≫ φ.right) φ.w (φ.left.fiber ≫ᵈ D.olift c'.hom c'.left.2)
  kernel_exact (congrArg (· ≫ᵈ D.opcartesianFactor χ)
    (D.olift_comp c.hom φ.right c.left.2)).symm.trans (D.olift_comp_opcartesianFactor χ)

/-- `olift_comp_actMap`, up to the transport. -/
theorem olift_comp_actMap_heq {c c' : Comma D.π (𝟭 E)} (φ : c ⟶ c') :
    D.olift c.hom c.left.2 ≫ᵈ (D.actMap φ).fiber ≍ φ.left.fiber ≫ᵈ D.olift c'.hom c'.left.2 :=
  (heq_of_eq (D.olift_comp_actMap φ)).trans (D.castBase_heq _ _)

/-- The action preserves identities, by the rules `olift (𝟙 _) x = 𝟙` and
`opcartesianFactor (olift f x) = 𝟙`. -/
theorem actMap_id (c : Comma D.π (𝟭 E)) : D.actMap (𝟙 c) = 𝟙 (D.actObj c) := by
  kernel_rfl'

/-- The action preserves composites, by the uniqueness of factorizations through chosen lifts. -/
theorem actMap_comp {c c' c'' : Comma D.π (𝟭 E)} (φ : c ⟶ c') (ψ : c' ⟶ c'') :
    D.actMap (φ ≫ ψ) = D.actMap φ ≫ D.actMap ψ := by
  refine Total.Hom.ext' rfl (heq_of_eq ?_)
  refine IsOpcartesian.hom_ext (D.isOpcartesianOlift c.hom c.left.2) (eq_of_heq ?_)
  have h₁ : φ.left.fiber ≫ᵈ (ψ.left.fiber ≫ᵈ D.olift c''.hom c''.left.2) ≍
      φ.left.fiber ≫ᵈ (D.olift c'.hom c'.left.2 ≫ᵈ (D.actMap ψ).fiber) :=
    comp_heq_of_heq_right ψ.w φ.left.fiber (D.olift_comp_actMap_heq ψ).symm
  have h₂ : (φ.left.fiber ≫ᵈ D.olift c'.hom c'.left.2) ≫ᵈ (D.actMap ψ).fiber ≍
      (D.olift c.hom c.left.2 ≫ᵈ (D.actMap φ).fiber) ≫ᵈ (D.actMap ψ).fiber :=
    comp_heq_of_heq_left φ.w (D.olift_comp_actMap_heq φ).symm _
  exact (D.olift_comp_actMap_heq (φ ≫ ψ)).trans (h₁.trans h₂)

/-- Two morphisms out of `push f x` over the same base morphism are equal if they agree after the
chosen lift `olift f x`. -/
theorem actObj_hom_ext {c : Comma D.π (𝟭 E)} {y : D.Total} {F G : D.actObj c ⟶ y}
    (hb : F.base = G.base)
    (h : D.olift c.hom c.left.2 ≫ᵈ F.fiber ≍ D.olift c.hom c.left.2 ≫ᵈ G.fiber) : F = G := by
  obtain ⟨b, φ⟩ := F
  obtain ⟨b', ψ⟩ := G
  dsimp only at hb
  subst hb
  exact congrArg _ (IsOpcartesian.hom_ext (D.isOpcartesianOlift c.hom c.left.2) (eq_of_heq h))

/-- The action `π/E ⥤ D.Total` of a split opfibration, `(x, e, f) ↦ push f x`. -/
def actFunctor : Comma D.π (𝟭 E) ⥤ D.Total where
  obj := D.actObj
  map := D.actMap
  map_id := D.actMap_id
  map_comp := D.actMap_comp

/-- The action, the square `(act, 𝟙) : R π ⟶ π` of `Arr Cat`. -/
def actHom : rMonad.T.obj D.πArr ⟶ D.πArr :=
  ⟨D.actFunctor.toCatHom, 𝟙 E, rfl⟩

/-- The domain component of the action square is the action. -/
theorem actHom_left : D.actHom.left = D.actFunctor.toCatHom :=
  rfl

/-- The codomain component of the action square is the identity. -/
theorem actHom_right : D.actHom.right = 𝟙 E :=
  rfl

/-- The unit law of the action: `push (𝟙 _) x = x` and `olift (𝟙 _) x = 𝟙`. -/
theorem actHom_unit : rMonad.η D.πArr ≫ D.actHom = 𝟙 D.πArr :=
  Arr.Hom.ext (by kernel_rfl') (by kernel_rfl')

/-- The associativity law of the action: `push (f ≫ g) x = push g (push f x)`, and the
corresponding equation of morphisms, by the uniqueness of factorizations through chosen lifts. -/
theorem actHom_assoc : rMonad.μ D.πArr ≫ D.actHom = rMonad.T.map D.actHom ≫ D.actHom := by
  refine Arr.Hom.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun X Y Ψ => ?_)) rfl
  let Ψ₁ := (rMonad.μ D.πArr).left.toFunctor.map Ψ
  let Ψ₂ := (rMonad.T.map D.actHom).left.toFunctor.map Ψ
  change D.actMap Ψ₁ ≍ D.actMap Ψ₂
  refine heq_of_eq (D.actObj_hom_ext rfl ((D.olift_comp_actMap_heq Ψ₁).trans ?_))
  have h₁ := comp_heq_of_heq_right Ψ.w.symm (D.olift X.left.hom X.left.left.2)
    (D.olift_comp_actMap_heq Ψ₂)
  have h₂ := comp_heq_of_heq_left Ψ.left.w.symm (D.olift_comp_actMap_heq Ψ.left)
    (D.olift Y.hom (D.actObj Y.left).2)
  kernel_exact h₂.symm.trans h₁.symm

/-- **The `R`-algebra of a split opfibration**, on the projection of its total category: the
action sends `(x, e, f : π x ⟶ e)` to `push f x`. -/
def ralg : RAlg Cat.{u, u} where
  obj := D.πArr
  act := D.actHom
  unit := D.actHom_unit
  assoc := D.actHom_assoc

/-- The `R`-algebra of a split opfibration is on its projection. -/
@[simp]
theorem ralg_obj : D.ralg.obj = D.πArr :=
  rfl

/-- The action of the `R`-algebra of a split opfibration. -/
@[simp]
theorem ralg_act : D.ralg.act = D.actHom :=
  rfl

/-! ## Split opfibrations are determined by their algebras -/

variable (E) in
/-- The `R`-algebra structures on the projection `π : D.Total ⥤ E`: the actions `R π ⟶ π`
satisfying the unit and associativity laws, that is the `R`-algebras whose underlying arrow is
`π`. -/
structure RAlgStr (D : Displayed.{u, u} E) where
  /-- The action. -/
  act : rMonad.T.obj D.πArr ⟶ D.πArr
  unit : rMonad.η D.πArr ≫ act = 𝟙 D.πArr
  assoc : rMonad.μ D.πArr ≫ act = rMonad.T.map act ≫ act

variable {D} in
/-- The `R`-algebra of an `R`-algebra structure on the projection. -/
def RAlgStr.toRAlg (a : RAlgStr E D) : RAlg Cat.{u, u} :=
  ⟨D.πArr, a.act, a.unit, a.assoc⟩

omit [SplitOpfib D] in
/-- The `R`-algebra structure of a split opfibration structure on `D`. -/
def SplitOpfib.toRAlgStr (s : SplitOpfib D) : RAlgStr E D :=
  ⟨@actHom E D s, @actHom_unit E D s, @actHom_assoc E D s⟩

/-- The object `(x, a', f : a ⟶ a')` of `π/E`. -/
abbrev commaMk {a a' : E} (f : a ⟶ a') (x : D.Ob a) : Comma D.π (𝟭 E) :=
  ⟨D.tot x, a', f⟩

/-- The morphism `(𝟙, f) : (x, a, 𝟙) ⟶ (x, a', f)` of `π/E`, from the unit `L π` at `x`. -/
def commaUnitHom {a a' : E} (f : a ⟶ a') (x : D.Ob a) :
    (⟨D.tot x, a, 𝟙 a⟩ : Comma D.π (𝟭 E)) ⟶ D.commaMk f x :=
  ⟨𝟙 _, f, rfl⟩

/-- The action sends `(𝟙, f)` to the chosen lift `olift f x`. -/
theorem actMap_commaUnitHom_fiber {a a' : E} (f : a ⟶ a') (x : D.Ob a) :
    (D.actMap (D.commaUnitHom f x)).fiber = D.olift f x := by
  kernel_rfl'

omit [SplitOpfib D] in
/-- Split opfibration structures with the same chosen pushforwards and lifts are equal. -/
theorem SplitOpfib.ext' : ∀ (s t : SplitOpfib D)
    (_ : ∀ {a a' : E} (f : a ⟶ a') (x : D.Ob a),
      @Opfib.push _ _ D s.toPreSplitOpfib.toOpfib a a' f x =
        @Opfib.push _ _ D t.toPreSplitOpfib.toOpfib a a' f x)
    (_ : ∀ {a a' : E} (f : a ⟶ a') (x : D.Ob a),
      @Opfib.olift _ _ D s.toPreSplitOpfib.toOpfib a a' f x ≍
        @Opfib.olift _ _ D t.toPreSplitOpfib.toOpfib a a' f x), s = t
  | @SplitOpfib.mk _ _ _ (@PreSplitOpfib.mk _ _ _ (Opfib.mk p o h) _ _) _ _,
    @SplitOpfib.mk _ _ _ (@PreSplitOpfib.mk _ _ _ (Opfib.mk p' o' h') _ _) _ _, hp, ho => by
    obtain rfl : @p = @p' := by funext a a' f x; exact hp f x
    obtain rfl : @o = @o' := by funext a a' f x; exact eq_of_heq (ho f x)
    obtain rfl : @h = @h' := Subsingleton.elim _ _
    rfl

omit [SplitOpfib D] in
/-- **A split opfibration structure is determined by its `R`-algebra structure**: the chosen
pushforward of `x` along `f` is the action at `(x, a', f)`, and the chosen lift is the action at
`(𝟙, f) : (x, a, 𝟙) ⟶ (x, a', f)`. -/
theorem SplitOpfib.toRAlgStr_injective : Function.Injective (SplitOpfib.toRAlgStr D) := by
  intro s t h
  have hL : @actFunctor E D s = @actFunctor E D t :=
    congrArg (fun a : RAlgStr E D => a.act.left.toFunctor) h
  refine SplitOpfib.ext' D s t (fun f x => ?_) (fun f x => ?_)
  · exact eq_of_heq (Sigma.ext_iff.1 (Functor.congr_obj hL (D.commaMk f x))).2
  · have e := Section.fiber_hcongr rfl (Functor.congr_obj hL (D.commaMk f x))
      (Functor.hcongr_hom hL (D.commaUnitHom f x))
    kernel_exact e

/-! ## Opcartesian functors are morphisms of algebras -/

section OpcartesianFunctor

variable {D} {E' : Cat.{u, u}} {D' : Displayed.{u, u} E'} [SplitOpfib D'] {u : E ⟶ E'}

variable (H : OpcartesianFunctor u.toFunctor D D')

/-- The square `(H, u) : π_D ⟶ π_{D'}` of the total functor of a displayed functor over `u`. -/
def OpcartesianFunctor.πArrHom : D.πArr ⟶ D'.πArr :=
  ⟨H.toDispFunctor.total.toCatHom, u, rfl⟩

/-- **An opcartesian functor is a morphism of `R`-algebras**: its total functor commutes with the
actions, since it preserves the chosen lifts and the factorizations through them. -/
def OpcartesianFunctor.ralgHom : D.ralg ⟶ D'.ralg where
  hom := H.πArrHom
  w := by
    refine Arr.Hom.ext (Cat.Hom.ext (Functor.hext (fun _ => rfl) fun c c' φ => ?_)) rfl
    let φ' := (rMonad.T.map H.πArrHom).left.toFunctor.map φ
    change H.toDispFunctor.total.map (D.actMap φ) ≍ D'.actMap φ'
    refine heq_of_eq (D'.actObj_hom_ext (F := H.toDispFunctor.total.map (D.actMap φ))
      (G := D'.actMap φ') rfl ?_)
    kernel_exact (DispFunctor.map_heq (G := H.toDispFunctor) φ.w.symm
      (D.olift_comp_actMap_heq φ)).trans (D'.olift_comp_actMap_heq φ').symm

/-- The morphism of `R`-algebras of an opcartesian functor is its total functor. -/
@[simp]
theorem OpcartesianFunctor.ralgHom_hom_left :
    H.ralgHom.hom.left = H.toDispFunctor.total.toCatHom :=
  rfl

/-- The morphism of `R`-algebras of an opcartesian functor lies over `u`. -/
@[simp]
theorem OpcartesianFunctor.ralgHom_hom_right : H.ralgHom.hom.right = u :=
  rfl

end OpcartesianFunctor

/-! ## The chosen lifts of the AWFS against LARIs -/

section Lift

variable {f : Arr Cat.{u, u}} (l : f.Lari) (D : Displayed.{u, u} f.cod) [SplitOpfib D]
  (S : (DisplayedCat.pull f.hom D).Section)

/-- The square `(S, 𝟙) : f ⟶ π` of a section `S` of the reindexing of `D` along `f`, whose first
component is the functor `p ↦ (f p, S p)` over `f`. -/
def sectionSq : f ⟶ D.πArr :=
  ⟨(S.total ⋙ (DisplayedCat.clift f.hom D).total).toCatHom, 𝟙 f.cod, rfl⟩

/-- **The chosen lift against a LARI is the transport along its counit**: the chosen lift of the
square `(S, 𝟙)` sends `e` to `push ε_e (S (r e))`, by `rfl`. -/
theorem lift_sectionSq_obj (e : f.cod) :
    (AWFS.lift (A := catAWFS) l.toLCoalg D.ralg (D.sectionSq S)).toFunctor.obj e =
      ⟨e, D.push (l.counit.toNatTrans.app e) (S.obj (l.toRetraction.r.toFunctor.obj e))⟩ :=
  rfl

end Lift

end Displayed
