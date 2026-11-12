import Displayed.Opfibration.RAlgebra

/-!
# `R`-algebras on a projection are split opfibrations

For a displayed category `D` over `E : Cat.{u, u}`, the split opfibration structures on `D` are
the `R`-algebra structures on its projection `π : D.Total ⥤ E` for the comma AWFS on `Cat`
(`splitOpfibEquiv : SplitOpfib D ≃ RAlgStr E D`). One direction is `SplitOpfib.toRAlgStr`
(`Opfibration/RAlgebra`): the action of a split opfibration pushes `x` forward along `f`.

## From an action to a split opfibration

An action `act : R π ⟶ π` is a square `(L, R')`, with `R' = 𝟙` by the unit law. Its functor
`L : π/E ⥤ D.Total` lies over `E` (`RAlgStr.L_fst`), is a retraction of `L π : y ↦ (y, π y, 𝟙)`
(`RAlgStr.L_unit`), and satisfies the associativity law `μ ⋙ L = R act ⋙ L`, where `μ` sends
`((x, e, f), e', g)` to `(x, e', f ≫ g)` (`compFun`).

The square of `act` is a rule (`Arr.Hom.w`), so the functor `R act = commaMap act` is typed
through it: its value at `((x, e, f), e', g)` has the component `g : e ⟶ e'` at the type
`π (L (x, e, f)) ⟶ e'`, which the rule identifies with `e ⟶ e'` only for the composite functor
`act.left ≫ π`, not at the objects. Nothing can be proved about these values directly. So
`R act` is first shown to be the functor `actComma L`, which transports `g` along the equation
`π (L c) = c.right` of the square (`RAlgStr.commaMap_nAct`), by the universal property of `π/E`:
both are compared through their composites with its legs and its universal 2-cell, which are
1- and 2-cells of `Cat` and are compared through the rules. This gives the elementary form of the
action (`ActData`), whose laws are equations of functors.

From it (`ActData.splitOpfib`):

* `push f x` is the action at `(x, a', f)`, whose first component is `a'` only propositionally, so
  its second component is transported (`ActData.push`);
* `olift f x` is the action at `(𝟙, f) : (x, a, 𝟙) ⟶ (x, a', f)`, transported (`homOfEq`);
* the factorization of `χ : x ⟶[f ≫ g] z` is the action at `(χ, g) : (x, a', f) ⟶ (z, a'', 𝟙)`,
  with `olift f x ≫ desc χ = χ` by the unit law, since `(𝟙, f) ≫ (χ, g) = L π (f ≫ g, χ)`;
* the factorization is unique: the associativity law at the morphism
  `ζ_c = ((𝟙, f), 𝟙) : ((x, π x, 𝟙), e, f) ⟶ ((x, e, f), e, 𝟙)` of `Rπ/E`, whose image by `μ`
  is the identity, is the triangle law of the adjunction `act ⊣ L π` over `E` given by lax
  idempotence (`ActData.L_map_actComma_zeta`), and a morphism `Ψ` out of `push f x` is the action at
  `ζ_c ≫ (Ψ, Ψ.base)`, which only depends on `olift f x ≫ Ψ` (`ActData.push_hom_ext`);
* `push (𝟙 a) x = x` by the unit law, and `push (f ≫ g) x = push g (push f x)` and the
  splitting of the chosen lifts by the associativity law at `((x, a', f), a', 𝟙) ⟶
  ((x, a', f), a'', g)`.

The splitting laws of the chosen lifts are fields of `SplitOpfib` typed through the rules for the
splitting of the pushforwards, `push (𝟙 a) x ↦ x`. They are proved up to heterogeneous equality
for the lifts of the cloven opfibration `ActData.opfib` (`olift_id_heq`, `olift_comp_heq`), whose
type `x ⟶[𝟙] Opfib.push (𝟙 a) x` compares with that of the field by its arguments, before the rule
rewrites either side.

The two constructions are inverse: the pushforwards and lifts of the split opfibration of the
action of `D` are those of `D` up to transports along `rfl`, and the action of the split opfibration
of an action is that action, by the uniqueness of factorizations.
-/

universe u

open CategoryTheory TwoCategory

namespace Displayed

open scoped Displayed

/-! ## Heterogeneous equalities -/

section HEq

variable {C : Type*} [Category C]

/-- Composites of heterogeneously equal morphisms between equal objects are heterogeneously
equal. -/
theorem comp_heq_comp {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'} (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  subst hX hY hZ
  cases hf
  cases hg
  rfl

/-- A morphism preceded by `eqToHom` is heterogeneously equal to it. -/
theorem eqToHom_comp_heq {X X' Y : C} (h : X = X') (f : X' ⟶ Y) : eqToHom h ≫ f ≍ f := by
  subst h
  simp

/-- A morphism followed by `eqToHom` is heterogeneously equal to it. -/
theorem comp_eqToHom_heq {X Y Y' : C} (f : X ⟶ Y) (h : Y = Y') : f ≫ eqToHom h ≍ f := by
  subst h
  simp

/-- `eqToHom h` is heterogeneously equal to the identity. -/
theorem eqToHom_heq_id' {X X' : C} (h : X = X') : eqToHom h ≍ 𝟙 X := by
  subst h
  rfl

/-- A functor sends heterogeneously equal morphisms between equal objects to heterogeneously equal
morphisms. -/
theorem Functor.map_heq' {C' : Type*} [Category C'] (F : C ⥤ C') {X X' Y Y' : C} (hX : X = X')
    (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : f ≍ f') : F.map f ≍ F.map f' := by
  subst hX hY
  cases h
  rfl

/-- A morphism heterogeneously equal to `f'` is `f'` between `eqToHom`s. -/
theorem heq_of_heq_of_eq_hom {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') {f : X ⟶ Y}
    {f' : X' ⟶ Y'} (h : f ≍ f') : f = eqToHom hX ≫ f' ≫ eqToHom hY.symm := by
  subst hX hY
  cases h
  simp

/-- The identities of equal objects are heterogeneously equal. -/
theorem id_heq_id {X X' : C} (h : X = X') : 𝟙 X ≍ 𝟙 X' := by
  subst h
  rfl

/-- Cancellation of a first factor through `eqToHom`, after replacing it by a heterogeneously equal
morphism. -/
theorem comp_eqToHom_comp_eq {X X' Y Y' Z : C} (hX : X = X') (hY : Y = Y') {u : X ⟶ Y}
    {u' : X' ⟶ Y'} (hu : u ≍ u') {v₁ v₂ : Y' ⟶ Z} (h : u' ≫ v₁ = u' ≫ v₂) :
    u ≫ eqToHom hY ≫ v₁ = u ≫ eqToHom hY ≫ v₂ := by
  subst hX hY
  cases hu
  simpa using h

end HEq

section Comma

variable {A B T : Type*} [Category A] [Category B] [Category T] {L : A ⥤ T} {R : B ⥤ T}

/-- Objects of a comma category with equal components, the morphisms heterogeneously, are equal. -/
theorem Comma.ext_heq {X Y : Comma L R} (hl : X.left = Y.left) (hr : X.right = Y.right)
    (hh : X.hom ≍ Y.hom) : X = Y := by
  obtain ⟨Xl, Xr, Xh⟩ := X
  obtain ⟨Yl, Yr, Yh⟩ := Y
  dsimp only at hl hr hh
  subst hl hr
  cases hh
  rfl

/-- Morphisms of a comma category between equal objects with heterogeneously equal components are
heterogeneously equal. -/
theorem Comma.hom_hext {X X' Y Y' : Comma L R} (hX : X = X') (hY : Y = Y') {φ : X ⟶ Y}
    {φ' : X' ⟶ Y'} (hl : φ.left ≍ φ'.left) (hr : φ.right ≍ φ'.right) : φ ≍ φ' := by
  subst hX hY
  exact heq_of_eq (Comma.hom_ext _ _ (eq_of_heq hl) (eq_of_heq hr))

end Comma

/-- 2-cells of `Cat` between equal 1-cells with heterogeneously equal components are heterogeneously
equal. -/
theorem Cat.hom₂_hext {C D : Cat.{u, u}} {F G F' G' : C ⟶ D} (hF : F = F') (hG : G = G')
    {α : F ⟶ G} {β : F' ⟶ G'} (h : ∀ X, α.toNatTrans.app X ≍ β.toNatTrans.app X) : α ≍ β := by
  subst hF hG
  exact heq_of_eq (Cat.Hom₂.ext (NatTrans.ext (funext fun X => eq_of_heq (h X))))

variable {E : Cat.{u, u}} {D : Displayed.{u, u} E}

/-! ## The action on `Rπ/E` of a functor over `E` -/

/-- The action `(c, e, g) ↦ (L c, e, g)` of a functor `L : π/E ⥤ D.Total` over `E` on the comma
category `Rπ/E` of the triples `(c, e, g : c.right ⟶ e)`. The equation `(L c).1 = c.right` is only
propositional, so `g` is transported along it. -/
def actComma (L : Comma D.π (𝟭 E) ⥤ D.Total) (hL : L ⋙ D.π = Comma.snd D.π (𝟭 E)) :
    Comma (Comma.snd D.π (𝟭 E)) (𝟭 E) ⥤ Comma D.π (𝟭 E) where
  obj X := ⟨L.obj X.left, X.right, eqToHom (Functor.congr_obj hL X.left) ≫ X.hom⟩
  map {X Y} Ψ := ⟨L.map Ψ.left, Ψ.right, by
    have h := Functor.congr_hom hL Ψ.left
    have w := Ψ.w
    simp only [Functor.comp_map, Comma.snd_map, Functor.id_map] at h w ⊢
    rw [h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl]
    rw [w]⟩
  map_id X := by ext <;> simp
  map_comp Ψ Ψ' := by ext <;> simp

variable (D) in
/-- The first factor `L π : D.Total ⥤ π/E`, `y ↦ (y, π y, 𝟙)`. -/
def lFun : D.Total ⥤ Comma D.π (𝟭 E) where
  obj y := ⟨y, y.1, 𝟙 y.1⟩
  map k := ⟨k, k.base, rfl⟩

variable (D) in
/-- The multiplication `Rπ/E ⥤ π/E` of `R`, `(c, e, g) ↦ (c.left, e, c.hom ≫ g)`. -/
def compFun : Comma (Comma.snd D.π (𝟭 E)) (𝟭 E) ⥤ Comma D.π (𝟭 E) where
  obj X := ⟨X.left.left, X.right, X.left.hom ≫ X.hom⟩
  map {X Y} Ψ := ⟨Ψ.left.left, Ψ.right, by
    have h₁ := Ψ.left.w
    have h₂ := Ψ.w
    simp only [Functor.id_map, Comma.snd_map] at h₁ h₂ ⊢
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]⟩

/-- `L π` of the comma factorization is `lFun`. -/
theorem lMap_toFunctor : D.πArr.lMap.toFunctor = D.lFun := by
  kernel_rfl'

/-- The multiplication of `R` at `π` is `compFun`. -/
theorem compMap_toFunctor : D.πArr.compMap.toFunctor = D.compFun := by
  kernel_rfl'

variable (D) in
/-- An action on the projection of `D` in elementary form: a functor `L : π/E ⥤ D.Total` over `E`,
a retraction of `L π`, satisfying the associativity law of an `R`-algebra with `R L` computed by
`actComma`. -/
structure ActData where
  /-- The action. -/
  L : Comma D.π (𝟭 E) ⥤ D.Total
  fst : L ⋙ D.π = Comma.snd D.π (𝟭 E)
  unit : D.lFun ⋙ L = 𝟭 D.Total
  assoc : D.compFun ⋙ L = actComma L fst ⋙ L

namespace RAlgStr

variable (a : RAlgStr E D)

/-- An action is the identity on the codomain, by the unit law. -/
theorem act_right : a.act.right = 𝟙 E := by
  kernel_exact congrArg Arr.Hom.right a.unit

/-- An action is a retraction of `L π`, by the unit law. -/
theorem lMap_comp_act_left : D.πArr.lMap ≫ a.act.left = 𝟙 _ := by
  kernel_exact congrArg Arr.Hom.left a.unit

/-- The action, as a functor `π/E ⥤ D.Total`. -/
def L : Comma D.π (𝟭 E) ⥤ D.Total :=
  a.act.left.toFunctor

/-- The action lies over `E`, by the equation of its square and the unit law. -/
theorem L_fst : a.L ⋙ D.π = Comma.snd D.π (𝟭 E) :=
  ((Cat.Hom.comp_toFunctor a.act.left D.πArr.hom).symm.trans
    (congrArg Cat.Hom.toFunctor a.act.w)).trans ((Cat.Hom.comp_toFunctor _ _).trans
      (congrArg ((rMonad.T.obj D.πArr).hom.toFunctor ⋙ ·)
        (congrArg Cat.Hom.toFunctor a.act_right)))

/-- The action is a retraction of `L π`, as functors. -/
theorem L_unit : D.lFun ⋙ a.L = 𝟭 D.Total :=
  (congrArg (· ⋙ a.L) lMap_toFunctor.symm).trans
    ((Cat.Hom.comp_toFunctor D.πArr.lMap a.act.left).symm.trans
      (congrArg Cat.Hom.toFunctor a.lMap_comp_act_left))

/-- The action, with its codomain component replaced by the identity, which it is. -/
def nAct : rMonad.T.obj D.πArr ⟶ D.πArr :=
  ⟨a.act.left, 𝟙 E, by rw [← a.act_right]⟩

/-- An action is its normalization. -/
theorem act_eq : a.act = a.nAct :=
  Arr.Hom.ext rfl a.act_right

/-- **`R` applied to an action is `actComma`**, by the universal property of `π/E`: their composites
with the legs agree by `rfl`, and their 2-cells, `g` and `eqToHom _ ≫ g` at `(c, e, g)`, up to
the transport along `(L c).1 = c.right`. Stated for `actComma`, whose objects are well typed,
rather than for `commaMap` of an action, whose objects are only typed by the rule for the square of
the action. -/
theorem commaMap_nAct : Arr.commaMap a.nAct = (actComma a.L a.L_fst).toCatHom := by
  have hl : Arr.commaMap a.nAct ≫ (HasCommas.commaCone D.πArr.hom (𝟙 D.πArr.cod)).left =
      (actComma a.L a.L_fst).toCatHom ≫ (HasCommas.commaCone D.πArr.hom (𝟙 D.πArr.cod)).left := by
    kernel_rfl'
  have hr : Arr.commaMap a.nAct ≫ (HasCommas.commaCone D.πArr.hom (𝟙 D.πArr.cod)).right =
      (actComma a.L a.L_fst).toCatHom ≫ (HasCommas.commaCone D.πArr.hom (𝟙 D.πArr.cod)).right := by
    kernel_rfl'
  refine (HasCommas.isComma D.πArr.hom (𝟙 D.πArr.cod)).ext (Comma.ext_heq hl hr ?_)
  refine Cat.hom₂_hext (by kernel_exact congrArg (· ≫ D.πArr.hom) hl)
    (by kernel_exact congrArg (· ≫ 𝟙 D.πArr.cod) hr) fun X => ?_
  kernel_exact (eqToHom_comp_heq (Functor.congr_obj a.L_fst X.left) X.hom).symm

/-- The associativity law of an action, with `R act` computed by `actComma`. -/
theorem L_assoc : D.compFun ⋙ a.L = actComma a.L a.L_fst ⋙ a.L := by
  have h : D.πArr.compMap ≫ a.act.left = Arr.commaMap a.nAct ≫ a.act.left := by
    have e := a.assoc
    rw [a.act_eq] at e
    kernel_exact congrArg Arr.Hom.left e
  rw [a.commaMap_nAct] at h
  exact (congrArg (· ⋙ a.L) compMap_toFunctor.symm).trans ((Cat.Hom.comp_toFunctor _ _).symm.trans
    ((congrArg Cat.Hom.toFunctor h).trans (Cat.Hom.comp_toFunctor _ _)))

/-- The elementary form of an `R`-algebra structure. -/
def toActData : ActData D :=
  ⟨a.L, a.L_fst, a.L_unit, a.L_assoc⟩

end RAlgStr

/-! ## Transports in the total category -/

variable (D) in
/-- A morphism `F : p ⟶ q` of the total category, with `p = (a, x)` and `q = (a', y)`, as a
displayed morphism `x ⟶[f] y`, for a base morphism `f` heterogeneously equal to its base. -/
def homOfEq {p q : D.Total} (F : p ⟶ q) {a a' : E} {x : D.Ob a} {y : D.Ob a'}
    (hp : p = D.tot x) (hq : q = D.tot y) {f : a ⟶ a'} (hf : F.base ≍ f) : x ⟶[f] y := by
  subst hp hq
  exact D.castBase (eq_of_heq hf) F.fiber

/-- `homOfEq F` is `F`, up to the transports. -/
theorem totalMk_homOfEq {p q : D.Total} (F : p ⟶ q) {a a' : E} {x : D.Ob a} {y : D.Ob a'}
    (hp : p = D.tot x) (hq : q = D.tot y) {f : a ⟶ a'} (hf : F.base ≍ f) :
    D.totalMk f (D.homOfEq F hp hq hf) ≍ F := by
  subst hp hq
  obtain rfl : F.base = f := eq_of_heq hf
  rfl

/-- The second component of `(a, x)`, transported along an equation of its first component, is
`x`. -/
theorem cast_snd_eq {p : D.Total} {a : E} (h : p.1 = a) {x : D.Ob a} (hp : p = D.tot x) :
    (cast (congrArg D.Ob h) p.2 : D.Ob a) = x := by
  subst hp
  rfl

/-- The second components of equal objects of the total category, transported to the same fibre,
are equal. -/
theorem cast_snd_congr {p q : D.Total} (hpq : p = q) {a : E} (hp : p.1 = a) (hq : q.1 = a) :
    (cast (congrArg D.Ob hp) p.2 : D.Ob a) = cast (congrArg D.Ob hq) q.2 := by
  subst hpq
  rfl

/-- `homOfEq F` is the displayed component of `F`, up to the transports. -/
theorem homOfEq_heq {p q : D.Total} (F : p ⟶ q) {a a' : E} {x : D.Ob a} {y : D.Ob a'}
    (hp : p = D.tot x) (hq : q = D.tot y) {f : a ⟶ a'} (hf : F.base ≍ f) :
    D.homOfEq F hp hq hf ≍ F.fiber := by
  subst hp hq
  obtain rfl : F.base = f := eq_of_heq hf
  rfl

/-- The base components of heterogeneously equal morphisms between equal objects are
heterogeneously equal. -/
theorem base_heq_of_heq {p q p' q' : D.Total} (hp : p = p') (hq : q = q') {F : p ⟶ q}
    {G : p' ⟶ q'} (h : F ≍ G) : F.base ≍ G.base := by
  subst hp hq
  cases h
  rfl

/-- Displayed morphisms whose morphisms of the total category are heterogeneously equal are
heterogeneously equal. -/
theorem fiber_heq_of_totalMk_heq {a a' : E} {f : a ⟶ a'} {x : D.Ob a} {y y' : D.Ob a'}
    (hy : y = y') {φ : x ⟶[f] y} {φ' : x ⟶[f] y'} (h : D.totalMk f φ ≍ D.totalMk f φ') :
    φ ≍ φ' := by
  subst hy
  exact Section.fiber_heq_of_eq (eq_of_heq h)

/-! ## The split opfibration of an action -/

namespace ActData

variable (d : ActData D)

/-- The action lies over `E`, on objects. -/
theorem fst_obj (c : Comma D.π (𝟭 E)) : (d.L.obj c).1 = c.right :=
  Functor.congr_obj d.fst c

/-- The action lies over `E`, on morphisms. -/
theorem base_map {c c' : Comma D.π (𝟭 E)} (φ : c ⟶ c') : (d.L.map φ).base ≍ φ.right :=
  Functor.hcongr_hom d.fst φ

/-- The unit law, on objects. -/
theorem unit_obj (y : D.Total) : d.L.obj (D.lFun.obj y) = y :=
  Functor.congr_obj d.unit y

/-- The unit law, on morphisms. -/
theorem unit_map {y y' : D.Total} (k : y ⟶ y') : d.L.map (D.lFun.map k) ≍ k :=
  Functor.hcongr_hom d.unit k

/-- The pushforward of `x` along `f`, the action at `(x, a', f)`. -/
def push {a a' : E} (f : a ⟶ a') (x : D.Ob a) : D.Ob a' :=
  cast (congrArg D.Ob (d.fst_obj (D.commaMk f x))) (d.L.obj (D.commaMk f x)).2

/-- The action at `(x, a', f)` is the pushforward of `x` along `f`. -/
theorem tot_push {a a' : E} (f : a ⟶ a') (x : D.Ob a) :
    d.L.obj (D.commaMk f x) = D.tot (d.push f x) :=
  Sigma.ext (d.fst_obj _) (cast_heq _ _).symm

/-- The chosen lift of `f` at `x`, the action at `(𝟙, f) : (x, a, 𝟙) ⟶ (x, a', f)`. -/
def olift {a a' : E} (f : a ⟶ a') (x : D.Ob a) : x ⟶[f] d.push f x :=
  D.homOfEq (d.L.map (D.commaUnitHom f x)) (d.unit_obj (D.tot x)) (d.tot_push f x)
    (d.base_map _)

/-- The morphism `(χ, g) : (x, a', f) ⟶ (z, a'', 𝟙)` of `π/E`, for `χ : x ⟶[f ≫ g] z`. -/
def descHom {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') {z : D.Ob a''}
    (χ : x ⟶[f ≫ g] z) : D.commaMk f x ⟶ (⟨D.tot z, a'', 𝟙 a''⟩ : Comma D.π (𝟭 E)) :=
  ⟨D.totalMk (f ≫ g) χ, g, rfl⟩

/-- The factorization of `χ : x ⟶[f ≫ g] z` through the chosen lift, the action at
`(χ, g) : (x, a', f) ⟶ (z, a'', 𝟙)`. -/
def desc {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') {z : D.Ob a''}
    (χ : x ⟶[f ≫ g] z) : d.push f x ⟶[g] z :=
  D.homOfEq (d.L.map (descHom f x g χ)) (d.tot_push f x) (d.unit_obj (D.tot z)) (d.base_map _)

/-- The chosen lift is the action at `(𝟙, f)`, up to the transports. -/
theorem totalMk_olift {a a' : E} (f : a ⟶ a') (x : D.Ob a) :
    D.totalMk f (d.olift f x) ≍ d.L.map (D.commaUnitHom f x) :=
  totalMk_homOfEq _ _ _ _

/-- **The factorization law**: `olift f x ≫ desc χ = χ`, by the unit law, since `(𝟙, f) ≫ (χ, g)`
is `L π` applied to `(f ≫ g, χ)`. -/
theorem olift_comp_desc {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'')
    {z : D.Ob a''} (χ : x ⟶[f ≫ g] z) : d.olift f x ≫ᵈ d.desc f x g χ = χ := by
  have e₁ : D.totalMk f (d.olift f x) ≫ D.totalMk g (d.desc f x g χ) ≍
      d.L.map (D.commaUnitHom f x) ≫ d.L.map (descHom f x g χ) :=
    comp_heq_comp (d.unit_obj _).symm (d.tot_push f x).symm (d.unit_obj _).symm
      (totalMk_homOfEq _ _ _ _) (totalMk_homOfEq _ _ _ _)
  have e₂ : D.commaUnitHom f x ≫ descHom f x g χ = D.lFun.map (D.totalMk (f ≫ g) χ) :=
    Comma.hom_ext _ _ rfl rfl
  have e₃ : d.L.map (D.commaUnitHom f x) ≫ d.L.map (descHom f x g χ) ≍ D.totalMk (f ≫ g) χ :=
    (heq_of_eq ((d.L.map_comp _ _).symm.trans (congrArg d.L.map e₂))).trans (d.unit_map _)
  exact eq_of_heq (Section.fiber_heq_of_eq (eq_of_heq (e₁.trans e₃)))

/-! ### Uniqueness of factorizations, from the associativity law -/

/-- The morphism `ζ_c = ((𝟙, f), 𝟙) : ((x, π x, 𝟙), e, f) ⟶ (c, e, 𝟙)` of `Rπ/E`, for
`c = (x, e, f)`: the component at `c` of the 2-cell of lax idempotence. -/
def zeta (c : Comma D.π (𝟭 E)) :
    (⟨D.lFun.obj c.left, c.right, c.hom⟩ : Comma (Comma.snd D.π (𝟭 E)) (𝟭 E)) ⟶
      ⟨c, c.right, 𝟙 c.right⟩ :=
  ⟨⟨𝟙 c.left, c.hom, rfl⟩, 𝟙 c.right, rfl⟩

/-- `μ ζ_c` is the identity of `c`. -/
theorem L_map_compFun_zeta (c : Comma D.π (𝟭 E)) :
    d.L.map (D.compFun.map (zeta c)) ≍ 𝟙 (d.L.obj c) := by
  have e : D.compFun.map (zeta c) = 𝟙 c :=
    Comma.hom_ext _ _ rfl rfl
  exact heq_of_eq ((congrArg d.L.map e).trans (d.L.map_id c))

/-- The triangle law of the adjunction `act ⊣ L π` over `E`: the action sends `ζ_c`, mapped by
`R act`, to the identity. -/
theorem L_map_actComma_zeta (c : Comma D.π (𝟭 E)) :
    d.L.map ((actComma d.L d.fst).map (zeta c)) ≍ 𝟙 (d.L.obj c) :=
  (Functor.hcongr_hom d.assoc (zeta c)).symm.trans (d.L_map_compFun_zeta c)

/-- `R act` at `(c, e, 𝟙)` is `L π (act c)`, up to the transport of its codomain component. -/
theorem actComma_obj_tgt (c : Comma D.π (𝟭 E)) :
    (actComma d.L d.fst).obj ⟨c, c.right, 𝟙 c.right⟩ = D.lFun.obj (d.L.obj c) :=
  Comma.ext_heq rfl (d.fst_obj c).symm
    ((heq_of_eq (Category.comp_id (eqToHom (d.fst_obj c)))).trans (eqToHom_heq_id' _))

/-- The morphism `(Ψ, Ψ.base) : (L c, e, 𝟙) ⟶ (w, π w, 𝟙)` of `π/E`, for `Ψ : L c ⟶ w`. -/
def thetaHom (c : Comma D.π (𝟭 E)) {w : D.Total} (Ψ : d.L.obj c ⟶ w) :
    (actComma d.L d.fst).obj ⟨c, c.right, 𝟙 c.right⟩ ⟶ D.lFun.obj w :=
  ⟨Ψ, eqToHom (d.fst_obj c).symm ≫ Ψ.base, by
    change Ψ.base ≫ 𝟙 _ = (eqToHom (d.fst_obj c) ≫ 𝟙 _) ≫ eqToHom (d.fst_obj c).symm ≫ Ψ.base
    simp⟩

/-- `(Ψ, Ψ.base)` is `L π Ψ`, up to the transports. -/
theorem thetaHom_heq (c : Comma D.π (𝟭 E)) {w : D.Total} (Ψ : d.L.obj c ⟶ w) :
    d.thetaHom c Ψ ≍ D.lFun.map Ψ :=
  Comma.hom_hext (d.actComma_obj_tgt c) rfl HEq.rfl (eqToHom_comp_heq _ _)

/-- The morphism `ζ_c ≫ (Ψ, Ψ.base)` of `π/E`, whose image by the action is `Ψ`. -/
def theta (c : Comma D.π (𝟭 E)) {w : D.Total} (Ψ : d.L.obj c ⟶ w) :
    (actComma d.L d.fst).obj ⟨D.lFun.obj c.left, c.right, c.hom⟩ ⟶ D.lFun.obj w :=
  (actComma d.L d.fst).map (zeta c) ≫ d.thetaHom c Ψ

/-- **The action sends `ζ_c ≫ (Ψ, Ψ.base)` to `Ψ`**, by the triangle law and the unit law. -/
theorem L_map_theta (c : Comma D.π (𝟭 E)) {w : D.Total} (Ψ : d.L.obj c ⟶ w) :
    d.L.map (d.theta c Ψ) ≍ Ψ := by
  have h₂ : d.L.map (d.thetaHom c Ψ) ≍ Ψ :=
    (Functor.map_heq' d.L (d.actComma_obj_tgt c) rfl (d.thetaHom_heq c Ψ)).trans (d.unit_map Ψ)
  have h₃ := comp_heq_comp (Functor.congr_obj d.assoc _).symm
    ((congrArg d.L.obj (d.actComma_obj_tgt c)).trans (d.unit_obj _)) (d.unit_obj _)
    (d.L_map_actComma_zeta c) h₂
  kernel_exact h₃

/-- Morphisms out of the action at `c` are determined by their composites with the action at
`(𝟙, f)` and by their bases. -/
theorem hom_ext_of_unit (c : Comma D.π (𝟭 E)) {w : D.Total} {Ψ₁ Ψ₂ : d.L.obj c ⟶ w}
    (hl : d.L.map (zeta c).left ≫ Ψ₁ = d.L.map (zeta c).left ≫ Ψ₂)
    (hb : Ψ₁.base = Ψ₂.base) : Ψ₁ = Ψ₂ := by
  have e : d.theta c Ψ₁ = d.theta c Ψ₂ :=
    Comma.hom_ext _ _ hl (by kernel_exact congrArg (𝟙 c.right ≫ eqToHom (d.fst_obj c).symm ≫ ·) hb)
  exact eq_of_heq ((d.L_map_theta c Ψ₁).symm.trans
    ((heq_of_eq (congrArg d.L.map e)).trans (d.L_map_theta c Ψ₂)))

/-- **Uniqueness of factorizations**: morphisms out of `push f x` are determined by their composites
with the chosen lift. -/
theorem push_hom_ext {a a' a'' : E} {f : a ⟶ a'} {x : D.Ob a} {g : a' ⟶ a''} {z : D.Ob a''}
    {ψ₁ ψ₂ : d.push f x ⟶[g] z} (h : d.olift f x ≫ᵈ ψ₁ = d.olift f x ≫ᵈ ψ₂) : ψ₁ = ψ₂ := by
  have key : eqToHom (d.tot_push f x) ≫ D.totalMk g ψ₁ =
      eqToHom (d.tot_push f x) ≫ D.totalMk g ψ₂ :=
    d.hom_ext_of_unit (D.commaMk f x)
      (comp_eqToHom_comp_eq (u := d.L.map (D.commaUnitHom f x))
        (u' := D.totalMk f (d.olift f x)) (d.unit_obj (D.tot x)) (d.tot_push f x)
        (d.totalMk_olift f x).symm (congrArg (D.totalMk (f ≫ g)) h)) rfl
  exact eq_of_heq (Section.fiber_heq_of_eq ((cancel_epi _).1 key))

/-- **The cloven opfibration of an action**: the chosen pushforward of `x` along `f` is the action
at `(x, a', f)`, and the chosen lift its action at `(𝟙, f)`, opcartesian by the triangle law of
the adjunction of lax idempotence, which comes from the associativity law. -/
@[instance_reducible]
def opfib : Opfib D where
  push f x := d.push f x
  olift f x := d.olift f x
  isOpcartesianOlift f x :=
    { desc := fun g _ χ => d.desc f x g χ
      desc_fac := fun g _ χ => d.olift_comp_desc f x g χ
      desc_uniq := fun _ hψ => d.push_hom_ext (hψ.trans (d.olift_comp_desc f x _ _).symm) }

/-! ### The splitting laws, from the unit and associativity laws -/

/-- `push (𝟙 a) x = x`, by the unit law. -/
theorem push_id {a : E} (x : D.Ob a) : d.push (𝟙 a) x = x :=
  cast_snd_eq (d.fst_obj _) (d.unit_obj (D.tot x))

/-- `R act` at `((x, a', f), a'', g)` is `(push f x, a'', g)`. -/
theorem actComma_obj_commaMk {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') :
    (actComma d.L d.fst).obj ⟨D.commaMk f x, a'', g⟩ = D.commaMk g (d.push f x) :=
  Comma.ext_heq (d.tot_push f x) rfl (eqToHom_comp_heq _ _)

/-- The action at `(x, a'', f ≫ g)` is at `(push f x, a'', g)`, by the associativity law. -/
theorem L_obj_commaMk_comp {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') :
    d.L.obj (D.commaMk (f ≫ g) x) = d.L.obj (D.commaMk g (d.push f x)) :=
  (Functor.congr_obj d.assoc ⟨D.commaMk f x, a'', g⟩).trans
    (congrArg d.L.obj (d.actComma_obj_commaMk f x g))

/-- `push (f ≫ g) x = push g (push f x)`, by the associativity law. -/
theorem push_comp {a a' a'' : E} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    d.push (f ≫ g) x = d.push g (d.push f x) :=
  cast_snd_congr (d.L_obj_commaMk_comp f x g) (d.fst_obj _) (d.fst_obj _)

/-- The pre-split opfibration of an action. -/
@[instance_reducible]
def preSplitOpfib : PreSplitOpfib D :=
  @PreSplitOpfib.mk _ _ D d.opfib (fun x => d.push_id x) (fun f g x => d.push_comp f g x)

/-- `olift (𝟙 a) x = 𝟙`, up to `push (𝟙 a) x = x`. -/
theorem olift_id_heq {a : E} (x : D.Ob a) : @Opfib.olift _ _ D d.opfib _ _ (𝟙 a) x ≍ 𝟙ᵈ x := by
  have e : D.commaUnitHom (𝟙 a) x = 𝟙 (D.lFun.obj (D.tot x)) :=
    Comma.hom_ext _ _ rfl rfl
  have h : D.totalMk (𝟙 a) (d.olift (𝟙 a) x) ≍ D.totalMk (𝟙 a) (𝟙ᵈ x) :=
    (d.totalMk_olift (𝟙 a) x).trans ((heq_of_eq ((congrArg d.L.map e).trans (d.L.map_id _))).trans
      (id_heq_id (d.unit_obj _)))
  exact fiber_heq_of_totalMk_heq (d.push_id x) h

/-- The morphism `(𝟙, g) : ((x, a', f), a', 𝟙) ⟶ ((x, a', f), a'', g)` of `Rπ/E`. -/
def compUnitHom {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') :
    (⟨D.commaMk f x, a', 𝟙 a'⟩ : Comma (Comma.snd D.π (𝟭 E)) (𝟭 E)) ⟶ ⟨D.commaMk f x, a'', g⟩ :=
  ⟨𝟙 _, g, rfl⟩

/-- The action at `μ (𝟙, g)`, the morphism `(𝟙, g) : (x, a', f) ⟶ (x, a'', f ≫ g)`, is the chosen
lift of `g` at `push f x`, by the associativity law. -/
theorem L_map_compFun_compUnitHom {a a' a'' : E} (f : a ⟶ a') (x : D.Ob a) (g : a' ⟶ a'') :
    d.L.map (D.compFun.map (compUnitHom f x g)) ≍ D.totalMk g (d.olift g (d.push f x)) := by
  have hsrc : (actComma d.L d.fst).obj ⟨D.commaMk f x, a', 𝟙 a'⟩ =
      (⟨D.tot (d.push f x), a', 𝟙 a'⟩ : Comma D.π (𝟭 E)) :=
    Comma.ext_heq (d.tot_push f x) rfl
      ((heq_of_eq (Category.comp_id (eqToHom (d.fst_obj (D.commaMk f x))))).trans
        ((eqToHom_heq_id' _).trans (id_heq_id (d.fst_obj (D.commaMk f x)))))
  have h₂ : (actComma d.L d.fst).map (compUnitHom f x g) ≍ D.commaUnitHom g (d.push f x) :=
    Comma.hom_hext hsrc (d.actComma_obj_commaMk f x g)
      ((heq_of_eq (d.L.map_id _)).trans (id_heq_id (d.tot_push f x))) HEq.rfl
  exact (Functor.hcongr_hom d.assoc (compUnitHom f x g)).trans
    ((Functor.map_heq' d.L hsrc (d.actComma_obj_commaMk f x g) h₂).trans
      (d.totalMk_olift g (d.push f x)).symm)

/-- `olift (f ≫ g) x = olift f x ≫ olift g (push f x)`, up to
`push (f ≫ g) x = push g (push f x)`. -/
theorem olift_comp_heq {a a' a'' : E} (f : a ⟶ a') (g : a' ⟶ a'') (x : D.Ob a) :
    @Opfib.olift _ _ D d.opfib _ _ (f ≫ g) x ≍
      @Opfib.olift _ _ D d.opfib _ _ f x ≫ᵈ
        @Opfib.olift _ _ D d.opfib _ _ g (@Opfib.push _ _ D d.opfib _ _ f x) := by
  have e : D.commaUnitHom (f ≫ g) x = D.commaUnitHom f x ≫ D.compFun.map (compUnitHom f x g) :=
    Comma.hom_ext _ _ rfl rfl
  have h : D.totalMk (f ≫ g) (d.olift (f ≫ g) x) ≍
      D.totalMk f (d.olift f x) ≫ D.totalMk g (d.olift g (d.push f x)) :=
    (d.totalMk_olift (f ≫ g) x).trans ((heq_of_eq ((congrArg d.L.map e).trans
      (d.L.map_comp _ _))).trans (comp_heq_comp (d.unit_obj _) (d.tot_push f x)
        ((d.L_obj_commaMk_comp f x g).trans (d.tot_push g (d.push f x)))
        (d.totalMk_olift f x).symm (d.L_map_compFun_compUnitHom f x g)))
  exact fiber_heq_of_totalMk_heq (d.push_comp f g x) h

/-- **The split opfibration of an action.** -/
@[instance_reducible]
def splitOpfib : SplitOpfib D :=
  @SplitOpfib.mk _ _ D d.preSplitOpfib (fun x => eq_of_heq (d.olift_id_heq x))
    (fun f g x => eq_of_heq (d.olift_comp_heq f g x))

/-- The action of the split opfibration of an action is that action. -/
theorem actMap_splitOpfib {c c' : Comma D.π (𝟭 E)} (φ : c ⟶ c') :
    @actMap E D d.splitOpfib c c' φ ≍ d.L.map φ := by
  let _ := d.splitOpfib
  have hc : d.L.obj c = D.actObj c := d.tot_push c.hom c.left.2
  have hc' : d.L.obj c' = D.actObj c' := d.tot_push c'.hom c'.left.2
  let G : D.actObj c ⟶ D.actObj c' := eqToHom hc.symm ≫ d.L.map φ ≫ eqToHom hc'
  have hG : G ≍ d.L.map φ :=
    (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  have e : D.commaUnitHom c.hom c.left.2 ≫ φ =
      D.lFun.map φ.left ≫ D.commaUnitHom c'.hom c'.left.2 :=
    Comma.hom_ext _ _ rfl φ.w.symm
  have h₁ : D.totalMk c.hom (d.olift c.hom c.left.2) ≫ G ≍
      φ.left ≫ D.totalMk c'.hom (d.olift c'.hom c'.left.2) :=
    (comp_heq_comp (d.unit_obj _).symm hc.symm hc'.symm (d.totalMk_olift _ _) hG).trans
      ((heq_of_eq (((d.L.map_comp _ _).symm.trans (congrArg d.L.map e)).trans
        (d.L.map_comp _ _))).trans (comp_heq_comp (d.unit_obj _) (d.unit_obj _) hc'
          (d.unit_map φ.left) (d.totalMk_olift _ _).symm))
  refine (heq_of_eq (D.actObj_hom_ext (F := D.actMap φ) (G := G)
    (eq_of_heq ((d.base_map φ).symm.trans (base_heq_of_heq hc hc' hG.symm))) ?_)).trans hG
  exact (D.olift_comp_actMap_heq φ).trans (Section.fiber_heq_of_eq (eq_of_heq h₁)).symm

end ActData

/-! ## The equivalence -/

variable (D) in
/-- `R`-algebra structures with the same action are equal. -/
theorem RAlgStr.ext {a b : RAlgStr E D} (h : a.act = b.act) : a = b := by
  obtain ⟨act, _, _⟩ := a
  obtain ⟨act', _, _⟩ := b
  dsimp only at h
  subst h
  rfl

variable (D) in
/-- **The split opfibration structures on `D` are the `R`-algebra structures on its
projection.** -/
def splitOpfibEquiv : SplitOpfib D ≃ RAlgStr E D where
  toFun := SplitOpfib.toRAlgStr D
  invFun a := a.toActData.splitOpfib
  left_inv s := by
    let d := (SplitOpfib.toRAlgStr D s).toActData
    refine SplitOpfib.ext' D _ s (fun {a a'} f x => ?_) (fun {a a'} f x => ?_)
    · kernel_exact cast_eq (congrArg D.Ob (Eq.refl a'))
        (@Opfib.push _ _ D s.toPreSplitOpfib.toOpfib _ _ f x)
    · kernel_exact (homOfEq_heq (d.L.map (D.commaUnitHom f x)) (d.unit_obj (D.tot x))
        (d.tot_push f x) (d.base_map _)).trans
          (heq_of_eq (@actMap_commaUnitHom_fiber E D s _ _ f x))
  right_inv a := by
    refine RAlgStr.ext D (Arr.Hom.ext (Cat.Hom.ext (Functor.hext (fun c => ?_)
      fun c c' φ => a.toActData.actMap_splitOpfib φ)) a.act_right.symm)
    exact (a.toActData.tot_push c.hom c.left.2).symm

end Displayed
