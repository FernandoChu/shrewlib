import ComprehensionCategory.Basic
import ComprehensionCategory.Term

/-!
# Maps of comprehension categories

A map from a comprehension category `D` over `C` to a comprehension category `E` over `C'`, over a
functor `F : C ⥤ C'` (`ComprehensionMap F D E`), consists of

* a displayed functor from `D` to `E` over `F`, with actions `obj` and `map`, that preserves
  cartesian morphisms, and
* a comparison morphism `cmp A : F.obj (Γ ▹ A) ⟶ F.obj Γ ▹ obj A` for each type `A` in context
  `Γ`, over `F.obj Γ` (`cmp_proj`) and natural in `A` (`cmp_natural`).

The comparisons are the components of a 2-cell from the comprehension functor of `D` followed by
`codMap F`, the action of `F` on the codomain displayed categories, to the displayed functor
followed by the comprehension functor of `E`. The map is

* *pseudo* (`PseudoComprehensionMap`) if the comparisons are isomorphisms, given with their
  inverses, and
* *strict* (`StrictComprehensionMap`) if the two composites into `cod C'` are equal: on objects
  (`compr_obj`, on the underlying `PreStrictComprehensionMap`), so that `F.obj (Γ ▹ A)` is
  `F.obj Γ ▹ obj A` and `F.map (𝐩 A)` is `𝐩 (obj A)`, and on morphisms (`compr_map`); and if it
  preserves the chosen cartesian lifts: substitution of types (`obj_pull`,
  `obj A⦃σ⦄ = (obj A)⦃F.map σ⦄`) and the lifts themselves (`map_clift`).

The two equations on the comprehension functors are rewrite rules. The equation on objects makes
the one on morphisms well-typed as a plain equation, and with both, a strict map is pseudo with
identity comparisons (`StrictComprehensionMap.toPseudo`), whose laws hold by `rfl`. The
preservation of the chosen lifts is not a rule: `obj_pull`, oriented as for `CartesianFunctor`,
would rewrite `obj A⦃σ⦄` to a form on which `compr_obj` no longer applies. So `map_clift` is a
heterogeneous equality, and in the models both hold by `rfl`.

All three kinds have identities and compose, over the identity and composite functors; for strict
maps, the axioms on the comprehension functors of the identity and the composite hold by `rfl`.

A strict map sends the terms of `A` to terms of `obj A` (`StrictComprehensionMap.mapTm`): the
image of a section of `𝐩 A` is a section of `F.map (𝐩 A)`, which is `𝐩 (obj A)`. Over the identity,
this is a bijection `Tm(Γ, A) ≃ Tm(Γ, obj A)` (`StrictComprehensionMap.tmEquiv`), with the same
sections, whose laws hold by `rfl`. These are the rules of Kovács' strict family inclusions,
Lift-Intro and Lift-Elim, while Lift-Ext, `Γ ▹ obj A = Γ ▹ A`, is the rule `compr_obj`.

Preserving the chosen lifts, a strict map preserves the morphisms `𝐪`
(`StrictComprehensionMap.q_obj`), and over the identity the bijection on terms commutes with
substitution (`StrictComprehensionMap.tmEquiv_pull`), heterogeneously: the two terms are of the
types `obj A⦃σ⦄` and `(obj A)⦃σ⦄`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {C'' : Type u₅} [Category.{v₅} C'']

/-! ## Maps -/

variable (F : C ⥤ C') (D : Displayed.{v₃, u₃} C) [Fib D] [Comprehension D]
  (E : Displayed.{v₄, u₄} C') [Fib E] [Comprehension E]

/-- A map of comprehension categories over `F`: a displayed functor preserving cartesian
morphisms, with natural comparisons `F.obj (Γ ▹ A) ⟶ F.obj Γ ▹ obj A` over `F.obj Γ`. -/
structure ComprehensionMap extends DispFunctor F D E where
  /-- The displayed functor preserves cartesian morphisms. -/
  isCartesianMap : toDispFunctor.PreservesCartesian
  /-- The comparison from the image of the extended context. -/
  cmp : ∀ {Γ : C} (A : D.Ty Γ), F.obj (Γ ▹ A) ⟶ F.obj Γ ▹ obj A
  /-- The comparison lies over `F.obj Γ`. -/
  cmp_proj : ∀ {Γ : C} (A : D.Ty Γ), cmp A ≫ 𝐩 (obj A) = F.map (𝐩 A)
  /-- The comparison is natural. -/
  cmp_natural : ∀ {Γ Γ' : C} {f : Γ ⟶ Γ'} {A : D.Ty Γ} {B : D.Ty Γ'} (φ : A ⟶[f] B),
    F.map (D.extMap φ) ≫ cmp B = cmp A ≫ E.extMap (map φ)

/-- A pseudo map of comprehension categories: a map whose comparisons are isomorphisms. -/
structure PseudoComprehensionMap extends ComprehensionMap F D E where
  /-- The inverse of the comparison. -/
  cmpInv : ∀ {Γ : C} (A : D.Ty Γ), F.obj Γ ▹ obj A ⟶ F.obj (Γ ▹ A)
  cmp_cmpInv : ∀ {Γ : C} (A : D.Ty Γ), cmp A ≫ cmpInv A = 𝟙 _ := by intros; rfl
  cmpInv_cmp : ∀ {Γ : C} (A : D.Ty Γ), cmpInv A ≫ cmp A = 𝟙 _ := by intros; rfl

/-- A pre-strict map of comprehension categories: a displayed functor preserving cartesian
morphisms, with which the comprehension functors commute on objects. This axiom is a rewrite
rule. -/
structure PreStrictComprehensionMap extends DispFunctor F D E where
  /-- The displayed functor preserves cartesian morphisms. -/
  isCartesianMap : toDispFunctor.PreservesCartesian
  /-- The comprehension functors commute on objects: `F.obj Γ ▹ obj A` is `F.obj (Γ ▹ A)`, with
  projection `F.map (𝐩 A)`. -/
  compr_obj : ∀ {Γ : C} (A : D.Ty Γ), E.compr.obj (obj A) = (codMap F).obj (D.compr.obj A)

attribute [rewrite_rule] PreStrictComprehensionMap.compr_obj

/-- A strict map of comprehension categories: a pre-strict map with which the comprehension
functors commute on morphisms too, and which preserves the chosen cartesian lifts, hence
substitution. As for `SplitFib`, the pre-strict map is a field rather than a parent, so that the
rule `compr_obj` applies to the axiom on morphisms, which is a rule too.

The preservation of the chosen lifts is not a rule: oriented as for `CartesianFunctor`, `obj_pull`
would rewrite `obj A⦃σ⦄` to `(obj A)⦃F.map σ⦄`, on which `compr_obj` no longer applies. So the
lifts are compared heterogeneously (`map_clift`), their domains being equal by `obj_pull`. -/
structure StrictComprehensionMap where
  /-- The underlying pre-strict map. -/
  toPre : PreStrictComprehensionMap F D E
  /-- The comprehension functors commute on morphisms. -/
  compr_map : ∀ {Γ Γ' : C} {f : Γ ⟶ Γ'} {A : D.Ty Γ} {B : D.Ty Γ'} (φ : A ⟶[f] B),
    E.compr.map (toPre.map φ) = (codMap F).map (D.compr.map φ) := by intros; rfl
  /-- Substitution of types is preserved: `obj A⦃σ⦄` is `(obj A)⦃F.map σ⦄`. -/
  obj_pull : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ),
    toPre.obj (Fib.pull σ A) = Fib.pull (F.map σ) (toPre.obj A) := by intros; rfl
  /-- The chosen cartesian lifts are preserved. -/
  map_clift : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ),
    toPre.map (Fib.clift σ A) ≍ Fib.clift (F.map σ) (toPre.obj A) := by intros; rfl

attribute [rewrite_rule] StrictComprehensionMap.compr_map

variable {F D E}

/-- The isomorphism `F.obj (Γ ▹ A) ≅ F.obj Γ ▹ obj A` of a pseudo map. -/
@[simps]
def PseudoComprehensionMap.cmpIso (M : PseudoComprehensionMap F D E) {Γ : C} (A : D.Ty Γ) :
    F.obj (Γ ▹ A) ≅ F.obj Γ ▹ M.obj A where
  hom := M.cmp A
  inv := M.cmpInv A
  hom_inv_id := M.cmp_cmpInv A
  inv_hom_id := M.cmpInv_cmp A

/-- **A strict map is pseudo**, with identity comparisons: by the rule `compr_obj`,
`F.obj Γ ▹ obj A` is `F.obj (Γ ▹ A)`, and by the rule `compr_map`, naturality is `rfl`. -/
def StrictComprehensionMap.toPseudo (M : StrictComprehensionMap F D E) :
    PseudoComprehensionMap F D E where
  toDispFunctor := M.toPre.toDispFunctor
  isCartesianMap := M.toPre.isCartesianMap
  cmp _ := 𝟙 _
  cmp_proj _ := rfl
  cmp_natural _ := rfl
  cmpInv _ := 𝟙 _

/-! ## Identities and composites -/

section Comp

variable {G : C' ⥤ C''} {E' : Displayed.{v₆, u₆} C''} [Fib E'] [Comprehension E']

variable (D) in
/-- The identity map of comprehension categories. -/
def ComprehensionMap.id : ComprehensionMap (𝟭 C) D D where
  toDispFunctor := DispFunctor.id D
  isCartesianMap H := H
  cmp _ := 𝟙 _
  cmp_proj _ := rfl
  cmp_natural _ := rfl

/-- The composite of maps of comprehension categories: the comparison of `G ∘ F` at `A` is the
image under `G` of the comparison of `F`, followed by the comparison of `G` at its image. -/
def ComprehensionMap.comp (M : ComprehensionMap F D E) (N : ComprehensionMap G E E') :
    ComprehensionMap (F ⋙ G) D E' where
  toDispFunctor := M.toDispFunctor.comp N.toDispFunctor
  isCartesianMap H := N.isCartesianMap (M.isCartesianMap H)
  cmp A := G.map (M.cmp A) ≫ N.cmp (M.obj A)
  cmp_proj A :=
    (congrArg (G.map (M.cmp A) ≫ ·) (N.cmp_proj (M.obj A))).trans (congrArg G.map (M.cmp_proj A))
  cmp_natural {_ _ _ A B} φ :=
    (congrArg (fun t => G.map t ≫ N.cmp (M.obj B)) (M.cmp_natural φ)).trans
      (congrArg (G.map (M.cmp A) ≫ ·) (N.cmp_natural (M.map φ)))

variable (D) in
/-- The identity pseudo map. -/
def PseudoComprehensionMap.id : PseudoComprehensionMap (𝟭 C) D D where
  toComprehensionMap := ComprehensionMap.id D
  cmpInv _ := 𝟙 _

/-- The composite of pseudo maps, whose inverse comparisons compose in the opposite order. -/
def PseudoComprehensionMap.comp (M : PseudoComprehensionMap F D E)
    (N : PseudoComprehensionMap G E E') : PseudoComprehensionMap (F ⋙ G) D E' where
  toComprehensionMap := M.toComprehensionMap.comp N.toComprehensionMap
  cmpInv A := N.cmpInv (M.obj A) ≫ G.map (M.cmpInv A)
  cmp_cmpInv A :=
    (congrArg (fun t => G.map (M.cmp A) ≫ t ≫ G.map (M.cmpInv A)) (N.cmp_cmpInv (M.obj A))).trans
      (congrArg G.map (M.cmp_cmpInv A))
  cmpInv_cmp A :=
    (congrArg (fun t => N.cmpInv (M.obj A) ≫ G.map t ≫ N.cmp (M.obj A)) (M.cmpInv_cmp A)).trans
      (N.cmpInv_cmp (M.obj A))

variable (D) in
/-- The identity strict map. -/
def StrictComprehensionMap.id : StrictComprehensionMap (𝟭 C) D D where
  toPre.toDispFunctor := DispFunctor.id D
  toPre.isCartesianMap H := H
  toPre.compr_obj _ := rfl

/-- A displayed functor respects heterogeneous equality of morphisms with equal domains. -/
theorem DispFunctor.map_heq_of_dom (H : DispFunctor G E E') {a a' : C'} {f : a ⟶ a'}
    {x x' : E.Ob a} {y : E.Ob a'} (hx : x = x') {φ : x ⟶[f] y} {φ' : x' ⟶[f] y} (h : φ ≍ φ') :
    H.map φ ≍ H.map φ' := by
  subst hx
  cases h
  rfl

/-- The composite of strict maps. The axioms on the comprehension functors hold by `rfl` through
the rules for `M` and `N`. -/
def StrictComprehensionMap.comp (M : StrictComprehensionMap F D E)
    (N : StrictComprehensionMap G E E') : StrictComprehensionMap (F ⋙ G) D E' where
  toPre.toDispFunctor := M.toPre.toDispFunctor.comp N.toPre.toDispFunctor
  toPre.isCartesianMap H := N.toPre.isCartesianMap (M.toPre.isCartesianMap H)
  toPre.compr_obj _ := rfl
  obj_pull σ A := (congrArg N.toPre.obj (M.obj_pull σ A)).trans (N.obj_pull (F.map σ) _)
  map_clift σ A :=
    (DispFunctor.map_heq_of_dom N.toPre.toDispFunctor (M.obj_pull σ A) (M.map_clift σ A)).trans
      (N.map_clift (F.map σ) _)

end Comp

/-! ## Terms -/

section Tm

/-- **A strict map sends terms to terms** (Lift-Intro): `F.map t.sec` is a section of
`F.map (𝐩 A)`, which is `𝐩 (obj A)` by the rule `compr_obj`. -/
def StrictComprehensionMap.mapTm (M : StrictComprehensionMap F D E) {Γ : C} {A : D.Ty Γ}
    (t : Tm(Γ, A)) : Tm(F.obj Γ, M.toPre.obj A) where
  sec := F.map t.sec
  sec_proj := (F.map_comp _ _).symm.trans ((congrArg F.map t.sec_proj).trans (F.map_id _))

/-- **Over the identity, the terms of `A` are those of `obj A`** (Lift-Intro and Lift-Elim): they
have the same sections, since `Γ ▹ obj A` is `Γ ▹ A` with the same projection. -/
def StrictComprehensionMap.tmEquiv {D : Displayed.{v₃, u₃} C} [Fib D] [Comprehension D]
    {E : Displayed.{v₄, u₄} C} [Fib E] [Comprehension E] (M : StrictComprehensionMap (𝟭 C) D E)
    {Γ : C} {A : D.Ty Γ} : Tm(Γ, A) ≃ Tm(Γ, M.toPre.obj A) where
  toFun := M.mapTm
  invFun s := ⟨s.sec, s.sec_proj⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comprehension functor respects heterogeneous equality of morphisms with equal domains. -/
theorem extMap_heq {E : Displayed.{v₄, u₄} C'} [Fib E] [Comprehension E] {a a' : C'} {f : a ⟶ a'}
    {x x' : E.Ob a} {y : E.Ob a'} (hx : x = x') {φ : x ⟶[f] y} {φ' : x' ⟶[f] y} (h : φ ≍ φ') :
    E.extMap φ ≍ E.extMap φ' := by
  subst hx
  cases h
  rfl

/-- **A strict map preserves the morphisms `𝐪`**: `𝐪(F.map σ, obj A)` is `F.map 𝐪(σ, A)`, since it
preserves the chosen lifts and commutes with the comprehension functors. -/
theorem StrictComprehensionMap.q_obj (M : StrictComprehensionMap F D E) {Δ Γ : C} (σ : Δ ⟶ Γ)
    (A : D.Ty Γ) : 𝐪(F.map σ, M.toPre.obj A) ≍ F.map 𝐪(σ, A) :=
  (extMap_heq (M.obj_pull σ A).symm (M.map_clift σ A).symm).trans
    (heq_of_eq (congrArg (fun ψ => ψ.1) (M.compr_map (Fib.clift σ A))))

/-- A section of a type equal to `B⦃σ⦄`, over a term `t` along a morphism equal to `𝐪(σ, B)`, is
`t⦃σ⦄`. -/
theorem Tm.heq_pull_of_sec_comp {E : Displayed.{v₄, u₄} C} [Fib E] [Comprehension E] {Δ Γ : C}
    (σ : Δ ⟶ Γ) {B : E.Ty Γ} (t : Tm(Γ, B)) {B' : E.Ty Δ} (hB : B' = B⦃σ⦄) (s : Tm(Δ, B'))
    (q' : Δ ▹ B' ⟶ Γ ▹ B) (hq : q' ≍ 𝐪(σ, B)) (h : s.sec ≫ q' = σ ≫ t.sec) : s ≍ t⦃σ⦄ := by
  subst hB
  cases hq
  exact heq_of_eq (Tm.pull_unique σ t s h)

/-- **Over the identity, a strict map commutes with the substitution of terms**: it preserves the
morphisms `𝐪`, so the image of `t⦃σ⦄` is the section over the image of `t` along `𝐪(σ, obj A)`.
The two terms are of the types `obj A⦃σ⦄` and `(obj A)⦃σ⦄`, equal by `obj_pull`. -/
theorem StrictComprehensionMap.tmEquiv_pull {D : Displayed.{v₃, u₃} C} [Fib D] [Comprehension D]
    {E : Displayed.{v₄, u₄} C} [Fib E] [Comprehension E] (M : StrictComprehensionMap (𝟭 C) D E)
    {Δ Γ : C} (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Γ, A)) :
    M.tmEquiv (t⦃σ⦄) ≍ (M.tmEquiv t)⦃σ⦄ :=
  Tm.heq_pull_of_sec_comp σ (M.tmEquiv t) (M.obj_pull σ A) (M.tmEquiv (t⦃σ⦄)) 𝐪(σ, A)
    (M.q_obj σ A).symm (Tm.pull_sec_q σ t)

end Tm

end Displayed
