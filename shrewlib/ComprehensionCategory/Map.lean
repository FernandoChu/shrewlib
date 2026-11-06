import ComprehensionCategory.Basic

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
  `F.obj Γ ▹ obj A` and `F.map (𝐩 A)` is `𝐩 (obj A)`, and on morphisms (`compr_map`).

Both equations of a strict map are rewrite rules. The equation on objects makes the one on
morphisms well-typed as a plain equation, and with both, a strict map is pseudo with identity
comparisons (`StrictComprehensionMap.toPseudo`), whose laws hold by `rfl`.

All three kinds have identities and compose, over the identity and composite functors; for strict
maps, the axioms of the identity and the composite hold by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {C'' : Type u₅} [Category.{v₅} C'']

/-! ## Maps -/

variable (F : C ⥤ C') (D : Displayed.{v₁, u₁, v₃, u₃} C) [Fib D] [Comprehension D]
  (E : Displayed.{v₂, u₂, v₄, u₄} C') [Fib E] [Comprehension E]

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
functors commute on morphisms too. As for `SplitFib`, the pre-strict map is a field rather than a
parent, so that the rule `compr_obj` applies to the axiom on morphisms, which is a rule too. -/
structure StrictComprehensionMap where
  /-- The underlying pre-strict map. -/
  toPre : PreStrictComprehensionMap F D E
  /-- The comprehension functors commute on morphisms. -/
  compr_map : ∀ {Γ Γ' : C} {f : Γ ⟶ Γ'} {A : D.Ty Γ} {B : D.Ty Γ'} (φ : A ⟶[f] B),
    E.compr.map (toPre.map φ) = (codMap F).map (D.compr.map φ) := by intros; rfl

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

variable {G : C' ⥤ C''} {E' : Displayed.{v₅, u₅, v₆, u₆} C''} [Fib E'] [Comprehension E']

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

/-- The composite of strict maps, whose axioms hold by `rfl` through the rules for `M` and `N`. -/
def StrictComprehensionMap.comp (M : StrictComprehensionMap F D E)
    (N : StrictComprehensionMap G E E') : StrictComprehensionMap (F ⋙ G) D E' where
  toPre.toDispFunctor := M.toPre.toDispFunctor.comp N.toPre.toDispFunctor
  toPre.isCartesianMap H := N.toPre.isCartesianMap (M.toPre.isCartesianMap H)
  toPre.compr_obj _ := rfl

end Comp

end Displayed
