import ComprehensionCategory.Model.OverCat.Shared.Pi
import ComprehensionCategory.Model.OverCat.Shared.HomDisc
import ComprehensionCategory.Model.OverCat.Shared.Universe
import ComprehensionCategory.Model.OverCat.Discrete.Small

/-!
# Directed univalence

The paper's Proposition `dunivalence`: for a contravariant type `A` and a discrete type `B`, the
terms of the Hom-type of the universe at their codes are those of the function type:

```
  Tm_s(Γ, Hom_U(A, B)) ≅ Tm(Γ, A → B)
```

naturally in `Γ`. As decided for the formalization, it is not an equality of types: at `γ`, the
values of `A → B` are the sections of the constant family `B γ` over `A γ`, while those of
`Hom_U(A, B)` are the `ULift`ed functors `A γ ⥤ B γ`, so the two functors `Γ ⥤ Cat` are only
isomorphic. It is a strict natural isomorphism (`dunivIso`), stable under substitution
(`dunivIso_pull`), and it gives the bijection of terms (`dunivTmEquiv`), natural in `Γ`
(`dunivTmEquiv_pull`).

## The function type into a discrete type

For a contravariant type `A` (of `ICatOpLax`) and a discrete type `B` (of `IDisc`), the function
type `A → B` is the Π-type `Π[A] B⦃𝐩 A⦄` of the category model (`Shared/Pi`), with `B` seen in the
category model and weakened (`funCodDisc`). Its value at `γ` is the category of sections of the
constant family `B γ` over `A γ`. It is discrete (`isDiscrete_piFib`): a morphism of sections has
components in the discrete category `B γ`, so the sections agree on objects, and on morphisms,
which are unique. So `A → B` is a type of the discrete model (`funDisc`), whose functor is the
Π-type, by `rfl`.

## Terms along isomorphisms of discrete types

A natural transformation `e : X ⟶ Y` between discrete types sends the sections of `∫ X` to those of
`∫ Y` (`mapSection`): the value at `γ` is `e γ` of that of the section, and the morphisms, between
objects of the discrete categories `Y γ'` that the naturality of `e` makes equal, are `eqToHom`s.
A natural isomorphism gives inverse maps (`mapSectionEquiv`), so a bijection of the terms
(`tmEquivOfIso`), natural in `Γ` along the restriction of `e` (`tmEquivOfIso_pull`).

## Directed univalence

For `A : Γᵒᵖ ⥤ Cat.{v, v}` and a discrete `B : IDiscOb.{v, v} Γ` of level `v`, over a context
`Γ : Cat.{v + 1, v + 1}`:

* `Hom_U(A, B)` is the Hom-type of the universe `U Γ` at the codes `codeOp A` of `A`, a term of
  `Uᵒᵖ`, and `code B` (`homU`). At `γ`, it is the discrete category on the morphisms
  `A γ ⟶ B γ` of `smallCat`, the `ULift`ed functors, and along `g`, it sends `h` to
  `A g ≫ h ≫ B g` (`homU_map_obj`), by `rfl`.
* `A → B` is `funDisc` of the lifts of `A` and `B` to level `v + 1` (`funU`).

At `γ`, a section `s` of the constant family `B γ` over `A γ` is a functor `A γ ⥤ B γ`
(`secToFun`), and conversely (`funToSec`). These give an isomorphism of categories, since both are
discrete (`dunivIsoApp`). It is natural: the transport `pushObj g s` of a section is
`x ↦ B g (s (A g x))`, which is the action `A g ≫ h ≫ B g` of `Hom_U(A, B)` (`secToFun_push`).
Both types are stable under substitution by `rfl`, in the kernel (`funU_pull`, `homU_pull`), and
so is the isomorphism, up to these equalities (`dunivIso_pull`): its restriction along `σ` is the
isomorphism for `σ ⋙ A` and `σ ⋙ B`.

The twisted form, `Tm_d(Γ, Hom_U(Ā, B)) ≅ Tm_d(Γ, Ā → B)`, is in `Applications/NatPi`.
-/

universe u v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

/-! ## The function type into a discrete type -/

section Disc

variable {Γ : Cat.{u, u}} (A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ)
  (B : IDisc.{u, u}.Ty Γ)

/-- The codomain of the function type: the discrete type `B`, seen in the category model and
weakened to `Γ ▹ A`. -/
abbrev funCodDisc : ICatLax.{u, u}.Ty (Γ ▹ A) :=
  (forgetComprehensionMap.toPre.obj B)⦃𝐩 A⦄

/-- Morphisms of a discrete category between equal objects are heterogeneously equal. -/
theorem hom_heq_of_isDiscrete {C : Type u} [Category.{u} C] [IsDiscrete C] {x x' y y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y') : f ≍ g := by
  subst hx hy
  exact heq_of_eq (Subsingleton.elim f g)

/-- **The function type into a discrete type is discrete**: a morphism of sections has components
in the discrete category `B γ`, so the sections agree, and morphisms are unique. -/
theorem isDiscrete_piFib (γ : Γ) :
    IsDiscrete ((Π[A] (funCodDisc A B) : ICatLax.Ty Γ).obj γ) where
  subsingleton _ _ := ⟨fun α β => Section.Hom.ext fun x =>
    @Subsingleton.elim _ ((B.isDiscrete γ).subsingleton _ _) (α.app x) (β.app x)⟩
  eq_of_hom {s t} α := by
    have hobj : ∀ x, s.obj x = t.obj x := fun x =>
      @IsDiscrete.eq_of_hom (B.toFunctor.obj γ) _ (B.isDiscrete γ) _ _ (α.app x)
    exact Section.ext hobj fun {x y} φ =>
      @hom_heq_of_isDiscrete (B.toFunctor.obj γ) _ (B.isDiscrete γ) _ _ _ _ (hobj x) (hobj y)
        (s.map φ) (t.map φ)

/-- **The function type `A → B`** into a discrete type, a type of the discrete model: the Π-type of
`B` weakened. -/
def funDisc : IDisc.{u, u}.Ty Γ where
  toFunctor := Π[A] (funCodDisc A B)
  isDiscrete := isDiscrete_piFib A B

/-- The functor of `A → B` is the Π-type, by `rfl`. -/
theorem funDisc_toFunctor : (funDisc A B).toFunctor = Π[A] (funCodDisc A B) :=
  rfl

end Disc

/-! ## Terms along isomorphisms of discrete types -/

section TmIso

variable {Γ : Cat.{u, u}} {X Y : IDisc.{u, u}.Ty Γ}

/-- The values along `k` of the image of a section `S` along `e` are equal: by the naturality of `e`
and since `S k` is a morphism of a discrete category. -/
theorem mapSection_eq (e : X.toFunctor ⟶ Y.toFunctor) (S : (∫ X.toFunctor).Section) {γ γ' : Γ}
    (k : γ ⟶ γ') :
    (Y.toFunctor.map k).toFunctor.obj ((e.app γ).toFunctor.obj (S.obj γ)) =
      (e.app γ').toFunctor.obj (S.obj γ') :=
  (Functor.congr_obj (congrArg Cat.Hom.toFunctor (e.naturality k)) (S.obj γ)).symm.trans
    (congrArg (e.app γ').toFunctor.obj ((X.isDiscrete γ').eq_of_hom (S.map k)))

/-- The morphism along `k` of the image of a section along `e`, an `eqToHom`. It is stated for a
variable `k`, so that the kernel checks its type once. -/
def mapSectionMap (e : X.toFunctor ⟶ Y.toFunctor) (S : (∫ X.toFunctor).Section) {γ γ' : Γ}
    (k : γ ⟶ γ') :
    (∫ Y.toFunctor).Hom k ((e.app γ).toFunctor.obj (S.obj γ))
      ((e.app γ').toFunctor.obj (S.obj γ')) :=
  eqToHom (mapSection_eq e S k)

/-- **The image of a section of `∫ X` along a natural transformation `e : X ⟶ Y`** of discrete
types: its values are those of `e` at the values of `S`, and its morphisms are unique. -/
def mapSection (e : X.toFunctor ⟶ Y.toFunctor) (S : (∫ X.toFunctor).Section) :
    (∫ Y.toFunctor).Section where
  obj γ := (e.app γ).toFunctor.obj (S.obj γ)
  map k := mapSectionMap e S k
  map_id γ := @Subsingleton.elim _ ((Y.isDiscrete γ).subsingleton _ _) _ _
  map_comp _ _ := @Subsingleton.elim _ ((Y.isDiscrete _).subsingleton _ _) _ _

/-- `mapSection` preserves composites. -/
theorem mapSection_mapSection {Z : IDisc.{u, u}.Ty Γ} (e : X.toFunctor ⟶ Y.toFunctor)
    (e' : Y.toFunctor ⟶ Z.toFunctor) (S : (∫ X.toFunctor).Section) :
    mapSection e' (mapSection e S) = mapSection (e ≫ e') S :=
  Section.ext (fun _ => rfl) fun _ =>
    @hom_heq_of_isDiscrete _ _ (Z.isDiscrete _) _ _ _ _ rfl rfl _ _

/-- `mapSection` preserves identities. -/
theorem mapSection_id (S : (∫ X.toFunctor).Section) : mapSection (𝟙 X.toFunctor) S = S :=
  Section.ext (fun _ => rfl) fun _ =>
    @hom_heq_of_isDiscrete _ _ (X.isDiscrete _) _ _ _ _ rfl rfl _ _

/-- The sections of `∫ X` and of `∫ Y`, for a natural isomorphism `e : X ≅ Y` of discrete types. -/
def mapSectionEquiv (e : X.toFunctor ≅ Y.toFunctor) :
    (∫ X.toFunctor).Section ≃ (∫ Y.toFunctor).Section where
  toFun := mapSection e.hom
  invFun := mapSection e.inv
  left_inv S := (mapSection_mapSection _ _ S).trans
    ((congrArg (mapSection · S) e.hom_inv_id).trans (mapSection_id S))
  right_inv S := (mapSection_mapSection _ _ S).trans
    ((congrArg (mapSection · S) e.inv_hom_id).trans (mapSection_id S))

/-- **The terms of isomorphic discrete types**: the terms are the sections, in the category model,
and the sections correspond along the isomorphism. -/
def tmEquivOfIso (e : X.toFunctor ≅ Y.toFunctor) : Tm(Γ, X) ≃ Tm(Γ, Y) :=
  forgetComprehensionMap.tmEquiv.trans (CatModel.Tm.sectionEquiv.trans
    ((mapSectionEquiv e).trans (CatModel.Tm.sectionEquiv.symm.trans
      forgetComprehensionMap.tmEquiv.symm)))

/-- Heterogeneously equal isomorphisms between equal discrete types give heterogeneously equal
bijections. -/
theorem tmEquivOfIso_hcongr {X' Y' : IDisc.{u, u}.Ty Γ} (hX : X = X') (hY : Y = Y')
    {e : X.toFunctor ≅ Y.toFunctor} {e' : X'.toFunctor ≅ Y'.toFunctor} (he : e ≍ e')
    {t : Tm(Γ, X)} {t' : Tm(Γ, X')} (ht : t ≍ t') : tmEquivOfIso e t ≍ tmEquivOfIso e' t' := by
  subst hX hY
  cases he
  cases ht
  rfl

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)

/-- The image of a reindexed section along the restricted transformation is the reindexing of the
image. -/
theorem mapSection_pull (e : X.toFunctor ⟶ Y.toFunctor) (S : (∫ X.toFunctor).Section) :
    mapSection (X := X⦃σ⦄) (Y := Y⦃σ⦄) (Functor.whiskerLeft σ.toFunctor e) (S.pull σ) =
      (mapSection e S).pull σ :=
  Section.ext (fun _ => rfl) fun _ =>
    @hom_heq_of_isDiscrete _ _ (Y.isDiscrete _) _ _ _ _ rfl rfl _ _

/-- **The bijection is natural in `Γ`**: substituted along `σ`, the term corresponding to `t` is the
one corresponding to `t⦃σ⦄` along the restriction of `e`. -/
theorem tmEquivOfIso_pull (e : X.toFunctor ≅ Y.toFunctor) (t : Tm(Γ, X)) :
    tmEquivOfIso (X := X⦃σ⦄) (Y := Y⦃σ⦄) (Functor.isoWhiskerLeft σ.toFunctor e) t⦃σ⦄ =
      (tmEquivOfIso e t)⦃σ⦄ := by
  apply forgetComprehensionMap.tmEquiv.injective
  refine Eq.trans ?_ (forgetComprehensionMap_tmEquiv_pull σ _).symm
  refine Eq.trans ?_ (CatModel.Tm.ofSection_pull σ _).symm
  change CatModel.Tm.ofSection (mapSection (X := X⦃σ⦄) (Y := Y⦃σ⦄)
      (Functor.whiskerLeft σ.toFunctor e.hom)
      (CatModel.Tm.toSection (forgetComprehensionMap.tmEquiv t⦃σ⦄))) = _
  exact (congrArg (fun S => CatModel.Tm.ofSection (mapSection (X := X⦃σ⦄) (Y := Y⦃σ⦄)
      (Functor.whiskerLeft σ.toFunctor e.hom) S))
      ((congrArg CatModel.Tm.toSection (forgetComprehensionMap_tmEquiv_pull σ t)).trans
        (CatModel.Tm.toSection_pull σ _))).trans
    (congrArg CatModel.Tm.ofSection (mapSection_pull σ e.hom _))

end TmIso

/-! ## Directed univalence -/

section Small

variable {Γ : Cat.{v + 1, v + 1}} (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}) (B : IDiscOb.{v, v} Γ)

/-- **`Hom_U(A, B)`**, the Hom-type of the universe at the codes of a contravariant type `A`, a term
of `Uᵒᵖ`, and of a discrete type `B`, of level `v`. A discrete type. -/
def homU : IDisc.{v + 1, v + 1}.Ty Γ :=
  homAt (A := U Γ) (codeOp A) (code B.toFunctor)

/-- At `γ`, `Hom_U(A, B)` is the discrete category on the morphisms `A γ ⟶ B γ` of `smallCat`, the
`ULift`ed functors, by `rfl`. -/
theorem homU_obj (γ : Γ) :
    (homU A B).toFunctor.obj γ =
      discrete' (ULift.{v + 1} (A.obj (Opposite.op γ) ⟶ B.toFunctor.obj γ)) :=
  rfl

/-- **`Hom_U(A, B)` is stable under substitution**, by `rfl` in the kernel. -/
theorem homU_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (homU A B)⦃σ⦄ = homU (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) := by
  kernel_rfl'

/-- **The function type `A → B`**, for `A` contravariant and `B` discrete of level `v`: the
discrete type `funDisc` of their lifts to level `v + 1`. -/
abbrev funU : IDisc.{v + 1, v + 1}.Ty Γ :=
  funDisc (CatOpModel.lift A) (liftDisc B)

/-- **`A → B` is stable under substitution**, by `rfl` in the kernel. -/
theorem funU_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (funU A B)⦃σ⦄ = funU (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) := by
  kernel_rfl'

variable {A B}

/-- The functor `A γ ⥤ B γ` of a section of the constant family `B γ` over `A γ`. -/
def secToFun {γ : Γ} (s : (funU A B).toFunctor.obj γ) :
    A.obj (Opposite.op γ) ⥤ B.toFunctor.obj γ where
  obj x := ULift.down (s.obj (ULift.up.{v + 1} x))
  map f := ULift.down (s.map (ULift.up.{v + 1} f))
  map_id x := congrArg ULift.down (s.map_id (ULift.up.{v + 1} x))
  map_comp f g := congrArg ULift.down (s.map_comp (ULift.up.{v + 1} f) (ULift.up.{v + 1} g))

/-- The section of the constant family `B γ` over `A γ` of a functor `A γ ⥤ B γ`. -/
def funToSec {γ : Γ} (F : A.obj (Opposite.op γ) ⥤ B.toFunctor.obj γ) :
    (funU A B).toFunctor.obj γ where
  obj x := ULift.up.{v + 1} (F.obj (ULift.down x))
  map f := ULift.up.{v + 1} (F.map (ULift.down f))

/-- A section is the section of its functor. -/
theorem funToSec_secToFun {γ : Γ} (s : (funU A B).toFunctor.obj γ) : funToSec (secToFun s) = s :=
  Section.ext (fun _ => rfl) fun _ => HEq.rfl

/-- A functor is the functor of its section, by `rfl`. -/
theorem secToFun_funToSec {γ : Γ} (F : A.obj (Opposite.op γ) ⥤ B.toFunctor.obj γ) :
    secToFun (funToSec (A := A) (B := B) F) = F :=
  rfl

/-- The functor of the transport of a section along `g` is `A g ⋙ s ⋙ B g`. -/
theorem secToFun_push {γ γ' : Γ} (g : γ ⟶ γ') (s : (funU A B).toFunctor.obj γ) :
    (secToFun (((funU A B).toFunctor.map g).toFunctor.obj s)).toCatHom =
      A.map g.op ≫ (secToFun s).toCatHom ≫ B.toFunctor.map g :=
  Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

/-- `Hom_U(A, B)` acts along `g` by `h ↦ A g ≫ h ≫ B g`, by `rfl`. -/
theorem homU_map_obj {γ γ' : Γ} (g : γ ⟶ γ') (h : (homU A B).toFunctor.obj γ) :
    ((homU A B).toFunctor.map g).toFunctor.obj h =
      (ULift.up.{v + 1} (A.map g.op ≫
        (ULift.down h : A.obj (Opposite.op γ) ⟶ B.toFunctor.obj γ) ≫ B.toFunctor.map g) :
        ULift.{v + 1} (A.obj (Opposite.op γ') ⟶ B.toFunctor.obj γ')) := by
  kernel_rfl'

variable (A B) in
/-- The functor from the values of `A → B` to those of `Hom_U(A, B)` at `γ`: a section goes to its
functor, and morphisms, which are unique, to equalities. -/
def dunivHom (γ : Γ) : (funU A B).toFunctor.obj γ ⟶ (homU A B).toFunctor.obj γ :=
  (show (funU A B).toFunctor.obj γ ⥤
      discrete' (ULift.{v + 1} (A.obj (Opposite.op γ) ⟶ B.toFunctor.obj γ)) from
    { obj s := ULift.up.{v + 1} (secToFun s).toCatHom
      map {_ _} α := ⟨⟨congrArg (fun s => ULift.up.{v + 1} (secToFun s).toCatHom)
        (((funU A B).isDiscrete γ).eq_of_hom α)⟩⟩
      map_id _ := discrete'_hom_ext _ _
      map_comp _ _ := discrete'_hom_ext _ _ }).toCatHom

variable (A B) in
/-- The functor from the values of `Hom_U(A, B)` to those of `A → B` at `γ`: a functor goes to its
section. -/
def dunivInv (γ : Γ) : (homU A B).toFunctor.obj γ ⟶ (funU A B).toFunctor.obj γ :=
  (show discrete' (ULift.{v + 1} (A.obj (Opposite.op γ) ⟶ B.toFunctor.obj γ)) ⥤
      (funU A B).toFunctor.obj γ from
    { obj e := funToSec (ULift.down e).toFunctor
      map {_ _} h := eqToHom (congrArg (fun e => funToSec (ULift.down e).toFunctor) h.down.down)
      map_id _ := @Subsingleton.elim _ (((funU A B).isDiscrete γ).subsingleton _ _) _ _
      map_comp _ _ :=
        @Subsingleton.elim _ (((funU A B).isDiscrete γ).subsingleton _ _) _ _ }).toCatHom

variable (A B) in
/-- The values of `A → B` and of `Hom_U(A, B)` at `γ` are isomorphic. -/
def dunivIsoApp (γ : Γ) : (funU A B).toFunctor.obj γ ≅ (homU A B).toFunctor.obj γ where
  hom := dunivHom A B γ
  inv := dunivInv A B γ
  hom_inv_id := Cat.Hom.ext (Functor.hext funToSec_secToFun fun _ _ _ =>
    @hom_heq_of_isDiscrete _ _ ((funU A B).isDiscrete γ) _ _ _ _ (funToSec_secToFun _)
      (funToSec_secToFun _) _ _)
  inv_hom_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ =>
    @hom_heq_of_isDiscrete _ _ ((homU A B).isDiscrete γ) _ _ _ _ rfl rfl _ _)

/-- The isomorphisms are natural: the transport of a section along `g` is `A g ⋙ s ⋙ B g`, the
action of `Hom_U(A, B)`. -/
theorem dunivHom_naturality {γ γ' : Γ} (g : γ ⟶ γ') :
    (funU A B).toFunctor.map g ≫ (dunivIsoApp A B γ').hom =
      (dunivIsoApp A B γ).hom ≫ (homU A B).toFunctor.map g := by
  have hobj : ∀ s, ((funU A B).toFunctor.map g ≫ (dunivIsoApp A B γ').hom).toFunctor.obj s =
      ((dunivIsoApp A B γ).hom ≫ (homU A B).toFunctor.map g).toFunctor.obj s := fun s => by
    have h₁ : ((funU A B).toFunctor.map g ≫ (dunivIsoApp A B γ').hom).toFunctor.obj s =
        ULift.up.{v + 1} (secToFun (((funU A B).toFunctor.map g).toFunctor.obj s)).toCatHom := by
      kernel_rfl'
    have h₂ : ((dunivIsoApp A B γ).hom ≫ (homU A B).toFunctor.map g).toFunctor.obj s =
        ULift.up.{v + 1} (A.map g.op ≫ (secToFun s).toCatHom ≫ B.toFunctor.map g) := by
      kernel_rfl'
    exact h₁.trans ((congrArg (ULift.up.{v + 1}) (secToFun_push g s)).trans h₂.symm)
  exact Cat.Hom.ext (Functor.hext hobj fun _ _ _ =>
    @hom_heq_of_isDiscrete _ _ ((homU A B).isDiscrete γ') _ _ _ _ (hobj _) (hobj _) _ _)

variable (A B) in
/-- **Directed univalence**: the function type `A → B` and the Hom-type `Hom_U(A, B)` of the
universe are isomorphic, by a strict natural isomorphism of functors `Γ ⥤ Cat`. -/
def dunivIso : (funU A B).toFunctor ≅ (homU A B).toFunctor :=
  NatIso.ofComponents (dunivIsoApp A B) dunivHom_naturality

/-- **Directed univalence is stable under substitution**: restricted along `σ`, the isomorphism is
that of `σ ⋙ A` and `σ ⋙ B`, up to the equalities `funU_pull` and `homU_pull` of its functors. -/
theorem dunivIso_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft σ.toFunctor (dunivIso A B) ≍
      dunivIso (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) := by
  kernel_rfl'

variable (A B) in
/-- **Directed univalence for terms** (paper, `dunivalence`): the terms of `A → B` are those of
`Hom_U(A, B)`. Through `forgetComprehensionMap.tmEquiv`, the former are the terms of the Π-type of
the category model. -/
def dunivTmEquiv : Tm(Γ, funU A B) ≃ Tm(Γ, homU A B) :=
  tmEquivOfIso (dunivIso A B)

/-- **The bijection is natural in `Γ`**, up to the equalities `funU_pull` and `homU_pull`. -/
theorem dunivTmEquiv_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) (t : Tm(Γ, funU A B)) :
    (dunivTmEquiv A B t)⦃σ⦄.castTy (homU_pull A B σ) =
      dunivTmEquiv (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) (t⦃σ⦄.castTy (funU_pull A B σ)) :=
  eq_of_heq ((Tm.castTy_heq _ _).trans
    ((heq_of_eq (tmEquivOfIso_pull σ (dunivIso A B) t)).symm.trans
      (tmEquivOfIso_hcongr (funU_pull A B σ) (homU_pull A B σ) (dunivIso_pull σ)
        (Tm.castTy_heq _ _).symm)))

end Small

end ComprehensionCategory.OverCat
