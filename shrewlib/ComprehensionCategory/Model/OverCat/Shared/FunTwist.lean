import ComprehensionCategory.Model.OverCat.Shared.Pi
import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Shared.Universe
import ComprehensionCategory.Model.OverCat.Displayed.Term
import Tactic.KernelTactic

/-!
# Twisted function types

As in the paper, consider the function type over two type variables, the second contravariant, in
the category model at level `v + 1`:

```
  Γ ▹ X : U ▹ Y : Uᵒᵖ ⊢ Y → X type
```

the Π-type `Π[Y] X⦃𝐩 Y⦄` of the category model over the contravariant one (`Shared/Pi`), with `Y`
decoded as a contravariant type (`ElOp`) and `X` as a type (`El`), both lifted to level `v + 1`
(`funTy`). Its last variable has the type `Uᵒᵖ`, the opposite of `U`, so it can be twisted:

```
  Γ ▹ X : U ▹ Y : U ⊢ Ȳ → X type_d                              (funTwistGen)
```

a type of the displayed model, now covariant in `Y`. Substituting the codes of two types `A` and
`B` of level `v` gives `Γ ⊢ Ā → B type_d` (`funTwist A B`). **Its terms are those of `B` in context
`Γ ▹ a : A`** (`funTwistEquiv`), by application, whose inverse is abstraction:

```
  app : Tm_d(Γ, Ā → B) ≃ Tm(Γ ▹ a : A, B) : λ
```

As for the Π-types, a term of `Ā → B` is a section of its displayed category `funDisp A B`
(`DisplayedModel.Tm.sectionEquiv`): over `γ`, a section `T γ` of `∫ B` over `A γ`, that is a functor
`A γ ⥤ B γ`, and over `g : γ ⟶ γ'`, a morphism of the twist, a vertical natural transformation from
`x ↦ B g (T γ x)` to `x ↦ T γ' (A g x)`. Its component at `x` is a morphism of `∫ B⦃𝐩 A⦄` over the
chosen opcartesian lift `(g, 𝟙) : (γ, x) ⟶ (γ', A g x)` of `∫ A` (`funAppOf`). So these sections are
those of `∫ B⦃𝐩 A⦄` over `Γ ▹ A` (`funSectionEquiv`), which are the terms of `B⦃𝐩 A⦄`
(`CatModel.Tm.sectionEquiv`): a section `S` of `∫ B⦃𝐩 A⦄` restricts to the fibres, with components
`S (g, 𝟙)` (`funSection`), and a section `T` of `funDisp A B` gives the section whose morphism over
`(g, φ) = (g, 𝟙) ≫ (𝟙, φ)` is the component along `g` followed by `T γ' φ` (`ofFunSection`).

The objects and morphisms of `funDisp A B` are those of the twist and of the Π-type by `rfl`, but
the elaborator is slow to unfold them. So they are accessed through definitions whose types are
stated in terms of `∫ B⦃𝐩 A⦄` (`funFib`, `funFibMap`, `funAppOf`), checked once, and the laws are
stated over explicit variables (`funMap_comp`) and checked in the kernel. The codomain `X⦃𝐩 Y⦄`
is the substitution of the type `El X`, rather than `El` of the substituted variable: substitution
of types is precomposition, by `rfl`, while that of terms is a pullback factorization.

**`Ā → B` and its bijection are stable under substitution** along `σ : Δ ⟶ Γ`:

```
  (Ā → B)⦃σ⦄ = (σ ⋙ A)‾ → σ ⋙ B                                  (funTwist_pull)
  app (t⦃σ⦄) = (app t)⦃𝐪(σ, A)⦄                                  (funTwistEquiv_pull)
```

The reindexing of `funDisp A B` along `σ` is `funDisp (σ ⋙ A) (σ ⋙ B)`, in the kernel
(`funDisp_pull`): `Ā → B` at `σ δ` only depends on `A (σ δ)` and `B (σ δ)`. The equality of the
straightened types follows through `funTwist_eq`, since comparing them directly in the kernel
unfolds the twist and does not finish. Abstraction `funLam` is the term of the section of `Ā → B`
of `t` (`funLam_heq`), and the section of `t⦃𝐪(σ, A)⦄` is the reindexing of that of `t`
(`funSection_pull`), as for `piLam_pull`, by `CatModel.Tm.toSection_pull_obj` and `_map`. So
abstraction is stable under substitution (`funLam_pull`), up to `funTwist_pull`, and so is its
inverse, application.
-/

universe v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

open scoped Displayed

variable (Γ : Cat.{v + 1, v + 1})

/-- The context `Γ ▹ X : U` of a type variable. -/
abbrev funCtx₀ : Cat.{v + 1, v + 1} := Γ ▹ U Γ

/-- The context `Γ ▹ X : U ▹ Y : Uᵒᵖ`. -/
abbrev funCtx : Cat.{v + 1, v + 1} := funCtx₀ Γ ▹ (U (funCtx₀ Γ))ᵒᵖ

/-- The domain `Y`, a contravariant type in context `Γ ▹ X : U ▹ Y : Uᵒᵖ`. -/
def funDom : Fibration.Straightening.ICatOpLax.{v + 1, v + 1}.Ty (funCtx Γ) :=
  CatOpModel.lift (ElOp (var (U (funCtx₀ Γ))ᵒᵖ))

/-- The codomain `X`, a type in context `Γ ▹ X : U ▹ Y : Uᵒᵖ`. -/
def funCod : ICatLax.{v + 1, v + 1}.Ty (funCtx Γ) :=
  (CatModel.lift (El (var (U Γ))))⦃𝐩 (U (funCtx₀ Γ))ᵒᵖ⦄

/-- The function type `Γ ▹ X : U ▹ Y : Uᵒᵖ ⊢ Y → X`. -/
def funTy : ICatLax.{v + 1, v + 1}.Ty (funCtx Γ) :=
  Π[funDom Γ] (funCod Γ)⦃𝐩 (funDom Γ)⦄

/-- Its twist `Γ ▹ X : U ▹ Y : U ⊢ Ȳ → X`. -/
def funTwistGen :
    Straightening.LaxNormalCat.{v + 1, v + 1, v + 1}.Ty (funCtx₀ Γ ▹ U (funCtx₀ Γ)) :=
  twist (B := U (funCtx₀ Γ)) (funTy Γ)

variable {Γ}

/-- `Ā → B`, for types `A` and `B` of level `v`. -/
def funTwist (A B : Γ ⥤ Cat.{v, v}) : Straightening.LaxNormalCat.{v + 1, v + 1, v + 1}.Ty Γ :=
  (funTwistGen Γ)⦃consSec (code B).sec (code A)⦄

variable (A B : Γ ⥤ Cat.{v, v})

/-- The substitution `Γ ⟶ Γ ▹ X : U ▹ Y : U` of the codes of `B` and `A`. -/
abbrev funSub : Γ ⟶ funCtx₀ Γ ▹ U (funCtx₀ Γ) := consSec (code B).sec (code A)

/-- The displayed category of `Ā → B`: that of the twist, reindexed along the codes. -/
abbrev funDisp : Displayed.{v + 1, v + 1} Γ :=
  DisplayedCat.pull (funSub A B) (twistDisp (B := U (funCtx₀ Γ)) (funTy Γ))

/-- `Ā → B` is the straightening of `funDisp A B`. -/
theorem funTwist_eq : funTwist A B = Straightening.straightenObj (funDisp A B) :=
  DisplayedModel.straightenObj_pull (funSub A B) (twistDisp (B := U (funCtx₀ Γ)) (funTy Γ))

/-- The unstraightening of `B⦃𝐩 A⦄`, whose sections are the terms of `B` in context `Γ ▹ A`. -/
abbrev funE : Displayed.{v + 1, v + 1} (Γ ▹ CatModel.lift A : Cat.{v + 1, v + 1}) :=
  ∫ ((CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄)

/-- The point `((γ, B γ), A γ)` of `Γ ▹ X : U ▹ Y : Uᵒᵖ`. -/
abbrev funPt (γ : Γ) : funCtx Γ :=
  (∫ (U (funCtx₀ Γ) ⋙ opFunctor')).tot (a := ((funSub A B).toFunctor.obj γ).1)
    ((funSub A B).toFunctor.obj γ).2

variable {A B}

/-- The value at `γ` of the section of `Ā → B` of a section of `∫ B⦃𝐩 A⦄`: its restriction to the
fibre `A γ`. -/
def funObj (S : (funE A B).Section) (γ : Γ) :
    PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ) where
  obj x := S.obj ⟨γ, x⟩
  map φ := S.map ((∫ (CatModel.lift A)).totalMk (𝟙 γ) φ)
  map_id x := S.map_id _
  map_comp φ ψ := by
    kernel_exact S.map_comp ((∫ (CatModel.lift A)).totalMk (𝟙 γ) φ)
      ((∫ (CatModel.lift A)).totalMk (𝟙 γ) ψ)

/-- The section of `Ā → B` of a section of `∫ B⦃𝐩 A⦄`: its restrictions to the fibres, and its
values at the chosen lifts `(g, 𝟙)`. -/
def funSection (S : (funE A B).Section) : (funDisp A B).Section where
  obj γ := funObj S γ
  map {γ γ'} g := ⟨fun x => S.map ((∫ (CatModel.lift A)).totalOlift g x), fun {x y} φ => by
    kernel_exact (S.map_comp ((∫ (CatModel.lift A)).totalMk (𝟙 γ) φ)
      ((∫ (CatModel.lift A)).totalOlift g y)).symm.trans
      (S.map_comp ((∫ (CatModel.lift A)).totalOlift g x)
        ((∫ (CatModel.lift A)).totalMk (𝟙 γ') (((CatModel.lift A).map g).toFunctor.map φ)))⟩
  map_id γ := Section.Hom.ext fun x => by
    kernel_exact S.map_id ((∫ (CatModel.lift A)).tot (a := γ) x)
  map_comp g g' := Section.Hom.ext fun x => by
    kernel_exact S.map_comp ((∫ (CatModel.lift A)).totalOlift g x)
      ((∫ (CatModel.lift A)).totalOlift g' _)

/-- The value at `γ` of a section of `Ā → B`, a section of `∫ B` over `A γ`. -/
def funFib (T : (funDisp A B).Section) (γ : Γ) :
    PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ) :=
  T.obj γ

/-- The transport along `φ` in the value at `γ` of a section of `Ā → B`, a morphism of `∫ B⦃𝐩 A⦄`
over `(𝟙, φ)`. -/
def funFibMap (T : (funDisp A B).Section) (γ : Γ) {x y : (CatModel.lift A).obj γ} (φ : x ⟶ y) :
    (funE A B).Hom ((∫ (CatModel.lift A)).totalMk (𝟙 γ) φ) ((funFib T γ).obj x)
      ((funFib T γ).obj y) :=
  (funFib T γ).map φ

variable (A B) in
/-- The fibre over `A γ` in which the morphisms of `Ā → B` over `g : γ ⟶ γ'` are vertical natural
transformations. -/
abbrev funHomDisp {γ γ' : Γ} (g : γ ⟶ γ') :=
  Fibration.Straightening.fibreDisp (funDom Γ) (piE (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄))
    ((∫ (U (funCtx₀ Γ) ⋙ opFunctor')).tot (a := ((funSub A B).toFunctor.obj γ').1)
      ((∫ (U (funCtx₀ Γ))).push ((funSub A B).toFunctor.map g).base
        ((funSub A B).toFunctor.obj γ).snd))

variable (A B) in
/-- The source of the morphisms of `Ā → B` over `g` from `s`: `x ↦ B g (s x)`. -/
abbrev funHomSrc {γ γ' : Γ} (g : γ ⟶ γ')
    (s : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ)) :
    (funHomDisp A B g).Section :=
  DoubleDisplayed.D2SFib.Straightening.Unstraightening.hobj (funTy Γ)
    ((funSub A B).toFunctor.map g).base ((funSub A B).toFunctor.obj γ).snd s

variable (A B) in
/-- The target of the morphisms of `Ā → B` over `g` to `t`: `x ↦ t (A g x)`. -/
abbrev funHomTgt {γ γ' : Γ} (g : γ ⟶ γ')
    (t : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ')) :
    (funHomDisp A B g).Section :=
  DoubleDisplayed.D2SFib.Straightening.Unstraightening.vobj (funTy Γ)
    ((∫ (U (funCtx₀ Γ))).opcartesianFactor ((funSub A B).toFunctor.map g).fiber) t

/-- The component at `x` of a morphism of `Ā → B` over `g`, a morphism of `∫ B⦃𝐩 A⦄` over the chosen
lift `(g, 𝟙)`. -/
def funAppOf {γ γ' : Γ} (g : γ ⟶ γ') {s : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ)}
    {t : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ')}
    (h : (funDisp A B).Hom g s t) (x : (CatModel.lift A).obj γ) :
    (funE A B).Hom ((∫ (CatModel.lift A)).totalOlift g x) (s.obj x)
      (t.obj (((CatModel.lift A).map g).toFunctor.obj x)) :=
  @Section.Hom.app _ _ (funHomDisp A B g) (funHomSrc A B g s) (funHomTgt A B g t) h x

/-- Morphisms of `Ā → B` with the same components are equal. -/
theorem funHom_ext {γ γ' : Γ} (g : γ ⟶ γ')
    {s : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ)}
    {t : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ')}
    {h k : (funDisp A B).Hom g s t} (happ : ∀ x, funAppOf g h x = funAppOf g k x) : h = k :=
  @Section.Hom.ext _ _ (funHomDisp A B g) (funHomSrc A B g s) (funHomTgt A B g t) h k happ

/-- Morphisms of `Ā → B` between equal objects with the same components are heterogeneously
equal. -/
theorem funHom_hext {γ γ' : Γ} (g : γ ⟶ γ')
    {s s' : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ)}
    {t t' : PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B γ')} (hs : s = s')
    (ht : t = t') {h : (funDisp A B).Hom g s t} {k : (funDisp A B).Hom g s' t'}
    (happ : ∀ x, funAppOf g h x ≍ funAppOf g k x) : h ≍ k := by
  subst hs ht
  exact heq_of_eq (funHom_ext g fun x => eq_of_heq (happ x))

/-- The component at `x` of the transport along `g` of a section of `Ā → B`. -/
abbrev funApp (T : (funDisp A B).Section) {γ γ' : Γ} (g : γ ⟶ γ') (x : (CatModel.lift A).obj γ) :
    (funE A B).Hom ((∫ (CatModel.lift A)).totalOlift g x) ((funFib T γ).obj x)
      ((funFib T γ').obj (((CatModel.lift A).map g).toFunctor.obj x)) :=
  funAppOf g (s := funFib T γ) (t := funFib T γ') (T.map g) x

/-- `funFibMap` preserves identities. -/
theorem funFibMap_id (T : (funDisp A B).Section) (γ : Γ) (x : (CatModel.lift A).obj γ) :
    funFibMap T γ (𝟙 x) =
      (funE A B).id (a := (∫ (CatModel.lift A)).tot (a := γ) x) ((funFib T γ).obj x) := by
  kernel_exact (funFib T γ).map_id x

/-- `funFibMap` preserves composites. -/
theorem funFibMap_comp (T : (funDisp A B).Section) (γ : Γ) {x y z : (CatModel.lift A).obj γ}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    funFibMap T γ (φ ≫ ψ) = (funE A B).comp (funFibMap T γ φ) (funFibMap T γ ψ) := by
  kernel_exact (funFib T γ).map_comp φ ψ

/-- The component along the identity is the identity. -/
theorem funApp_id (T : (funDisp A B).Section) (γ : Γ) (x : (CatModel.lift A).obj γ) :
    funApp T (𝟙 γ) x =
      (funE A B).id (a := (∫ (CatModel.lift A)).tot (a := γ) x) ((funFib T γ).obj x) := by
  kernel_exact congrArg (fun h => funAppOf (𝟙 γ) (s := funFib T γ) (t := funFib T γ) h x)
    (T.map_id γ)

/-- The component along a composite is the composite of the components. -/
theorem funApp_comp (T : (funDisp A B).Section) {γ γ' γ'' : Γ} (g : γ ⟶ γ') (g' : γ' ⟶ γ'')
    (x : (CatModel.lift A).obj γ) :
    funApp T (g ≫ g') x =
      (funE A B).comp (funApp T g x) (funApp T g' (((CatModel.lift A).map g).toFunctor.obj x)) := by
  kernel_exact congrArg (fun h => funAppOf (g ≫ g') (s := funFib T γ) (t := funFib T γ'') h x)
    (T.map_comp g g')

/-- The components along `g` are natural in `x`. -/
theorem funApp_naturality (T : (funDisp A B).Section) {γ γ' : Γ} (g : γ ⟶ γ')
    {x y : (CatModel.lift A).obj γ} (φ : x ⟶ y) :
    (funE A B).comp (funFibMap T γ φ) (funApp T g y) =
      (funE A B).comp (funApp T g x)
        (funFibMap T γ' (((CatModel.lift A).map g).toFunctor.map φ)) := by
  kernel_exact (T.map g).naturality φ

/-- The composition law of the section of `∫ B⦃𝐩 A⦄` of a section `T` of `Ā → B`: over
`(f, φ) ≫ (g, ψ) = (f ≫ g, A g φ ≫ ψ)`, the components along `f` and `g` and the transports along
`A g φ` and `ψ` are rearranged by the naturality of the component along `g`. -/
theorem funMap_comp (T : (funDisp A B).Section) {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ'')
    {x : (CatModel.lift A).obj γ} {y : (CatModel.lift A).obj γ'} {z : (CatModel.lift A).obj γ''}
    (φ : ((CatModel.lift A).map f).toFunctor.obj x ⟶ y)
    (ψ : ((CatModel.lift A).map g).toFunctor.obj y ⟶ z) :
    (funE A B).comp (funApp T (f ≫ g) x)
        (funFibMap T γ'' (((CatModel.lift A).map g).toFunctor.map φ ≫ ψ)) =
      (funE A B).comp ((funE A B).comp (funApp T f x) (funFibMap T γ' φ))
        ((funE A B).comp (funApp T g y) (funFibMap T γ'' ψ)) := by
  have h₁ := congrArg₂ (funE A B).comp (funApp_comp T f g x)
    (funFibMap_comp T γ'' (((CatModel.lift A).map g).toFunctor.map φ) ψ)
  have h₂ := congrArg ((funE A B).comp (funApp T f x) ·)
    (congrArg ((funE A B).comp · (funFibMap T γ'' ψ)) (funApp_naturality T g φ).symm)
  exact h₁.trans h₂

/-- The section of `∫ B⦃𝐩 A⦄` of a section of `Ā → B`: over `(g, φ) = (g, 𝟙) ≫ (𝟙, φ)`, the
component of the transport along `g`, followed by the transport in the fibre along `φ`. -/
def ofFunSection (T : (funDisp A B).Section) : (funE A B).Section where
  obj p := (funFib T p.1).obj p.2
  map {p q} F := by
    kernel_exact (funE A B).comp (funApp T F.base p.2) (funFibMap T q.1 F.fiber)
  map_id p := by
    kernel_exact congrArg₂ (funE A B).comp (funApp_id T p.1 p.2) (funFibMap_id T p.1 p.2)
  map_comp {p q r} F G := by
    kernel_exact funMap_comp T F.base G.base F.fiber G.fiber

/-- A section of `∫ B⦃𝐩 A⦄` is recovered from its restrictions to the fibres. -/
theorem ofFunSection_funSection (S : (funE A B).Section) : ofFunSection (funSection S) = S :=
  Section.ext (fun _ => rfl) fun F => by
    kernel_exact heq_of_eq (S.map_comp ((∫ (CatModel.lift A)).totalOlift F.base _)
      ((∫ (CatModel.lift A)).totalMk (𝟙 _) F.fiber)).symm

/-- A section of `Ā → B` is recovered from the section of `∫ B⦃𝐩 A⦄` it gives. -/
theorem funSection_ofFunSection (T : (funDisp A B).Section) : funSection (ofFunSection T) = T := by
  have hobj : ∀ γ, (funSection (ofFunSection T)).obj γ = T.obj γ := fun γ =>
    Section.ext (fun x => rfl) fun {x y} φ => by
      kernel_exact heq_of_eq
        (congrArg ((funE A B).comp · (funFibMap T γ φ)) (funApp_id T γ x))
  refine Section.ext hobj fun {γ γ'} g => ?_
  refine funHom_hext g (hobj γ) (hobj γ') fun x => ?_
  kernel_exact heq_of_eq
    (congrArg ((funE A B).comp (funApp T g x) ·) (funFibMap_id T γ' _))

/-- **The sections of `Ā → B` are those of `∫ B⦃𝐩 A⦄`.** -/
def funSectionEquiv : (funDisp A B).Section ≃ (funE A B).Section where
  toFun := ofFunSection
  invFun := funSection
  left_inv := funSection_ofFunSection
  right_inv := ofFunSection_funSection

variable (A B) in
/-- **The terms of `Ā → B` are those of `B` in context `Γ ▹ a : A`**: application, with inverse
abstraction. -/
def funTwistEquiv :
    Tm(Γ, funTwist A B) ≃ Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄) :=
  (Equiv.cast (congrArg (fun X => Tm(Γ, X)) (funTwist_eq A B))).trans
    (DisplayedModel.Tm.sectionEquiv.trans (funSectionEquiv.trans CatModel.Tm.sectionEquiv.symm))


variable (A B) in
/-- **Abstraction**, the inverse of `funTwistEquiv`. -/
def funLam : Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄) →
    Tm(Γ, funTwist A B) :=
  (funTwistEquiv A B).symm

/-! ## Stability under substitution -/

section Pull

/- `A` and `B` are declared again after `σ`: with `σ` after them, the elaborator times out on
these statements. -/
variable {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) (A B : Γ ⥤ Cat.{v, v})

/-- The reindexing of `funDisp A B` along `σ` is `funDisp (σ ⋙ A) (σ ⋙ B)`. -/
theorem funDisp_pull :
    DisplayedCat.pull σ (funDisp A B) = funDisp (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) := by
  kernel_rfl'

/-- **`Ā → B` is stable under substitution.** -/
theorem funTwist_pull : (funTwist A B)⦃σ⦄ = funTwist (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) :=
  ((congrArg (fun X => X⦃σ⦄) (funTwist_eq A B)).trans (DisplayedModel.straightenObj_pull _ _)).trans
    ((congrArg Straightening.straightenObj (funDisp_pull σ A B)).trans (funTwist_eq _ _).symm)

/-- The fibre over `A (σ δ)` of the sections in the value of `Ā → B` at `σ δ`, for `A` and `B`
and for `σ ⋙ A` and `σ ⋙ B` at `δ`. -/
theorem funFibreDisp_pull (δ : Δ) :
    Fibration.Straightening.fibreDisp (funDom Δ) (piE (funDom Δ) ((funCod Δ)⦃𝐩 (funDom Δ)⦄))
        (funPt (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) δ) =
      Fibration.Straightening.fibreDisp (funDom Γ) (piE (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄))
        (funPt A B (σ.toFunctor.obj δ)) := by
  kernel_rfl'

/-- The values of `Ā → B` at `σ δ`, for `A` and `B` and for `σ ⋙ A` and `σ ⋙ B` at `δ`. -/
theorem funPiFib_pull (δ : Δ) :
    PiFib (funDom Δ) ((funCod Δ)⦃𝐩 (funDom Δ)⦄) (funPt (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) δ) =
      PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt A B (σ.toFunctor.obj δ)) := by
  kernel_rfl'

/-- The fibre of the morphisms of `Ā → B` over `σ f`, for `A` and `B` and for `σ ⋙ A` and
`σ ⋙ B` over `f`. -/
theorem funHomDisp_pull {δ δ' : Δ} (f : δ ⟶ δ') :
    funHomDisp (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) f = funHomDisp A B (σ.toFunctor.map f) := by
  kernel_rfl'

/-- The sections of the fibre of `funHomDisp_pull`. -/
theorem funHomSection_pull {δ δ' : Δ} (f : δ ⟶ δ') :
    (funHomDisp (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) f).Section =
      (funHomDisp A B (σ.toFunctor.map f)).Section := by
  kernel_rfl'

/-- The sources of the morphisms of `Ā → B` over `σ f`. -/
theorem funHomSrc_pull {δ δ' : Δ} (f : δ ⟶ δ') :
    funHomSrc (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) f ≍ funHomSrc A B (σ.toFunctor.map f) := by
  kernel_rfl'

/-- The targets of the morphisms of `Ā → B` over `σ f`. -/
theorem funHomTgt_pull {δ δ' : Δ} (f : δ ⟶ δ') :
    funHomTgt (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) f ≍ funHomTgt A B (σ.toFunctor.map f) := by
  kernel_rfl'

variable {A B}

/-- The restrictions to the fibres of the section of `t⦃𝐪(σ, A)⦄` are those of `t`, at the images
along `σ`. -/
theorem funObj_pull (t : Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄))
    (δ : Δ) :
    funObj (A := σ.toFunctor ⋙ A) (B := σ.toFunctor ⋙ B)
        (CatModel.Tm.toSection t⦃𝐪(σ, CatModel.lift A)⦄) δ ≍
      funObj (CatModel.Tm.toSection t) (σ.toFunctor.obj δ) :=
  Section.hext (funFibreDisp_pull σ A B δ) (fun x => by
    kernel_exact CatModel.Tm.toSection_pull_obj 𝐪(σ, CatModel.lift A) t
      ((∫ (CatModel.lift (σ.toFunctor ⋙ A))).tot (a := δ) x))
    fun {_ _} φ => by
      kernel_exact CatModel.Tm.toSection_pull_map 𝐪(σ, CatModel.lift A) t
        ((∫ (CatModel.lift (σ.toFunctor ⋙ A))).totalMk (𝟙 δ) φ)

/-- The section of `Ā → B` of `t⦃𝐪(σ, A)⦄` is the reindexing of that of `t` along `σ`: their
restrictions to the fibres and their components along the chosen lifts `(f, 𝟙)` are those of `t`
at the images along `σ`. -/
theorem funSection_pull (t : Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄)) :
    funSection (A := σ.toFunctor ⋙ A) (B := σ.toFunctor ⋙ B)
        (CatModel.Tm.toSection t⦃𝐪(σ, CatModel.lift A)⦄) ≍
      (funSection (CatModel.Tm.toSection t)).pull σ :=
  Section.hext (funDisp_pull σ A B).symm (funObj_pull σ t) fun {δ δ'} f => by
    refine Section.Hom.hext_of_eq (funHomDisp_pull σ A B f)
      (apply_heq (funPiFib_pull σ A B δ) (funHomSection_pull σ A B f) (funHomSrc_pull σ A B f)
        (funObj_pull σ t δ))
      (apply_heq (funPiFib_pull σ A B δ') (funHomSection_pull σ A B f) (funHomTgt_pull σ A B f)
        (funObj_pull σ t δ')) ?hX ?hY fun x => ?_
    case hX => kernel_rfl'
    case hY => kernel_rfl'
    kernel_exact CatModel.Tm.toSection_pull_map 𝐪(σ, CatModel.lift A) t
      ((∫ (CatModel.lift (σ.toFunctor ⋙ A))).totalOlift f x)

/-- The inverse of `Equiv.cast` sends a term to a heterogeneously equal one. -/
theorem equivCast_symm_heq {α β : Sort _} (h : α = β) (y : β) : (Equiv.cast h).symm y ≍ y := by
  cases h
  rfl

/-- Abstraction is the term of the section of `Ā → B` of the section of `t`. The elaborator
reduces the cast of `funTwistEquiv` slowly, so this is stated up to heterogeneous equality. -/
theorem funLam_heq (t : Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄)) :
    funLam A B t ≍ DisplayedModel.Tm.ofSection (funSection (CatModel.Tm.toSection t)) := by
  unfold funLam funTwistEquiv
  rw [Equiv.symm_trans_apply]
  exact (equivCast_symm_heq _ _).trans HEq.rfl

/-- **Abstraction is stable under substitution**, up to the equality of the types
`funTwist_pull`. -/
theorem funLam_pull (t : Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄)) :
    (funLam A B t)⦃σ⦄ ≍ funLam (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) t⦃𝐪(σ, CatModel.lift A)⦄ :=
  (Tm.pull_hcongr σ (funTwist_eq A B) (funLam_heq t)).trans
    ((DisplayedModel.Tm.ofSection_pull σ _).trans
      ((DisplayedModel.Tm.ofSection_hext (funDisp_pull σ A B) (funSection_pull σ t).symm).trans
        (funLam_heq _).symm))

/-- Application sends a term over `t⦃σ⦄` to the substitution of the application of `t` along
`𝐪(σ, A)`. -/
theorem funTwistEquiv_pull_of (t : Tm(Γ, funTwist A B))
    (t' : Tm(Δ, funTwist (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B))) (h : t' ≍ t⦃σ⦄) :
    funTwistEquiv (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) t' =
      (funTwistEquiv A B t)⦃𝐪(σ, CatModel.lift A)⦄ := by
  have ht : t = funLam A B (funTwistEquiv A B t) := ((funTwistEquiv A B).symm_apply_apply t).symm
  have h' := funLam_pull σ (funTwistEquiv A B t)
  rw [← ht] at h'
  rw [eq_of_heq (h.trans h')]
  exact (funTwistEquiv _ _).apply_symm_apply _

/-- **Application is stable under substitution**: the bijection `funTwistEquiv` is natural in
`Γ`. -/
theorem funTwistEquiv_pull (t : Tm(Γ, funTwist A B)) :
    funTwistEquiv (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) (t⦃σ⦄.castTy (funTwist_pull σ A B)) =
      (funTwistEquiv A B t)⦃𝐪(σ, CatModel.lift A)⦄ :=
  funTwistEquiv_pull_of σ t _ (Tm.castTy_heq _ _)

end Pull

end ComprehensionCategory.OverCat
