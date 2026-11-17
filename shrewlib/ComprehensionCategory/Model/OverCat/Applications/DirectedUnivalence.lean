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

As a vertical isomorphism of `IDisc` (`IDisc.isoOfNatIso`), it gives the bijection of terms
(`Tm.mapEquiv`, `ComprehensionCategory/Term`), which is natural in `Γ` (`Tm.mapEquiv_pull`).

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
  Tm.mapEquiv (IDisc.isoOfNatIso (dunivIso A B))

/-- **The bijection is natural in `Γ`**, up to the equalities `funU_pull` and `homU_pull`. -/
theorem dunivTmEquiv_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) (t : Tm(Γ, funU A B)) :
    (dunivTmEquiv A B t)⦃σ⦄.castTy (homU_pull A B σ) =
      dunivTmEquiv (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) (t⦃σ⦄.castTy (funU_pull A B σ)) := by
  -- Stated in steps: elaborated as one term, the unification of the types times out.
  have h1 := Tm.mapEquiv_pull σ (IDisc.isoOfNatIso (dunivIso A B))
    (e' := IDisc.isoOfNatIso (X := (funU A B)⦃σ⦄) (Y := (homU A B)⦃σ⦄)
      (Functor.isoWhiskerLeft σ.toFunctor (dunivIso A B)))
    (IDisc.pullMap_homOfNatTrans σ (dunivIso A B).hom).symm t
  have h2 := Tm.mapEquiv_hcongr (funU_pull A B σ) (homU_pull A B σ)
    (IDisc.isoOfNatIso_hcongr (funU_pull A B σ) (homU_pull A B σ) (dunivIso_pull σ))
    (Tm.castTy_heq (funU_pull A B σ) t⦃σ⦄).symm
  exact eq_of_heq ((Tm.castTy_heq _ _).trans ((heq_of_eq h1).trans h2))

end Small

end ComprehensionCategory.OverCat
