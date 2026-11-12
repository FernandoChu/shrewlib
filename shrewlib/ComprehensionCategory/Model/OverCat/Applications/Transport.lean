import ComprehensionCategory.Model.OverCat.Shared.HomElim
import ComprehensionCategory.Model.OverCat.Shared.HomDisc
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Unit

/-!
# Transport and the Yoneda lemma

The paper's lemma before the Yoneda corollary (subsection "Yoneda lemma"): for a type `A` and a
discrete type `P` in context `Γ ▹ a : A`, the terms of `P` at the codomain `b` in the context of
Hom-elimination are those of `P` at `a`:

```
  Tm(Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b), P b) ≅ Tm(Γ ▹ a : A, P a)          (yonedaEquiv)
```

The paper states it for `Γ := F : A → U_s` and `P := F a`, with `A` a type in the empty context;
here `Γ`, `A` and `P` are general, and the paper's instance is not derived (it would need the
application of a term of the Π-type `A → U_s` to the variable, decoded in the discrete model).

* The codomain `homCod A : homCtx A ⟶ Γ ▹ A`, `(γ, b, a, f) ↦ (γ, b)`, is given by its values, and
  is the composite of the projections (`homCod_eq`), as the domain `homDom` of `Shared/HomElim`.
  Along the reflexivity `reflSec A`, `(γ, a) ↦ (γ, a, a, 𝟙 a)`, it is the identity, by `rfl`.
* **Transport** (`transport P`), the paper's `j(f, r, r)`: Hom-Elim with `X := P`, the motive
  `P b` weakened by `r : P a` (`transportMotive`), and `d` the variable `r`. By Hom-Comp,
  `j(refl_a, r, r) ≡ r` (`transport_refl`), and transport is stable under substitution
  (`transport_pull`), from `homElim_pull`.
* `yonedaFun θ := θ[a/b, refl_a/f]`, the substitution along `reflSec A`, and `yonedaInv k`, the
  substitution of `r := k` (along the section of `k` weakened along `homDom`) in `transport P`.
* `yonedaFun (yonedaInv k) = k` (`yonedaFun_yonedaInv`) is Hom-Comp: `reflSec A` followed by the
  section of `k⦃homDom A⦄` is the section of `k` followed by `r = homR A P` (`reflSec_comp_sec`),
  and the variable substituted along the section of `k` is `k` (`CatModel.var_pull_sec`).
* `yonedaInv (yonedaFun θ) = θ` (`yonedaInv_yonedaFun`) needs `P` discrete and uniqueness of empty
  types (`hE : EmptyUnique`), for Hom-Disc. As in the paper, it is an instance of a more general
  fact (`eq_of_pull_reflSec`): two terms `a b` of a discrete type over `homCtx A` that agree along
  `reflSec A` are equal. Hom-Elim with `X` the unit type, the motive the Hom-type
  `Hom(a, b)` of the discrete model (`homDiscMotive`, `Shared/HomDisc`) and the premise the
  reflexivity `Refl` of `a[a/b, refl_a/f]` (`homDiscRefl`), which is a term of the substituted
  motive since `b` agrees with `a` along `reflSec A` (`homDiscAt_pull_reflSec`, `homDiscPremise`),
  gives a term of `Hom(a, b)`, after substituting the star for `x`. By Hom-Disc
  (`eq_of_homDiscAt`), `a = b`. For `a := θ` and `b := yonedaInv (yonedaFun θ)`, they agree along
  `reflSec A` by `yonedaFun_yonedaInv`.

The terms of `P` in the category model are compared with those of the discrete model through
`forgetComprehensionMap.tmEquiv`, which keeps the sections and commutes with substitution by `rfl`.

**The bijection is natural in `Γ`**: `yonedaFun` commutes with the substitutions `homCtxMap σ A`
and `𝐪(σ, A)` (`yonedaFun_pull`), since `reflSec (A⦃σ⦄) ≫ homCtxMap σ A = 𝐪(σ, A) ≫ reflSec A` by
`rfl` (`reflSec_homCtxMap`), and so does its inverse (`yonedaInv_pull`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ)

/-! ## The codomain -/

/-- The codomain `homCtx A ⟶ Γ ▹ A`, `(γ, b, a, f) ↦ (γ, b)`. -/
def homCod : homCtx A ⟶ Γ ▹ A :=
  (show (homCtx A : Type u) ⥤ (Γ ▹ A : Cat.{u, u}) from
    { obj p := p.1.1
      map k := k.base.base
      map_id _ := rfl
      map_comp _ _ := rfl }).toCatHom

/-- The codomain is the projection of the twisted Hom-type followed by that of `A⦃𝐩 A⦄`. -/
theorem homCod_eq : homCod A = 𝐩 (twist (homFunctor A)) ≫ 𝐩 (A⦃𝐩 A⦄) := by
  kernel_exact (congrArg (· ≫ 𝐩 (A⦃𝐩 A⦄))
    (DisplayedModel.proj_straightenObj (twistDisp (homFunctor A)))).symm

/-- The reflexivity is a section of the codomain. -/
theorem reflSec_homCod : reflSec A ≫ homCod A = 𝟙 (Γ ▹ A) :=
  rfl

/-! ## Transport -/

variable {A} (P : ICatLax.{u, u}.Ty (Γ ▹ A))

/-- The motive of transport, `P b` in context `Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b) ▹ r : P a`. -/
abbrev transportMotive : ICatLax.{u, u}.Ty (elimCtx A P) :=
  P⦃homCod A⦄⦃𝐩 (P⦃homDom A⦄)⦄

/-- **Transport**, the paper's `j(f, r, r) : P b` in context
`Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b) ▹ r : P a`: Hom-Elim with `X := P`, the motive `P b` and the
premise the variable `r`. -/
def transport : Tm(elimCtx A P, transportMotive P) :=
  homElim (transportMotive P) (var P)

/-- **Transport along the reflexivity is the identity**: `j(refl_a, r, r) ≡ r`, by Hom-Comp. -/
theorem transport_refl : (transport P)⦃homR A P⦄ = var P :=
  homElim_pull_homR _ _

variable {P}

/-- `θ[a/b, refl_a/f]`: the substitution of a term of `P b` along the reflexivity, a term of `P`,
since `reflSec A ≫ homCod A = 𝟙`. -/
def yonedaFun (θ : Tm(homCtx A, P⦃homCod A⦄)) : Tm(Γ ▹ A, P) :=
  θ⦃reflSec A⦄

/-- A type weakened along `𝐩 B` and substituted along the section of a term of `B` is the type,
since `t.sec ≫ 𝐩 B = 𝟙`. -/
theorem pull_proj_sec {Δ : Cat.{u, u}} {B : ICatLax.{u, u}.Ty Δ} (C : ICatLax.{u, u}.Ty Δ)
    (t : Tm(Δ, B)) : C⦃𝐩 B⦄⦃t.sec⦄ = C :=
  congrArg (fun σ => C⦃σ⦄) t.sec_proj

/-- `j(f, k, k)`: transport with `r := k`, the substitution of `transport P` along the section of
`k` weakened along the domain. -/
def yonedaInv (k : Tm(Γ ▹ A, P)) : Tm(homCtx A, P⦃homCod A⦄) :=
  ((transport P)⦃(k⦃homDom A⦄).sec⦄).castTy (pull_proj_sec (P⦃homCod A⦄) (k⦃homDom A⦄))

/-- Substitutions of a term along equal morphisms are heterogeneously equal. -/
theorem pull_heq_of_eq {Δ Θ : Cat.{u, u}} {B : ICatLax.{u, u}.Ty Θ} {σ σ' : Δ ⟶ Θ}
    (h : σ = σ') (t : Tm(Θ, B)) : t⦃σ⦄ ≍ t⦃σ'⦄ := by
  subst h
  rfl

/-- A term weakened along the domain and substituted along the reflexivity is the term. -/
theorem pull_homDom_reflSec (k : Tm(Γ ▹ A, P)) : (k⦃homDom A⦄)⦃reflSec A⦄ = k := by
  kernel_exact (Displayed.Tm.pull_comp (reflSec A) (homDom A) k).symm.trans
    (Displayed.Tm.pull_id k)

/-- The reflexivity followed by the section of `k⦃homDom A⦄` is the section of `k` followed by
`r = homR A P`. -/
theorem reflSec_comp_sec (k : Tm(Γ ▹ A, P)) :
    reflSec A ≫ (k⦃homDom A⦄).sec = k.sec ≫ homR A P := by
  refine (Displayed.Tm.pull_sec_q (reflSec A) (k⦃homDom A⦄)).symm.trans ?_
  kernel_exact congrArg (fun t : Tm(Γ ▹ A, P) => t.sec ≫ homR A P) (pull_homDom_reflSec k)

/-- **`j(refl_a, k, k) ≡ k`**, by Hom-Comp. -/
theorem yonedaFun_yonedaInv (k : Tm(Γ ▹ A, P)) : yonedaFun (yonedaInv k) = k := by
  have h' := pull_proj_sec (P⦃homCod A⦄) (k⦃homDom A⦄)
  refine eq_of_heq ((Tm.pull_hcongr (reflSec A) h'.symm
    (Tm.castTy_heq h' ((transport P)⦃(k⦃homDom A⦄).sec⦄))).trans ?_)
  refine (heq_of_eq (Displayed.Tm.pull_comp (reflSec A) (k⦃homDom A⦄).sec
    (transport P))).symm.trans ?_
  refine (pull_heq_of_eq (reflSec_comp_sec k) (transport P)).trans ?_
  refine (heq_of_eq (Displayed.Tm.pull_comp k.sec (homR A P) (transport P))).trans ?_
  refine (Tm.pull_hcongr k.sec rfl (heq_of_eq (transport_refl P))).trans ?_
  exact var_pull_sec k

/-! ## Uniqueness along the reflexivity, by Hom-Disc -/

section Disc

variable (hE : EmptyUnique.{u}) {B : IDisc.{u, u}.Ty (homCtx A)}

/-- The Hom-type from `a` to `b`, substituted along the reflexivity, is that from `a` to itself
there, when `b` agrees with `a` along the reflexivity. -/
theorem homDiscAt_pull_reflSec (a b : Tm(homCtx A, B)) (h : b⦃reflSec A⦄ = a⦃reflSec A⦄) :
    (homDiscAt (Tm.toOp hE a) b)⦃reflSec A⦄ =
      homDiscAt (Tm.toOp hE (a⦃reflSec A⦄)) (a⦃reflSec A⦄) := by
  kernel_exact (pull_homDiscAt (reflSec A) (Tm.toOp hE a) b).trans
    (congrArg₂ (homDiscAt (A := B⦃reflSec A⦄)) (toOp_pull hE (reflSec A) a) h)

/-- The motive `Hom(a, b)` of the uniqueness, a discrete type seen in the category model, weakened
along the unit type `x : 1`. -/
abbrev homDiscMotive (a b : Tm(homCtx A, B)) :
    ICatLax.{u, u}.Ty (elimCtx A (CatModel.unit (Γ ▹ A))) :=
  (forgetComprehensionMap.toPre.obj (homDiscAt (Tm.toOp hE a) b))⦃𝐩 (CatModel.unit (homCtx A))⦄

/-- The premise: the reflexivity `Refl` of `a[a/b, refl_a/f]`, a term of the motive substituted
along `r`, weakened along `x : 1`. -/
def homDiscPremise (a b : Tm(homCtx A, B)) (h : b⦃reflSec A⦄ = a⦃reflSec A⦄) :
    Tm(Γ ▹ A ▹ CatModel.unit (Γ ▹ A),
      (homDiscMotive hE a b)⦃homR A (CatModel.unit (Γ ▹ A))⦄) :=
  (forgetComprehensionMap.tmEquiv ((homDiscRefl hE (a⦃reflSec A⦄)).castTy
    (homDiscAt_pull_reflSec hE a b h).symm))⦃𝐩 (CatModel.unit (Γ ▹ A))⦄

include hE in
/-- **Two terms of a discrete type over `homCtx A` that agree along the reflexivity are equal**:
Hom-Elim gives a term of the Hom-type from one to the other, and Hom-Disc concludes. -/
theorem eq_of_pull_reflSec (a b : Tm(homCtx A, B)) (h : b⦃reflSec A⦄ = a⦃reflSec A⦄) : a = b :=
  eq_of_homDiscAt hE a b (forgetComprehensionMap.tmEquiv.symm
    ((homElim (homDiscMotive hE a b) (homDiscPremise hE a b h))⦃(CatModel.star (homCtx A)).sec⦄))

variable {Pd : IDisc.{u, u}.Ty (Γ ▹ A)}

include hE in
/-- **`j(f, θ*, θ*) ≡ θ`** for `θ*` the substitution of `θ` along the reflexivity: both agree along
the reflexivity, by `yonedaFun_yonedaInv`. -/
theorem yonedaInv_yonedaFun (θ : Tm(homCtx A, (forgetComprehensionMap.toPre.obj Pd)⦃homCod A⦄)) :
    yonedaInv (yonedaFun θ) = θ := by
  have h : (forgetComprehensionMap.tmEquiv.symm (yonedaInv (yonedaFun θ)) :
      Tm(homCtx A, Pd⦃homCod A⦄))⦃reflSec A⦄ =
        (forgetComprehensionMap.tmEquiv.symm θ : Tm(homCtx A, Pd⦃homCod A⦄))⦃reflSec A⦄ := by
    apply forgetComprehensionMap.tmEquiv.injective
    kernel_exact (forgetComprehensionMap_tmEquiv_pull (reflSec A)
      (forgetComprehensionMap.tmEquiv.symm (yonedaInv (yonedaFun θ)) :
        Tm(homCtx A, Pd⦃homCod A⦄))).trans
      ((yonedaFun_yonedaInv (yonedaFun θ)).trans
        (forgetComprehensionMap_tmEquiv_pull (reflSec A)
          (forgetComprehensionMap.tmEquiv.symm θ : Tm(homCtx A, Pd⦃homCod A⦄))).symm)
  exact (congrArg forgetComprehensionMap.tmEquiv (eq_of_pull_reflSec hE
    (forgetComprehensionMap.tmEquiv.symm θ : Tm(homCtx A, Pd⦃homCod A⦄)) _ h)).symm

/-- **The paper's lemma before the Yoneda corollary**: for a discrete type `P` in context
`Γ ▹ a : A`, the terms of `P b` in context `Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b)` are those of
`P a` in context `Γ ▹ a : A`, by substitution along the reflexivity and transport. -/
def yonedaEquiv :
    Tm(homCtx A, (forgetComprehensionMap.toPre.obj Pd)⦃homCod A⦄) ≃
      Tm(Γ ▹ A, forgetComprehensionMap.toPre.obj Pd) where
  toFun := yonedaFun
  invFun := yonedaInv
  left_inv := yonedaInv_yonedaFun hE
  right_inv := yonedaFun_yonedaInv

end Disc

/-! ## Stability under substitution -/

section Pull

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)

variable (A) in
/-- The substitution `homCtxMap σ A` commutes with the reflexivities, by `rfl`. -/
theorem reflSec_homCtxMap : reflSec (A⦃σ⦄) ≫ homCtxMap σ A = 𝐪(σ, A) ≫ reflSec A := by
  kernel_rfl'

/-- **`yonedaFun` is natural in `Γ`**: it commutes with the substitutions `homCtxMap σ A` and
`𝐪(σ, A)`. -/
theorem yonedaFun_pull (θ : Tm(homCtx A, P⦃homCod A⦄)) :
    yonedaFun (A := A⦃σ⦄) (P := P⦃𝐪(σ, A)⦄) θ⦃homCtxMap σ A⦄ = (yonedaFun θ)⦃𝐪(σ, A)⦄ :=
  eq_of_heq ((heq_of_eq (Displayed.Tm.pull_comp (reflSec (A⦃σ⦄)) (homCtxMap σ A) θ)).symm.trans
    ((pull_heq_of_eq (reflSec_homCtxMap A σ) θ).trans
      (heq_of_eq (Displayed.Tm.pull_comp 𝐪(σ, A) (reflSec A) θ))))

/-- **`yonedaInv` is natural in `Γ`**, as the inverse of `yonedaFun`. -/
theorem yonedaInv_pull (hE : EmptyUnique.{u}) {Pd : IDisc.{u, u}.Ty (Γ ▹ A)}
    (k : Tm(Γ ▹ A, forgetComprehensionMap.toPre.obj Pd)) :
    yonedaInv (A := A⦃σ⦄) (P := (forgetComprehensionMap.toPre.obj Pd)⦃𝐪(σ, A)⦄) k⦃𝐪(σ, A)⦄ =
      (yonedaInv k)⦃homCtxMap σ A⦄ := by
  apply (yonedaEquiv (A := A⦃σ⦄) (Pd := Pd⦃𝐪(σ, A)⦄) hE).injective
  exact (yonedaFun_yonedaInv _).trans ((yonedaFun_pull σ (yonedaInv k)).trans
    (congrArg (·⦃𝐪(σ, A)⦄) (yonedaFun_yonedaInv k))).symm

variable (P) in
/-- The variable is stable under substitution. -/
theorem var_pull_q : (var P)⦃𝐪(𝐪(σ, A), P)⦄ = var (P⦃𝐪(σ, A)⦄) :=
  (Displayed.Tm.pull_unique _ (var P) _
    (Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl'))).symm

variable (P) in
/-- **Transport is stable under substitution**, along `σ⁺ = elimCtxMap σ A P`, by `homElim_pull`. -/
theorem transport_pull : (transport P)⦃elimCtxMap σ A P⦄ = transport (P⦃𝐪(σ, A)⦄) := by
  have h : homElim (transportMotive P⦃𝐪(σ, A)⦄) ((var P)⦃𝐪(𝐪(σ, A), P)⦄) =
      transport (P⦃𝐪(σ, A)⦄) :=
    congrArg (homElim (transportMotive P⦃𝐪(σ, A)⦄)) (var_pull_q P σ)
  kernel_exact (homElim_pull σ (transportMotive P) (var P)).trans h

end Pull

end ComprehensionCategory.OverCat
