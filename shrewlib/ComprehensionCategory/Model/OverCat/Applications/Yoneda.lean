import ComprehensionCategory.Model.OverCat.Shared.HomElim
import ComprehensionCategory.Model.OverCat.Shared.HomDisc
import ComprehensionCategory.Model.OverCat.Shared.Pi
import ComprehensionCategory.Model.OverCat.Shared.Universe

/-!
# The Yoneda lemma

The paper's lemma before the Yoneda corollary (`lem:yoneda`): for a type `A` in the empty context,
a context `Γ` and terms `F : A → U_s` and `a₀ : A` in context `Γ`, the terms of `F b` in the context
of Hom-elimination are those of `F a₀`:

```
  Tm(Γ ▹ b : A ▹ f : Homₐ(ā₀, b), F b) ≅ Tm(Γ, F a₀)          (yonedaEquiv)
```

`A` is a category of level `v + 1`, seen in context `Γ` as the constant type at `A`, of the
category model (`CatModel.constTy Γ A`) and of the contravariant one. `A → U_s` is the Π-type of
the universe of discrete types of level `v` over it (`copresheafTy`, `Shared/Pi`,
`Shared/Universe`), `F b` the application of `F` decoded, a discrete type in context `Γ ▹ b : A`
(`app F`), and `F a₀` its substitution `(app F)⦃a₀.sec⦄` (`appAt F a₀`).

The proof is that of the paper:

* `yonedaFun θ := θ[a₀/b, refl_a₀/f]`, the substitution along `r = homElimR a₀`. It is a term of
  `(F b)[a₀/b, refl_a₀/f]`, which is `F a₀` since `r` followed by the codomain is the section of
  `a₀` (`homElimR_homElimCod`). This equality of types is a rule declared in this file
  (`pull_homElimCod_homElimR`), so that `θ[a₀/b, refl_a₀/f]` is not transported, nor the premise
  `k` of Hom-Elim below.
* `yonedaInv k := j(f, k)`, Hom-Elim with the motive `F b` and the premise `k`. It corresponds to
  the transport of HoTT.
* `yonedaFun (yonedaInv k) = k` (`yonedaFun_yonedaInv`) is Hom-Comp, `j(refl_a₀, k) ≡ k`, a rule
  in this file too (`homComp`).
* `yonedaInv (yonedaFun θ) = θ` (`yonedaInv_yonedaFun`) uses that `F b` is discrete, and
  uniqueness of empty types (`hE : EmptyUnique`), for Hom-Disc. With `θ* := yonedaFun θ`, Hom-Elim
  with the motive the Hom-type `Hom_{F b}(θ, j(f, θ*))` of the discrete model (`yonedaHom`) and
  the premise the reflexivity `Refl_{θ*}` (`yonedaRefl`) gives a term of this Hom-type
  (`yonedaHomTm`), and Hom-Disc concludes. The premise is a term of `Hom_{F a₀}(θ*, θ*)`, which is
  the motive along `r` (`yonedaHom_pull_homElimR`): the Hom-type is stable under substitution, and
  `j(f, θ*)` is `θ*` along `r`, by Hom-Comp. This last step is definitional, by the rules, but the
  stability of the Hom-type is not, so the premise is transported along this equality.

The file declares three rules, as conveniences (section Helpers), each oriented from left to right:
`P⦃homElimCod a₀⦄⦃homElimR a₀⦄ ↦ P⦃a₀.sec⦄` (`pull_homElimCod_homElimR`), Hom-Comp
`(homElim D d)⦃homElimR a₀⦄ ↦ d` (`homComp`), and `(discTm t)⦃σ⦄ ↦ discTm (t⦃σ⦄)`
(`discTm_pull`).

The Hom-type of `F b` is that of the discrete model, so the terms `θ` and `j(f, θ*)` of the
category model are seen there by `discTm`, the inverse of `forgetComprehensionMap.tmEquiv`: it
keeps the sections, and commutes with substitution as any strict map
(`StrictComprehensionMap.tmEquiv_pull`).
-/

universe u v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

/-! ## Helpers: rules for this file

These are not part of the lemma. They are conveniences that make three equations definitional in
this file, so that the proof below reads as in the paper. Each is oriented from left to right:

* `pull_homElimCod_homElimR`: `P⦃homElimCod a₀⦄⦃homElimR a₀⦄ ↦ P⦃a₀.sec⦄`. So
  `(F b)[a₀/b, refl_a₀/f]` is `F a₀`, and `yonedaFun` and `yonedaInv` need no transport along an
  equality of types;
* `homComp`, Hom-Comp: `(homElim D d)⦃homElimR a₀⦄ ↦ d`;
* `discTm_pull`, for the helper `discTm`: `(discTm t)⦃σ⦄ ↦ discTm (t⦃σ⦄)`. Seeing a term in the
  discrete model is pushed outside substitutions, so that Hom-Comp applies under it, and no
  equation between `θ` and `j(f, θ*)` along `r` has to be carried in the discrete model.

One transport remains: the premise `Refl_{θ*}` is transported to the motive along `r`
(`yonedaRefl`), an equality of types that is not definitional (`yonedaHom_pull_homElimR`).

The rules are declared here only, and are seen by this file and the `Readme`s that import it. -/

/-- **`P[a₀/b, refl_a₀/f]` is `P a₀`, as a rule**: for a type `P` in context `Γ ▹ b : B`, its
weakening to the context of Hom-elimination, substituted along `r`, is `P⦃a₀.sec⦄`, since `r`
followed by the codomain is the section of `a₀` (`homElimR_homElimCod`). This is not `rfl`: the
values of `r` are those of the section of `a₀`, whose first components are the points of `Γ`, while
those of the values of `a₀.sec` only equal them. The rule is declared after
`PreSplitFib.pull_comp`, with the same head, and is used first on the terms that it matches. -/
@[rewrite_rule]
theorem pull_homElimCod_homElimR {Γ : Cat.{u, u}} {B : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, B))
    (P : ICatLax.{u, u}.Ty (Γ ▹ B)) : P⦃homElimCod a₀⦄⦃homElimR a₀⦄ = P⦃a₀.sec⦄ := by
  kernel_exact congrArg (fun τ => P⦃τ⦄) (homElimR_homElimCod a₀)

-- Hom-Comp, `j(refl_a₀, d) ≡ d`, as a rule: `(homElim D d)⦃homElimR a₀⦄` rewrites to `d`.
attribute [rewrite_rule] homComp

/-- A term of a discrete type, in the category model, as a term of the discrete model, with the
same section: the inverse of `forgetComprehensionMap.tmEquiv`, as a constant for the rule
`discTm_pull`. -/
def discTm {Γ : Cat.{u, u}} {P : IDisc.{u, u}.Ty Γ}
    (t : Tm(Γ, forgetComprehensionMap.toPre.obj P)) : Tm(Γ, P) :=
  forgetComprehensionMap.tmEquiv.symm t

/-- **Seeing a term in the discrete model commutes with substitution, as a rule**, from the fact
for any strict map (`StrictComprehensionMap.tmEquiv_pull`). With Hom-Comp, the terms `θ` and
`j(f, θ*)` are then equal along `r` in the discrete model too, definitionally. -/
@[rewrite_rule]
theorem discTm_pull {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {P : IDisc.{u, u}.Ty Γ}
    (t : Tm(Γ, forgetComprehensionMap.toPre.obj P)) :
    (discTm t)⦃σ⦄ = discTm (P := P⦃σ⦄) (t⦃σ⦄) :=
  forgetComprehensionMap.tmEquiv.injective
    (by kernel_exact eq_of_heq (forgetComprehensionMap.tmEquiv_pull σ (discTm t)))

/-- Terms with the same image in the discrete model are equal. -/
theorem discTm_injective {Γ : Cat.{u, u}} {P : IDisc.{u, u}.Ty Γ} :
    Function.Injective (discTm (P := P)) :=
  forgetComprehensionMap.tmEquiv.symm.injective

/-! ## The types `A → U_s`, `F b` and `F a₀`

A category `A`, a type in the empty context, is in context `Γ` the constant type at `A`, covariant
and contravariant, and the two extensions of `Γ` by it are the same category, by `rfl`.
So the application of a term `F` of `A → U_s`, a term of the universe in the contravariant
extension, decodes to a discrete type `F b` in context `Γ ▹ b : A` (`app F`). -/

variable {Γ : Cat.{v + 1, v + 1}} {A : Cat.{v + 1, v + 1}}

variable (Γ A) in
/-- The type `A → U_s` in context `Γ`, for a category `A`, a type in the empty context: the Π-type
of the universe of discrete types over the constant type at `A`, contravariant. -/
abbrev copresheafTy : ICatLax.{v + 1, v + 1}.Ty Γ :=
  piTy (CatOpModel.constTy Γ A) (UDisc _)

/-- `F b`, in the category model. -/
abbrev app (F : Tm(Γ, copresheafTy Γ A)) :
    ICatLax.{v + 1, v + 1}.Ty (Γ ▹ CatModel.constTy Γ A) :=
  forgetComprehensionMap.toPre.obj <| liftDisc (ElDisc (piApp F))

/-- `F a₀`: the type `F b`, substituted by `a₀`. -/
abbrev appAt (F : Tm(Γ, copresheafTy Γ A)) (a₀ : Tm(Γ, CatModel.constTy Γ A)) :
    ICatLax.{v + 1, v + 1}.Ty Γ :=
  (app F)⦃a₀.sec⦄

variable {F : Tm(Γ, copresheafTy Γ A)} {a₀ : Tm(Γ, CatModel.constTy Γ A)}

/-! ## The bijection -/

/-- `θ[a₀/b, refl_a₀/f]`: the substitution of a term of `F b` along `r`, a term of `F a₀`. -/
def yonedaFun (θ : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄)) : Tm(Γ, appAt F a₀) :=
  θ⦃homElimR a₀⦄

/-- `j(f, k)`: Hom-Elim with the motive `F b` and the premise `k`, a term of `F a₀`. It corresponds
to the transport of HoTT. -/
def yonedaInv (k : Tm(Γ, appAt F a₀)) : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄) :=
  homElim ((app F)⦃homElimCod a₀⦄) k

/-- **`j(refl_a₀, k) ≡ k`**: this is Hom-Comp. -/
theorem yonedaFun_yonedaInv (k : Tm(Γ, appAt F a₀)) : yonedaFun (yonedaInv k) = k := by
  kernel_exact homComp ((app F)⦃homElimCod a₀⦄) k

/-! ## `j(f, θ*) ≡ θ`, by Hom-Elim and Hom-Disc

For a term `θ` of `F b`, with `θ* := θ[a₀/b, refl_a₀/f]`. The Hom-type of `F b` is that of the
discrete model, so `θ` and `j(f, θ*)` are taken there (`toDisc`), and the Hom-type in the category
model, for Hom-Elim. -/

variable (hE : EmptyUnique.{v + 1}) (θ : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄))

-- The proof does not unfold `F b`, and the elaborator times out reducing its substitutions.
attribute [local irreducible] liftDisc

/-- A term of `F b`, as a term of the discrete model, with the same section. -/
abbrev toDisc (t : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄)) :
    Tm(homElimCtx a₀, (liftDisc (ElDisc (piApp F)))⦃homElimCod a₀⦄) :=
  discTm t

/-- **The motive `Hom_{F b}(θ, j(f, θ*))`**, a type of the discrete model. The term `θ`, in the
contravariant position, is a term of `(F b)ᵒᵖ`, which is `F b` if empty types are unique. -/
abbrev yonedaHom : IDisc.{v + 1, v + 1}.Ty (homElimCtx a₀) :=
  homDiscAt (Tm.toOp hE (toDisc θ)) (toDisc (yonedaInv (yonedaFun θ)))

/-- **The motive along `r` is `Hom_{F a₀}(θ*, θ*)`**: the Hom-type is stable under substitution, and
`j(f, θ*)[a₀/b, refl_a₀/f]` is `θ*` by Hom-Comp. -/
theorem yonedaHom_pull_homElimR :
    (yonedaHom hE θ)⦃homElimR a₀⦄ =
      homDiscAt (Tm.toOp hE ((toDisc θ)⦃homElimR a₀⦄)) ((toDisc θ)⦃homElimR a₀⦄) := by
  kernel_exact (pull_homDiscAt (homElimR a₀) (Tm.toOp hE (toDisc θ))
    (toDisc (yonedaInv (yonedaFun θ)))).trans
    (congrArg (fun a => homDiscAt (A := (liftDisc (ElDisc (piApp F)))⦃homElimCod a₀⦄⦃homElimR a₀⦄) a
      ((toDisc θ)⦃homElimR a₀⦄)) (toOp_pull hE (homElimR a₀) (toDisc θ)))

/-- **The premise `Refl_{θ*}`**, a term of `Hom_{F a₀}(θ*, θ*)`, the motive along `r`. -/
def yonedaRefl :
    Tm(Γ, (forgetComprehensionMap.toPre.obj (yonedaHom hE θ))⦃homElimR a₀⦄) := by
  kernel_exact forgetComprehensionMap.tmEquiv ((homDiscRefl hE ((toDisc θ)⦃homElimR a₀⦄)).castTy
    (yonedaHom_pull_homElimR hE θ).symm)

/-- **Hom-Elim: the term `j(f, Refl_{θ*})` of `Hom_{F b}(θ, j(f, θ*))`**, with the motive
`yonedaHom` and the premise `yonedaRefl`. -/
def yonedaHomTm : Tm(homElimCtx a₀, yonedaHom hE θ) :=
  discTm (homElim (forgetComprehensionMap.toPre.obj (yonedaHom hE θ)) (yonedaRefl hE θ))

include hE in
/-- **`j(f, θ*) ≡ θ`, by discreteness of `F b`**: there is a term of `Hom_{F b}(θ, j(f, θ*))`
(`yonedaHomTm`), so the two terms are equal (Hom-Disc). -/
theorem yonedaInv_yonedaFun : yonedaInv (yonedaFun θ) = θ :=
  (discTm_injective
    (eq_of_homDiscAt hE (toDisc θ) (toDisc (yonedaInv (yonedaFun θ))) (yonedaHomTm hE θ))).symm

variable (F a₀) in
/-- **The paper's lemma before the Yoneda corollary**: for a type `A` in the empty context and
terms `F : A → U_s` and `a₀ : A` in context `Γ`, the terms of `F b` in context
`Γ ▹ b : A ▹ f : Homₐ(ā₀, b)` are those of `F a₀` in context `Γ`, by substitution along the
reflexivity and Hom-Elim. -/
def yonedaEquiv : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄) ≃ Tm(Γ, appAt F a₀) where
  toFun := yonedaFun
  invFun := yonedaInv
  left_inv := yonedaInv_yonedaFun hE
  right_inv := yonedaFun_yonedaInv

end ComprehensionCategory.OverCat
