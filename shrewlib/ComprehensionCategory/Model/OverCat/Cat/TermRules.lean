import ComprehensionCategory.Model.OverCat.Cat.Term

/-!
# Terms in the category model compute, by rules

A term `t : Tm(Γ, A)` of the category model is a functor `t.sec : Γ ⥤ Γ ⋉ A` with
`t.sec ≫ 𝐩 A = 𝟙 Γ`, so the first component of `t.sec γ` is `γ` only propositionally
(`Cat/Term`). This file makes it so definitionally, with three rules:

* `(t.sec γ).1 = γ` and `(t.sec f).base = f` (`Tm.sec_obj_fst`, `Tm.sec_map_base`), the equation
  `t.sec_proj` on objects and on morphisms, oriented towards the points and morphisms of `Γ`. They
  are stated for the functor `t.sec.toFunctor`, the most unfolded form, and are keyed on the
  projections `Sigma.fst` and `Total.Hom.base`.
* `t⦃σ⦄.sec = ((Tm.toSection t).pull σ).total` (`Tm.pull_sec`): the section of a substituted term
  is that of the reindexed section, `δ ↦ (δ, t (σ δ))`. It is keyed on `Tm.sec`, with the
  substitution `Tm.pull` of the category model as its argument.

By the first two, the second component of `t.sec γ` is in `A γ` with no transport, and the
transports in the substitution of a term and in its section `Tm.toSection t` reduce away: for
instance `(var A)⦃t.sec⦄ = t` and `Tm.toSection t⦃σ⦄ = (Tm.toSection t).pull σ` hold by `rfl` in the
kernel. The kernel also reduces the factorization of `Tm.pull` through the pullback square of
`𝐪(σ, A)` to the reindexed section, but the elaborator does so only slowly, hence the third rule.
With them, constructions of the internal language from a term compute, as the context and the
substitutions of Hom-elimination at a term (`Shared/HomIntro`, `Shared/HomElim`).

The rules are not in `Cat/Term`, and are imported only where they are used: once `Tm.sec` is the
head of a rule, definitional equality compares the arguments of two applications of it before
unfolding them, and proofs that compare the sections of terms of two models through their
unfoldings (`Shared/HomDisc`, `Shared/Pi`) no longer check.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

variable {Γ Δ : Cat.{u, u}}

/-- **The first component of `t.sec γ` is `γ`**: the equation `t.sec_proj` on objects, as a rule. -/
@[rewrite_rule]
theorem Tm.sec_obj_fst {A : ICatLax.{u, u}.Ty Γ} (t : Tm(Γ, A)) (γ : Γ) :
    (t.sec.toFunctor.obj γ).1 = γ :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor t.sec_proj) γ

/-- **The first component of `t.sec f` is `f`**: the equation `t.sec_proj` on morphisms, as a rule.
Its statement typechecks by the rule `Tm.sec_obj_fst`. -/
@[rewrite_rule]
theorem Tm.sec_map_base {A : ICatLax.{u, u}.Ty Γ} (t : Tm(Γ, A)) {γ γ' : Γ} (f : γ ⟶ γ') :
    (t.sec.toFunctor.map f).base = f :=
  eq_of_heq (Functor.hcongr_hom (congrArg Cat.Hom.toFunctor t.sec_proj) f)

/-- **The section of a substituted term is that of the reindexed section**,
`δ ↦ (δ, t (σ δ))`, as a rule, for the elaborator to compute substituted terms. -/
@[rewrite_rule]
theorem Tm.pull_sec {A : ICatLax.{u, u}.Ty Γ} (σ : Δ ⟶ Γ) (t : Tm(Γ, A)) :
    t⦃σ⦄.sec = ((Tm.toSection t).pull σ).total.toCatHom :=
  congrArg Displayed.Tm.sec ((Tm.sectionEquiv.left_inv t⦃σ⦄).symm.trans
    (congrArg (Tm.ofSection (A := A⦃σ⦄)) (Tm.toSection_pull σ t)))

end ComprehensionCategory.CatModel
