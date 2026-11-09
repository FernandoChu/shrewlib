import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat

/-!
# Hom-types of discrete types

The Hom-types of a type `A` of the discrete model are those of `A` in the category model:

* `homDisc A`, in context `Γ ▹ b : A ▹ a : Aᵒᵖ` of the discrete model, is `Hom[A]` of the category
  model, whose context is the same (`homDisc_eq`);
* `homDiscAt a b`, for terms `a : Tm(Γ, Aᵒᵖ)` and `b : Tm(Γ, A)` of the discrete model, is
  `homAt a b` of the category model, for the same terms seen in the category model along
  `forgetComprehensionMap` (`homDiscAt_eq`). It is stable under substitution (`pull_homDiscAt`).

Both hold by `rfl`: forgetting the discreteness preserves the Hom-types strictly.

**Hom-Disc** (`eq_of_homDiscAt`): two terms `a b : Tm(Γ, A)` of a discrete type with a term of
`homDiscAt a b` are equal. The Hom-type of the paper takes `a` as a term of `Aᵒᵖ`, which is `A` by
op-Disc. This needs uniqueness of empty types (`EmptyUnique`, in `Logic/EmptyUnique`), a hypothesis
of the theorem, through which `a` is transported to a term of `Aᵒᵖ` (`Tm.toOp`). At each `γ`, the
value of the term of the Hom-type is a morphism from the value of `a` to that of `b` in the
discrete category `A γ`, so these values are equal; the sections of `a` and `b` then agree on
morphisms too, since the morphisms of the fibres are unique (`fiber_heq_of_isDiscrete`). The
values are compared up to the transports and to the first components of the sections, which are
`γ` only propositionally.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- **The Hom-type of a discrete type**, in context `Γ ▹ b : A ▹ a : Aᵒᵖ` of the discrete model:
`Hom[A]` of the category model. -/
def homDisc (A : IDisc.{u, u}.Ty Γ) : IDisc.{u, u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) :=
  Hom[A.toFunctor]

/-- **The Hom-type of two terms of a discrete type**: that of the category model, for the terms
seen in it. -/
def homDiscAt {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) : IDisc.{u, u}.Ty Γ :=
  homAt (A := forgetComprehensionMap.toPre.obj A) (forgetComprehensionMap.tmEquiv a)
    (forgetComprehensionMap.tmEquiv b)

/-- **Forgetting the discreteness preserves the Hom-types**, by `rfl`. -/
theorem homDisc_eq (A : IDisc.{u, u}.Ty Γ) :
    homDisc A = Hom[forgetComprehensionMap.toPre.obj A] :=
  rfl

/-- **Forgetting the discreteness preserves the Hom-types of two terms**, by `rfl`. -/
theorem homDiscAt_eq {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) :
    homDiscAt a b = homAt (A := forgetComprehensionMap.toPre.obj A)
      (forgetComprehensionMap.tmEquiv a) (forgetComprehensionMap.tmEquiv b) :=
  rfl

/-- **The Hom-type of two terms of a discrete type is stable under substitution.** -/
theorem pull_homDiscAt {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ))
    (b : Tm(Γ, A)) : (homDiscAt a b)⦃σ⦄ = homDiscAt (A := A⦃σ⦄) a⦃σ⦄ b⦃σ⦄ :=
  pull_homAt σ _ _

/-- A term of a discrete type `A` as a term of `Aᵒᵖ`, if empty types are unique (op-Disc). -/
def Tm.toOp (hE : EmptyUnique.{u}) {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, A)) : Tm(Γ, Aᵒᵖ) :=
  a.castTy (op_eq_self hE A).symm

/-- The values of a transported term of the category model are those of the term. -/
theorem castTy_sec_obj_snd {A B : ICatLax.{u, u}.Ty Γ} (h : A = B) (t : Tm(Γ, A)) (γ : Γ) :
    ((t.castTy h).sec.toFunctor.obj γ).2 ≍ (t.sec.toFunctor.obj γ).2 := by
  subst h
  rfl

/-- The values of a transported term of the discrete model are those of the term. -/
theorem castTy_sec_obj_snd_disc {A B : IDisc.{u, u}.Ty Γ} (h : A = B) (t : Tm(Γ, A)) (γ : Γ) :
    ((t.castTy h).sec.toFunctor.obj γ).2 ≍ (t.sec.toFunctor.obj γ).2 := by
  subst h
  rfl

/-- The fibre components of morphisms of the context extension by a discrete type are unique: they
are morphisms of discrete categories. -/
theorem fiber_heq_of_isDiscrete {A : IDisc.{u, u}.Ty Γ} {p p' q q' : (∫ A.toFunctor).Total}
    (hp : p = p') (hq : q = q') {F : p ⟶ q} {G : p' ⟶ q'} (hb : F.base ≍ G.base) :
    F.fiber ≍ G.fiber := by
  subst hp hq
  obtain ⟨g, φ⟩ := F
  obtain ⟨g', φ'⟩ := G
  obtain rfl : g = g' := eq_of_heq hb
  exact heq_of_eq (@Subsingleton.elim _ ((A.isDiscrete q.1).subsingleton _ _) φ φ')

/-- **Hom-Disc**: if empty types are unique, terms `a b` of a discrete type with a term of the
Hom-type from `a` to `b` are equal. -/
theorem eq_of_homDiscAt (hE : EmptyUnique.{u}) {A : IDisc.{u, u}.Ty Γ} (a b : Tm(Γ, A))
    (f : Tm(Γ, homDiscAt (Tm.toOp hE a) b)) : a = b := by
  -- The first components of the values of a term are the points of `Γ`.
  have hfst : ∀ {B : IDisc.{u, u}.Ty Γ} (t : Tm(Γ, B)) (γ : Γ), (t.sec.toFunctor.obj γ).1 = γ :=
    fun t γ => Functor.congr_obj (congrArg Cat.Hom.toFunctor t.sec_proj) γ
  have hobj : ∀ γ, a.sec.toFunctor.obj γ = b.sec.toFunctor.obj γ := by
    intro γ
    -- The value of `f` at `γ` is a morphism from the value of `a₃`, the transport of `a`, to that
    -- of `b`, over the first component `F.1` of the value of `f`.
    let a₃ := (forgetComprehensionMap.tmEquiv (Tm.toOp hE a)).castTy
      (pull_sec_op_weak (A := A.toFunctor) (forgetComprehensionMap.tmEquiv b)).symm
    let F := f.sec.toFunctor.obj γ
    have hF : F.1 = γ := Functor.congr_obj (congrArg Cat.Hom.toFunctor f.sec_proj) γ
    have hδ : (a₃.sec.toFunctor.obj F.1).1 = γ :=
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor a₃.sec_proj) F.1).trans hF
    have hxy : (a₃.sec.toFunctor.obj F.1).2 =
        (b.sec.toFunctor.obj (a₃.sec.toFunctor.obj F.1).1).2 :=
      (A.isDiscrete _).eq_of_hom F.2
    refine Sigma.ext ((hfst a γ).trans (hfst b γ).symm) ?_
    refine ((congr_arg_heq (fun γ' => (a.sec.toFunctor.obj γ').2) hF).symm.trans ?_).trans
      (congr_arg_heq (fun γ' => (b.sec.toFunctor.obj γ').2) hδ)
    exact (castTy_sec_obj_snd_disc _ a F.1).symm.trans
      ((castTy_sec_obj_snd _ (forgetComprehensionMap.tmEquiv (Tm.toOp hE a)) F.1).symm.trans
        (heq_of_eq hxy))
  have ha := congrArg Cat.Hom.toFunctor a.sec_proj
  have hb := congrArg Cat.Hom.toFunctor b.sec_proj
  have hbase : ∀ {γ γ' : Γ} (g : γ ⟶ γ'),
      (a.sec.toFunctor.map g).base ≍ (b.sec.toFunctor.map g).base :=
    fun g => (Functor.hcongr_hom ha g).trans (Functor.hcongr_hom hb g).symm
  exact Tm.ext (Cat.Hom.ext (Functor.hext hobj fun γ γ' g =>
    Total.Hom.hext (hobj γ) (hobj γ') (hbase g)
      (fiber_heq_of_isDiscrete (A := A) (hobj γ) (hobj γ') (hbase g))))

end ComprehensionCategory.OverCat
