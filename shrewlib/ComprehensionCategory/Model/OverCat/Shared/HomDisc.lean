import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat
import Tactic.KernelTactic

/-!
# Hom-types of discrete types

The Hom-types of a type `A` of the discrete model are defined in the discrete model, and are those
of `A` in the category model:

* `homDisc A`, in context `Γ ▹ b : A ▹ a : Aᵒᵖ` of the discrete model, sends `((γ, b), a)` to the
  discrete category on the morphisms `a ⟶ b` of `A γ`, like `Hom[A]`. A morphism `((f, ψ), φ)` of
  the context acts on them by the equalities `a' = A f a = A f b = b'` that the morphisms of the
  discrete categories give (`homDiscAct`), rather than by composing `φ ≫ A f h ≫ ψ` as `Hom[A]`
  does (`homAct`).
* `homDiscAt a b`, for terms `a : Tm(Γ, Aᵒᵖ)` and `b : Tm(Γ, A)` of the discrete model, is the
  substitution of `homDisc A` along their pairing, as `homAt` is that of `Hom[A]`.

**Forgetting the discreteness preserves the Hom-types strictly** (`homDisc_eq`, `homDiscAt_eq`):
`homDisc A` is `Hom[A]` of the category model, since the two actions on morphisms agree, the
morphisms of the discrete categories `A γ'` being unique. The contexts and opposite types of the
discrete model are those of the category model, by `rfl`, and the pairings of the terms have the
same sections, so `homDiscAt a b` is `homAt` for `a` and `b` seen in the category model. Its
stability under substitution (`pull_homDiscAt`) follows from that of `homAt`.

**Hom-Disc** (`eq_of_homDiscAt`): two terms `a b : Tm(Γ, A)` of a discrete type with a term of
`homDiscAt a b` are equal. The Hom-type of the paper takes `a` as a term of `Aᵒᵖ`, which is `A` by
op-Disc. This needs uniqueness of empty types (`EmptyUnique`, in `Logic/EmptyUnique`), a hypothesis
of the theorem, through which `a` is transported to a term of `Aᵒᵖ` (`Tm.toOp`). Through
`homDiscAt_eq`, the term of the Hom-type is one of `homAt` in the category model
(`eq_of_homAt_disc`). At each `γ`, its value is a morphism from the value of `a` to that of `b` in
the discrete category `A γ`, so these values are equal; the sections of `a` and `b` then agree on
morphisms too, since the morphisms of the fibres are unique (`fiber_heq_of_isDiscrete`). The
values are compared up to the transports and to the first components of the sections, which are
`γ` only propositionally.

**Reflexivity**: conversely, if the values of `a` and `b` agree, `homDiscAt a b` has a term
(`homDiscAtRefl`), whose value at `γ` is the `eqToHom` of their equality, and whose transports are
unique, the morphisms of discrete categories. In particular, if empty types are unique, a term `t`
of a discrete type gives a term of `homDiscAt (Tm.toOp hE t) t` (`homDiscRefl`), the reflexivity
`Refl_t` of the paper, and the transport `Tm.toOp hE` commutes with substitution (`toOp_pull`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The action of a morphism `((f, ψ), φ)` of the context on the morphisms of a discrete type `A`:
a morphism `a ⟶ b` of `A γ` goes to the morphism `a' ⟶ b'` of `A γ'` induced by the equalities
`a' = A f a = A f b = b'`, which the morphisms `φ`, `h` and `ψ` of discrete categories give. -/
def homDiscAct (A : IDisc.{u, u}.Ty Γ) {γ γ' : Γ} (f : γ ⟶ γ') {a b : A.toFunctor.obj γ}
    {a' b' : A.toFunctor.obj γ'}
    (φ : @Quiver.Hom ((A.toFunctor ⋙ opFunctor').obj γ') _ ((A.toFunctor.map f).toFunctor.obj a) a')
    (ψ : (A.toFunctor.map f).toFunctor.obj b ⟶ b') (h : a ⟶ b) : a' ⟶ b' :=
  eqToHom ((@IsDiscrete.eq_of_hom _ _ (A.isDiscrete γ') _ _
      (φ : @Quiver.Hom (A.toFunctor.obj γ') _ a' ((A.toFunctor.map f).toFunctor.obj a))).trans
    ((congrArg (A.toFunctor.map f).toFunctor.obj
        (@IsDiscrete.eq_of_hom _ _ (A.isDiscrete γ) _ _ h)).trans
      (@IsDiscrete.eq_of_hom _ _ (A.isDiscrete γ') _ _ ψ)))

/-- Functors between discrete categories `discrete' S` and `discrete' T` are equal if they agree on
objects. -/
theorem catHom_discrete'_ext {S T : Type u} {F G : discrete' S ⟶ discrete' T}
    (h : ∀ s, F.toFunctor.obj s = G.toFunctor.obj s) : F = G :=
  Cat.Hom.ext (CategoryTheory.Functor.ext h fun _ _ _ => discrete'_hom_ext _ _)

/-- **The Hom-type of a discrete type**, in context `Γ ▹ b : A ▹ a : Aᵒᵖ` of the discrete model: at
`((γ, b), a)`, the discrete category on the morphisms `a ⟶ b` of `A γ`, which a morphism of the
context acts on by the equalities that the morphisms of the discrete categories give
(`homDiscAct`). -/
def homDisc (A : IDisc.{u, u}.Ty Γ) : IDisc.{u, u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) where
  toFunctor :=
    { obj X := discrete' (@Quiver.Hom (A.toFunctor.obj X.1.1) _ X.2 X.1.2)
      map g := discreteMap' (homDiscAct A g.base.base g.fiber g.base.fiber)
      map_id X := catHom_discrete'_ext fun _ =>
        @Subsingleton.elim _ ((A.isDiscrete X.1.1).subsingleton _ _) _ _
      map_comp {_ _ Z} _ _ := catHom_discrete'_ext fun _ =>
        @Subsingleton.elim _ ((A.isDiscrete Z.1.1).subsingleton _ _) _ _ }
  isDiscrete _ := isDiscrete_discrete' _

/-- **Forgetting the discreteness preserves the Hom-types**: the Hom-type of a discrete type is that
of the category model. They have the same values, and their actions on morphisms agree since the
morphisms of discrete categories are unique. -/
theorem homDisc_eq (A : IDisc.{u, u}.Ty Γ) :
    homDisc A = Hom[forgetComprehensionMap.toPre.obj A] :=
  IDiscOb.ext (Functor.hext (fun _ => rfl) fun _ Y _ => heq_of_eq (catHom_discrete'_ext fun _ =>
    @Subsingleton.elim _ ((A.isDiscrete Y.1.1).subsingleton _ _) _ _))

/-- The type `(A⦃𝐩 A⦄)ᵒᵖ` of the second variable of the Hom-type of a discrete type, substituted
along the section of a term `b` of `A`, is `Aᵒᵖ`, since `b.sec ≫ 𝐩 A = 𝟙`. -/
theorem pull_sec_op_weak_disc {A : IDisc.{u, u}.Ty Γ} (b : Tm(Γ, A)) :
    (A⦃𝐩 A⦄)ᵒᵖ⦃b.sec⦄ = Aᵒᵖ :=
  congrArg (fun σ => (A⦃σ⦄)ᵒᵖ) b.sec_proj

/-- **The Hom-type of two terms of a discrete type**, `homDisc A` substituted along the pairing of
the terms. -/
def homDiscAt {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) : IDisc.{u, u}.Ty Γ :=
  (homDisc A)⦃consSec b.sec (a.castTy (pull_sec_op_weak_disc b).symm)⦄

/-- **Forgetting the discreteness preserves the Hom-types of two terms**: the Hom-type of two terms
of a discrete type is that of the category model, for the terms seen in it. -/
theorem homDiscAt_eq {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) :
    homDiscAt a b = homAt (A := forgetComprehensionMap.toPre.obj A)
      (forgetComprehensionMap.tmEquiv a) (forgetComprehensionMap.tmEquiv b) := by
  -- The two transports of `a` have the same section, that of `a`.
  have hsec := eq_of_heq ((Tm.castTy_sec_heq (pull_sec_op_weak_disc b).symm a).trans
    (Tm.castTy_sec_heq (pull_sec_op_weak (forgetComprehensionMap.tmEquiv b)).symm
      (forgetComprehensionMap.tmEquiv a)).symm)
  kernel_exact (congrArg (fun H => H⦃consSec b.sec (a.castTy (pull_sec_op_weak_disc b).symm)⦄)
    (homDisc_eq A)).trans
    (congrArg (fun σ => Hom[forgetComprehensionMap.toPre.obj A]⦃σ ≫ 𝐪(b.sec, (A⦃𝐩 A⦄)ᵒᵖ)⦄) hsec)

/-- **The Hom-type of two terms of a discrete type is stable under substitution.** -/
theorem pull_homDiscAt {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : IDisc.{u, u}.Ty Γ} (a : Tm(Γ, Aᵒᵖ))
    (b : Tm(Γ, A)) : (homDiscAt a b)⦃σ⦄ = homDiscAt (A := A⦃σ⦄) a⦃σ⦄ b⦃σ⦄ := by
  kernel_exact (congrArg (·⦃σ⦄) (homDiscAt_eq a b)).trans
    ((pull_homAt σ (forgetComprehensionMap.tmEquiv a) (forgetComprehensionMap.tmEquiv b)).trans
      (homDiscAt_eq (A := A⦃σ⦄) a⦃σ⦄ b⦃σ⦄).symm)

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

/-- Hom-Disc, with the Hom-type of the category model: the term `f` of the Hom-type is a term of
`homAt` for `a` and `b` seen in the category model. -/
theorem eq_of_homAt_disc (hE : EmptyUnique.{u}) {A : IDisc.{u, u}.Ty Γ} (a b : Tm(Γ, A))
    (f : Tm(Γ, homAt (A := forgetComprehensionMap.toPre.obj A)
      (forgetComprehensionMap.tmEquiv (Tm.toOp hE a)) (forgetComprehensionMap.tmEquiv b))) :
    a = b := by
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

/-- **Hom-Disc**: if empty types are unique, terms `a b` of a discrete type with a term of the
Hom-type from `a` to `b` are equal. -/
theorem eq_of_homDiscAt (hE : EmptyUnique.{u}) {A : IDisc.{u, u}.Ty Γ} (a b : Tm(Γ, A))
    (f : Tm(Γ, homDiscAt (Tm.toOp hE a) b)) : a = b :=
  eq_of_homAt_disc hE a b (f.castTy (homDiscAt_eq _ b))

/-! ## Reflexivity -/

section Refl

variable {A : IDisc.{u, u}.Ty Γ}

/-- The point `((γ', b), a)` of `Γ ▹ b : A ▹ a : Aᵒᵖ` at which `homDiscAt a b` is evaluated at
`γ`. -/
abbrev homDiscPt (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) (γ : Γ) :=
  (consSec b.sec (a.castTy (pull_sec_op_weak_disc b).symm)).toFunctor.obj γ

/-- If the values of `a` and `b` agree, the two objects of `A` at the point `homDiscPt a b γ` are
equal: the value of `a` and that of `b`, at a first component equal to `γ`. -/
theorem homDiscPt_eq (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A))
    (hab : ∀ γ, (a.sec.toFunctor.obj γ).2 ≍ (b.sec.toFunctor.obj γ).2) (γ : Γ) :
    @Eq (A.toFunctor.obj (homDiscPt a b γ).1.1) (homDiscPt a b γ).2 (homDiscPt a b γ).1.2 := by
  let a' := a.castTy (pull_sec_op_weak_disc b).symm
  have hγ : (a'.sec.toFunctor.obj γ).1 = γ :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor a'.sec_proj) γ
  exact eq_of_heq ((castTy_sec_obj_snd_disc _ a γ).trans ((hab γ).trans
    (congr_arg_heq (fun γ' => (b.sec.toFunctor.obj γ').2) hγ.symm)))

/-- The values of `homDiscAt a b` are subsingletons: morphisms of discrete categories. -/
theorem homDiscAt_obj_subsingleton (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A)) (γ : Γ)
    (x y : (homDiscAt a b).toFunctor.obj γ) : x = y :=
  @Subsingleton.elim _ ((A.isDiscrete (homDiscPt a b γ).1.1).subsingleton _ _) x y

/-- The transport along `k` of the reflexivity, a proof of an equality of morphisms of a discrete
category. It is stated for a variable `k`, so that the kernel checks its type once. -/
def homDiscAtReflMap (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A))
    (hab : ∀ γ, (a.sec.toFunctor.obj γ).2 ≍ (b.sec.toFunctor.obj γ).2) {γ γ' : Γ} (k : γ ⟶ γ') :
    (∫ (forgetComprehensionMap.toPre.obj (homDiscAt a b))).Hom k
      (eqToHom (homDiscPt_eq a b hab γ)) (eqToHom (homDiscPt_eq a b hab γ')) :=
  ⟨⟨homDiscAt_obj_subsingleton a b γ' _ _⟩⟩

/-- **The reflexivity of two terms with the same values**, a term of the Hom-type from one to the
other: at `γ`, the `eqToHom` of the equality of their values. -/
def homDiscAtRefl (a : Tm(Γ, Aᵒᵖ)) (b : Tm(Γ, A))
    (hab : ∀ γ, (a.sec.toFunctor.obj γ).2 ≍ (b.sec.toFunctor.obj γ).2) : Tm(Γ, homDiscAt a b) :=
  forgetComprehensionMap.tmEquiv.symm (CatModel.Tm.ofSection
    { obj γ := eqToHom (homDiscPt_eq a b hab γ)
      map k := homDiscAtReflMap a b hab k
      map_id _ := discrete'_hom_ext _ _
      map_comp _ _ := discrete'_hom_ext _ _ })

/-- **Hom-Refl for discrete types**: if empty types are unique, a term `t` of a discrete type gives
the term `Refl_t` of the Hom-type from `t` to itself. -/
def homDiscRefl (hE : EmptyUnique.{u}) (t : Tm(Γ, A)) : Tm(Γ, homDiscAt (Tm.toOp hE t) t) :=
  homDiscAtRefl (Tm.toOp hE t) t fun γ => castTy_sec_obj_snd_disc _ t γ

/-- The transport `Tm.toOp hE` commutes with substitution. -/
theorem toOp_pull (hE : EmptyUnique.{u}) {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ, A)) :
    (Tm.toOp hE t)⦃σ⦄ = Tm.toOp hE t⦃σ⦄ := by
  kernel_exact eq_of_heq ((Tm.pull_hcongr σ (op_eq_self hE A)
    (Tm.castTy_heq (op_eq_self hE A).symm t)).trans
    (Tm.castTy_heq (op_eq_self hE (A⦃σ⦄)).symm t⦃σ⦄).symm)

end Refl

end ComprehensionCategory.OverCat
