import ComprehensionCategory.Model.OverCat.Shared.HomIntro

/-!
# Natural transformations as terms of twisted Hom-types

The paper's Proposition `internal-nat-hom`: for two terms `f g : Tm(Γ, B)` of a type `B` of the
category model, the terms of the twisted Hom-type

```
  Γ ⊢ Hom_B(f̄, g) type_d
```

are the natural transformations from `f` to `g`, seen as sections of `∫ B`: the morphisms of the
category of sections `Section.category`, the vertical natural transformations (`natEquiv`).

`Hom_B(f̄, g)` is the twist of the Hom-type `Hom[B]`, a type of the displayed model in context
`Γ ▹ b : B ▹ a : B` (`Shared/HomIntro`), substituted along the pairing of `g` (for `b`) and `f`
(for `a`). As for the twisted Hom-type `twistedHom` of Hom-Intro, it is the straightening of a
displayed category over `Γ` (`twistedHomAtDisp`), the reindexing of the twist `twistDisp` along
this pairing (`twistedHomAt_eq`):

* its objects over `γ` are the morphisms `f γ ⟶ g γ` of `B γ`;
* its morphisms over `k : γ ⟶ γ'` from `e` to `e'` are the proofs of `B k e ≫ g k = f k ≫ e'`,
  the naturality squares (`prop:twist-hom` of the paper).

So a section of it is a family of morphisms `f γ ⟶ g γ` with naturality squares, a vertical
natural transformation between the sections of `f` and `g` (`natSectionEquiv`), and the terms of
`Hom_B(f̄, g)` are these sections (`DisplayedModel.Tm.sectionEquiv`).

The pairing is given by its values on the sections `F` and `G` of `f` and `g`
(`pairSec : γ ↦ ((γ, G γ), F γ)`), so that these descriptions hold by `rfl`. It is the extension
`consSec g.sec f` of the comprehension structure only propositionally (`pairSec_eq`): the functor
laws of a section are not definitional, so the rule for `Functor.map_id` rewrites
`(pairSec F G).map (𝟙 γ)` to an identity that the values `G.map (𝟙 γ)` do not reduce to. For the
same reason, the morphisms of a section of `twistedHomAtDisp` along `k` are given by a definition
over a variable `k` (`natHomMap`), never instantiated at `𝟙 γ` before the kernel checks it.

The twisted Hom-type `twistedHom A` of Hom-Intro is the instance of `Hom_B(f̄, g)` at the variable
of `A` twice, by `rfl` (`twistedHom_eq_twistedHomAt`).

**Stability under substitution**: `Hom_B(f̄, g)⦃σ⦄ = Hom_{B⦃σ⦄}(f⦃σ⦄‾, g⦃σ⦄)`
(`twistedHomAt_pull`), since the reindexing of `twistedHomAtDisp F G` along `σ` is that of the
reindexed sections, by `rfl`, and the section of `f⦃σ⦄` is the reindexing of that of `f`
(`CatModel.Tm.toSection_pull`, `OverCat/Cat/Term`). The bijection is natural in `Γ`
(`natEquiv_pull`): it sends the substituted term to the reindexing `Section.Hom.pull σ` of the
natural transformation.

**The paper's statement** (`natHomEquiv`): for `F G : A ⥤ B`, the terms of `Hom_B(F̄a, Ga)` in
context `a : A` are the natural transformations `F ⟶ G`. Here `B` is the constant type
`constTy A B`, in the context `A` itself rather than `⋆ ▹ A`, whose terms are the functors `A ⥤ B`
(`Tm.ofConst`), and the vertical natural transformations between their sections are the natural
transformations between the functors (`constSectionHomEquiv`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}} {B : ICatLax.{u, u}.Ty Γ}

/-! ## The twisted Hom-type of two terms -/

/-- The pairing `Γ ⟶ Γ ▹ b : B ▹ a : B` of two sections `F` and `G` of `∫ B`,
`γ ↦ ((γ, G γ), F γ)`, given by its values: `G` is the first variable, `b`, and `F` the second,
`a`. -/
def pairSec (F G : (∫ B).Section) : Γ ⟶ Γ ▹ B ▹ B⦃𝐩 B⦄ :=
  (show (Γ : Type u) ⥤ (Γ ▹ B ▹ B⦃𝐩 B⦄ : Cat.{u, u}) from
    { obj γ := ⟨⟨γ, G.obj γ⟩, F.obj γ⟩
      map k := ⟨⟨k, G.map k⟩, F.map k⟩
      map_id γ := Total.Hom.ext' (Total.Hom.ext' rfl (heq_of_eq (G.map_id γ)))
        (heq_of_eq (F.map_id γ))
      map_comp k k' := Total.Hom.ext' (Total.Hom.ext' rfl (heq_of_eq (G.map_comp k k')))
        (heq_of_eq (F.map_comp k k')) }).toCatHom

/-- The type `B⦃𝐩 B⦄` of the second variable, substituted along the section of a term `g` of `B`,
is `B`, since `g.sec ≫ 𝐩 B = 𝟙`. -/
theorem pull_sec_weak (g : Tm(Γ, B)) : B⦃𝐩 B⦄⦃g.sec⦄ = B :=
  congrArg (fun σ => B⦃σ⦄) g.sec_proj

/-- The pairing of the sections of two terms of sections is the extension of the comprehension
structure, componentwise by `rfl`. -/
theorem pairSec_ofSection (F G : (∫ B).Section) :
    pairSec F G = consSec (Tm.ofSection G).sec
      ((Tm.ofSection F : Tm(Γ, B)).castTy (pull_sec_weak (Tm.ofSection G)).symm) :=
  Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

/-- **The pairing of the sections of `f` and `g` is the extension `consSec g.sec f`** of the
comprehension structure. -/
theorem pairSec_eq (f g : Tm(Γ, B)) :
    pairSec (Tm.toSection f) (Tm.toSection g) =
      consSec g.sec (f.castTy (pull_sec_weak g).symm) := by
  obtain ⟨F, rfl⟩ : ∃ F, Tm.ofSection F = f := ⟨_, Tm.sectionEquiv.left_inv f⟩
  obtain ⟨G, rfl⟩ : ∃ G, Tm.ofSection G = g := ⟨_, Tm.sectionEquiv.left_inv g⟩
  rw [Tm.toSection_ofSection, Tm.toSection_ofSection]
  exact pairSec_ofSection F G

/-- The displayed category of the twisted Hom-type of two sections `F` and `G`, over `Γ`: the twist
of the Hom-type, reindexed along their pairing. Its objects over `γ` are the morphisms
`F γ ⟶ G γ` of `B γ`, and its morphisms over `k` from `e` to `e'` the proofs of
`B k e ≫ G k = F k ≫ e'`. -/
def twistedHomAtDisp (F G : (∫ B).Section) : Displayed.{u, u} Γ :=
  DisplayedCat.pull (pairSec F G) (twistDisp (homFunctor B))

/-- **The twisted Hom-type `Γ ⊢ Hom_B(f̄, g)`** of two terms `f g : Tm(Γ, B)`, a type of the
displayed model. -/
def twistedHomAt (f g : Tm(Γ, B)) : Straightening.IProf.{u, u, u}.Ty Γ :=
  Straightening.straightenObj (twistedHomAtDisp (Tm.toSection f) (Tm.toSection g))

/-- **The twisted Hom-type of two terms is derivable**: it is the twist of the Hom-type of `B`,
substituted along the pairing of `g` and `f`. -/
theorem twistedHomAt_eq (f g : Tm(Γ, B)) :
    twistedHomAt f g = (twist (homFunctor B))⦃consSec g.sec (f.castTy (pull_sec_weak g).symm)⦄ := by
  kernel_exact (DisplayedModel.straightenObj_pull (pairSec (Tm.toSection f) (Tm.toSection g))
    (twistDisp (homFunctor B))).symm.trans
    (congrArg (fun σ => (twist (homFunctor B))⦃σ⦄) (pairSec_eq f g))

/-- **The twisted Hom-type of Hom-Intro is the twisted Hom-type of the variable with itself**,
`Γ ▹ a : A ⊢ Hom_A(ā, a)`, by `rfl`. -/
theorem twistedHom_eq_twistedHomAt (A : ICatLax.{u, u}.Ty Γ) :
    twistedHom A = twistedHomAt (var A) (var A) := by
  kernel_rfl'

/-! ## Its terms are the natural transformations -/

variable {F G : (∫ B).Section}

/-- The morphisms of `twistedHomAtDisp F G` are unique: they are proofs of equations. -/
theorem twistedHomAtDisp_hom_ext {γ γ' : Γ} {k : γ ⟶ γ'} {x : (twistedHomAtDisp F G).Ob γ}
    {y : (twistedHomAtDisp F G).Ob γ'} (φ ψ : (twistedHomAtDisp F G).Hom k x y) : φ = ψ :=
  Subsingleton.elim (α := ULift (PLift _)) φ ψ

/-- The naturality square of `α` at `k`, as a morphism of `twistedHomAtDisp F G` over `k`. It is
stated for a variable `k`, so that the kernel checks its type once: instantiated at `𝟙 γ`, the rules
rewrite the expected type and the type of the square differently. -/
def natHomMap (α : F ⟶ G) {γ γ' : Γ} (k : γ ⟶ γ') :
    (twistedHomAtDisp F G).Hom k (α.app γ) (α.app γ') :=
  ⟨⟨(α.naturality k).symm⟩⟩

/-- The vertical natural transformation of a section of `twistedHomAtDisp F G`: its objects, with
the naturality squares of its morphisms. -/
def toNatHom (S : (twistedHomAtDisp F G).Section) : F ⟶ G :=
  ⟨fun γ => S.obj γ, fun k => (S.map k).down.down.symm⟩

/-- The section of `twistedHomAtDisp F G` of a vertical natural transformation: its components,
with its naturality squares. -/
def ofNatHom (α : F ⟶ G) : (twistedHomAtDisp F G).Section where
  obj γ := α.app γ
  map k := natHomMap α k
  map_id _ := twistedHomAtDisp_hom_ext _ _
  map_comp _ _ := twistedHomAtDisp_hom_ext _ _

/-- **The sections of `twistedHomAtDisp F G` are the vertical natural transformations from `F` to
`G`.** -/
def natSectionEquiv : (twistedHomAtDisp F G).Section ≃ (F ⟶ G) where
  toFun := toNatHom
  invFun := ofNatHom
  left_inv _ := Section.ext (fun _ => rfl) fun _ => heq_of_eq (twistedHomAtDisp_hom_ext _ _)
  right_inv _ := Section.Hom.ext fun _ => rfl

/-- **The terms of `Hom_B(f̄, g)` are the natural transformations from `f` to `g`** (paper,
`internal-nat-hom`): the vertical natural transformations between their sections. -/
def natEquiv (f g : Tm(Γ, B)) : Tm(Γ, twistedHomAt f g) ≃ (Tm.toSection f ⟶ Tm.toSection g) :=
  DisplayedModel.Tm.sectionEquiv.trans natSectionEquiv

/-! ## Stability under substitution -/

section Pull

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)

/-- The reindexing of `twistedHomAtDisp F G` along `σ` is that of the reindexed sections, by
`rfl`. -/
theorem twistedHomAtDisp_pull (F G : (∫ B).Section) :
    DisplayedCat.pull σ (twistedHomAtDisp F G) =
      twistedHomAtDisp (B := B⦃σ⦄) (F.pull σ) (G.pull σ) := by
  kernel_rfl'

/-- **The twisted Hom-type of two terms is stable under substitution.** -/
theorem twistedHomAt_pull (f g : Tm(Γ, B)) :
    (twistedHomAt f g)⦃σ⦄ = twistedHomAt f⦃σ⦄ g⦃σ⦄ := by
  kernel_exact (congrArg Straightening.straightenObj
    (twistedHomAtDisp_pull σ (Tm.toSection f) (Tm.toSection g))).trans
    (congrArg₂ (fun F G => Straightening.straightenObj (twistedHomAtDisp (B := B⦃σ⦄) F G))
      (Tm.toSection_pull σ f).symm (Tm.toSection_pull σ g).symm)

/-- `natSectionEquiv` sends heterogeneously equal terms of equal types to heterogeneously equal
natural transformations. -/
theorem natSectionEquiv_hcongr {F F' G G' : (∫ B).Section} (hF : F = F') (hG : G = G')
    {X : Straightening.IProf.Tm (Γ := Γ) (Straightening.straightenObj (twistedHomAtDisp F G))}
    {Y : Straightening.IProf.Tm (Γ := Γ) (Straightening.straightenObj (twistedHomAtDisp F' G'))}
    (h : X ≍ Y) :
    natSectionEquiv (DisplayedModel.Tm.toSection (D := twistedHomAtDisp F G) X) ≍
      natSectionEquiv (DisplayedModel.Tm.toSection (D := twistedHomAtDisp F' G') Y) := by
  subst hF hG
  cases h
  rfl

/-- The natural transformation of the reindexing of a section is the reindexing of its natural
transformation. -/
theorem toNatHom_pull (S : (twistedHomAtDisp F G).Section) :
    toNatHom (B := B⦃σ⦄) (F := F.pull σ) (G := G.pull σ) (S.pull σ) =
      Section.Hom.pull σ (toNatHom S) :=
  Section.Hom.ext fun _ => rfl

/-- **The bijection is natural in `Γ`**: the natural transformation of a substituted term is the
reindexing of that of the term. -/
theorem natEquiv_pull (f g : Tm(Γ, B)) (t : Tm(Γ, twistedHomAt f g)) :
    natEquiv f⦃σ⦄ g⦃σ⦄ (t⦃σ⦄.castTy (twistedHomAt_pull σ f g)) ≍
      Section.Hom.pull σ (natEquiv f g t) := by
  have ht : t⦃σ⦄ ≍ DisplayedModel.Tm.ofSection ((DisplayedModel.Tm.toSection t).pull σ) :=
    (heq_of_eq (congrArg (·⦃σ⦄) (DisplayedModel.Tm.sectionEquiv.left_inv t).symm)).trans
      (DisplayedModel.Tm.ofSection_pull σ _)
  refine (natSectionEquiv_hcongr (Tm.toSection_pull σ f) (Tm.toSection_pull σ g)
    ((Tm.castTy_heq _ _).trans ht)).trans ?_
  refine heq_of_eq ((congrArg natSectionEquiv
    (DisplayedModel.Tm.sectionEquiv.right_inv _)).trans ?_)
  exact toNatHom_pull σ _

end Pull

/-! ## Functors into a category -/

/-- The vertical natural transformations between the sections of the terms of two functors
`F G : A ⥤ K`, as terms of the constant type at `K`, are the natural transformations `F ⟶ G`. -/
def constSectionHomEquiv {A K : Cat.{u, u}} (F G : A ⥤ K) :
    (Tm.toSection (Tm.ofConst F) ⟶ Tm.toSection (Tm.ofConst G)) ≃ (F ⟶ G) where
  toFun α := { app a := α.app a, naturality _ _ k := α.naturality k }
  invFun θ := { app a := θ.app a, naturality k := θ.naturality k }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The paper's Proposition `internal-nat-hom`**: for functors `F G : A ⥤ K`, the terms of
`a : A ⊢ Hom_K(F̄a, Ga)` are the natural transformations `F ⟶ G`. The type `K` is the constant type
at `K` in the context `A`, whose terms are the functors `A ⥤ K`. -/
def natHomEquiv {A K : Cat.{u, u}} (F G : A ⥤ K) :
    Tm(A, twistedHomAt (B := constTy A K) (Tm.ofConst F) (Tm.ofConst G)) ≃ (F ⟶ G) :=
  (natEquiv _ _).trans (constSectionHomEquiv F G)

end ComprehensionCategory.OverCat
