import ComprehensionCategory.Model.OverCat.Shared.HomIntro
import Displayed.Opfibration.RAlgebra

/-!
# Hom-elimination

For a type `A` of the category model in context `Γ` and a term `a₀` of `A`, the category model
validates the elimination and computation rules of the Hom-types based at `a₀` (paper,
`prop:hom-elim`):

```
     Γ ⊢ A type      Γ ⊢ a₀ : A
     Γ ▹ b : A ▹ f : Homₐ(ā₀, b) ⊢ D type
     Γ ⊢ d : D[a₀/b, refl_a₀/f]
  ------------------------------------------- Hom-Elim
     Γ ▹ b : A ▹ f : Homₐ(ā₀, b) ⊢ j(f, d) : D

     Γ ⊢ j(refl_a₀, d) ≡ d : D[a₀/b, refl_a₀/f]          Hom-Comp
```

The basepoint is a term `a₀ : Tm(Γ, A)`, as in the paper, and the context and the substitutions
of the rules are those of the internal language, built from the comprehension structures:

* `(a₀⦃𝐩 A⦄).sec : Γ ▹ b : A ⟶ Γ ▹ b : A ▹ a : A` is the substitution `[a₀/a]`, the
  section of `a₀` weakened to `Γ ▹ A`. It is `(γ, b) ↦ (γ, b, a₀ γ)`.
* The type `Γ ▹ b : A ⊢ Homₐ(ā₀, b)` is the twist of the Hom-type
  `Γ ▹ b : A ▹ a : A ⊢ Homₐ(ā, b)` (`Shared/Twist`, `Shared/HomIntro`) substituted along
  it. The context `homElimCtx a₀` that it extends, in the displayed model, is the category
  `a₀/A` of the paper. Its objects are the tuples `(γ, b, f : a₀ γ ⟶ b)`, and its morphisms the
  tuples `(θ, β, e)` with `e` a proof of `A θ f ≫ β = a₀ θ ≫ f'`. Its projections are
  `homElimCod a₀` to `Γ ▹ A`, that of the Hom-type, and `homElimRet a₀ = homElimCod a₀ ≫ 𝐩 A` to
  `Γ`.
* The substitution `[a₀/b, refl_a₀/f]` is `r = homElimR a₀ = consSec a₀.sec (reflAt a₀)`, the
  extension of the section of `a₀` by the term `Γ ⊢ refl_a₀ : Homₐ(ā₀, a₀)` of Hom-Intro
  (`reflAt`, `Shared/HomIntro`), whose type is the Hom-type above substituted along the section of
  `a₀`. It is `γ ↦ (γ, a₀ γ, 𝟙)`. So the premise `d : D[a₀/b, refl_a₀/f]` is a term of
  `D⦃homElimR a₀⦄`.

These compute by the rules of `OverCat/Cat/TermRules`: the first component of `a₀.sec γ` is `γ`
(`Tm.sec_obj_fst`, `Tm.sec_map_base`), and the section of a substituted term is that of the
reindexed section (`Tm.pull_sec`). So the values `a₀ γ : A γ`, those of the section
`Tm.toSection a₀`, need no transport, the objects and morphisms of `homElimCtx a₀` are the tuples
above by `rfl`, and `homElimCtx a₀⦃σ⦄` is the category of the reindexed section.

The Hom-type based at `a₀` is stable under substitution: along `𝐪(σ, A)`, it is that of `A⦃σ⦄`
based at `a₀⦃σ⦄` (`homElimTy_pull`). This holds by `rfl` in the kernel, but it is slow to find out,
and the elaborator times out: they first compare the arguments of the two substitutions, which
differ. It is proved from an equation of substitutions, checked componentwise (`q_sec_weak`), and
is a rule, oriented towards the Hom-type of the substituted term and declared after the
composition of substitutions, with the same head. So the context extended by the substituted
Hom-type is `homElimCtx a₀⦃σ⦄`, and the morphisms `𝐪` of the comprehension structures into
`homElimCtx a₀` have it as domain.

## The proof, through the AWFS

As in the paper, Hom-Elim is the chosen lift of the comma AWFS on `Cat` (`TwoCategory.catAWFS`,
`TwoCategory.AWFS.lift`):

* `r` is a left adjoint right inverse (`homElimLari`), with right adjoint the projection
  `F : homElimCtx a₀ ⟶ Γ`, `(γ, b, f) ↦ γ` (`homElimRet`), identity unit, and counit
  `ε : F ≫ r ⟶ 𝟙` with components `(𝟙, f) : (γ, a₀ γ, 𝟙) ⟶ (γ, b, f)` (`homElimCounit`). So `r` is
  an `L`-coalgebra
  (`Arr.Lari.toLCoalg`). Its naturality is the equation `A θ f ≫ β = a₀ θ ≫ f'` of the morphisms of
  `homElimCtx a₀`, and the triangle identities hold componentwise by `rfl`.
* `D` is a type of the category model, so `∫ D` is a split opfibration, and its projection `𝐩 D`
  an `R`-algebra (`Displayed.ralg`).
* `homElim D d` is the chosen lift of the square `(d ≫ 𝐪(r, D), 𝟙) : r ⟶ 𝐩 D` (`homElimSq`). The
  lower triangle makes it a term of `D`, and the upper one is Hom-Comp
  (`homComp : (homElim D d)⦃homElimR a₀⦄ = d`).

## Stability under substitution

For `σ : Δ ⟶ Γ`, the substitution `σ⁺ : homElimCtx a₀⦃σ⦄ ⟶ homElimCtx a₀`, `(δ, b, f) ↦ (σ δ, b, f)`
(`homElimCtxMap`), is the morphism `𝐪(𝐪(σ, A), Homₐ(ā₀, b))` of the comprehension structures, whose
domain is `homElimCtx a₀⦃σ⦄` by the rule `homElimTy_pull`. It commutes with `r`, with the
projections and with the counits, all by `rfl`. So `(σ, σ⁺)` is a morphism of LARIs
(`homElimLariHom`), hence of `L`-coalgebras, and `𝐪(σ⁺, D)` preserves the chosen lifts, a morphism
of `R`-algebras (`homElimAlgHom`). The square of the substituted premise `d⦃σ⦄`, whose type
`D⦃homElimR a₀⦄⦃σ⦄` is `D⦃σ⁺⦄⦃homElimR a₀⦃σ⦄⦄` by `rfl`, is the reindexing of that of `d`
(`homElimSq_pull`), and by the functoriality of the chosen lifts (`AWFS.coalgHom_comp_lift_eq`) and
the uniqueness of substitutions of terms,

```
  j(f, d)⦃σ⁺⦄ = j(f, d⦃σ⦄)          (homElim_pull)
```

with the motive `D⦃σ⁺⦄`, and no transport.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel TwoCategory

open scoped Displayed

variable {Γ : Cat.{u, u}}

section Elim

variable {A : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, A))

/-! ## The context of Hom-elimination -/

/-- **The context `Γ ▹ b : A ▹ f : Homₐ(ā₀, b)`**, the category `a₀/A` of the paper, extended in the
displayed model by the twist of the Hom-type substituted along `[a₀/a]`. Its objects are the tuples
`((γ, b), f)` with `f : a₀ γ ⟶ b` in `A γ`, and its morphisms `((θ, β), e)` the tuples of
`θ : γ ⟶ γ'`, `β : A θ b ⟶ b'` and a proof `e` of `A θ f ≫ β = a₀ θ ≫ f'`. -/
abbrev homElimCtx : Cat.{u, u} :=
  Γ ▹ A ▹ (twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄

/-- The codomain `homElimCtx a₀ ⟶ Γ ▹ A`, `(γ, b, f) ↦ (γ, b)`: the projection of the Hom-type. -/
def homElimCod : homElimCtx a₀ ⟶ Γ ▹ A :=
  𝐩 ((twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄)

/-- Morphisms of `homElimCtx a₀` with the same base are equal: their components in the Hom-type are
proofs of equations. -/
theorem homElimCtx_hom_ext {p p' : homElimCtx a₀} {k k' : p ⟶ p'} (h : k.base = k'.base) :
    k = k' := by
  obtain ⟨b, ⟨⟨_⟩⟩⟩ := k
  obtain ⟨b', ⟨⟨_⟩⟩⟩ := k'
  dsimp only at h
  subst h
  rfl

/-- **The substitution `r = [a₀/b, refl_a₀/f] : Γ ⟶ homElimCtx a₀`**: the extension of the section
of `a₀` by the term `refl_a₀` of Hom-Intro. It is `γ ↦ (γ, a₀ γ, 𝟙)`. -/
def homElimR : Γ ⟶ homElimCtx a₀ :=
  consSec a₀.sec (reflAt a₀)

/-- **The projection `F : homElimCtx a₀ ⟶ Γ`**, `(γ, b, f) ↦ γ`, the right adjoint of `r`: the
composite of the projections of the comprehension structures. -/
def homElimRet : homElimCtx a₀ ⟶ Γ :=
  homElimCod a₀ ≫ 𝐩 A

/-- `r` followed by the codomain is the section of `a₀`. -/
theorem homElimR_homElimCod : homElimR a₀ ≫ homElimCod a₀ = a₀.sec :=
  consSec_proj a₀.sec (reflAt a₀)

/-- `r ≫ F = 𝟙`. -/
theorem homElimR_homElimRet : homElimR a₀ ≫ homElimRet a₀ = 𝟙 Γ :=
  rfl

/-! ## The counit -/

/-- The component at `p = (γ, b, f)` of the counit, `(𝟙, f) : (γ, a₀ γ, 𝟙) ⟶ p`. Its equation
`A 𝟙 (𝟙 (a₀ γ)) ≫ f = a₀ 𝟙 ≫ f` is the identity law of `a₀`. -/
def homElimCounitApp (p : homElimCtx a₀) : (homElimRet a₀ ≫ homElimR a₀).toFunctor.obj p ⟶ p :=
  ⟨⟨𝟙 p.1.1, p.2⟩, ⟨⟨by
    change _ = (Tm.toSection a₀).map (𝟙 p.1.1) ≫ _
    rw [(Tm.toSection a₀).map_id]
    rfl⟩⟩⟩

/-- The counit is natural: its components commute by the equation `A θ f ≫ β = a₀ θ ≫ f'` of
morphisms of `homElimCtx a₀`. -/
theorem homElimCounitApp_naturality {p p' : homElimCtx a₀} (K : p ⟶ p') :
    (homElimRet a₀ ≫ homElimR a₀).toFunctor.map K ≫ homElimCounitApp a₀ p' =
      homElimCounitApp a₀ p ≫ K :=
  homElimCtx_hom_ext a₀ (Total.Hom.ext' rfl (heq_of_eq K.fiber.down.down.symm))

/-- **The counit `ε : F ≫ r ⟶ 𝟙`**, with components `(𝟙, f) : (γ, a₀ γ, 𝟙) ⟶ (γ, b, f)`. -/
def homElimCounit : homElimRet a₀ ≫ homElimR a₀ ⟶ 𝟙 (homElimCtx a₀) :=
  ⟨{ app := homElimCounitApp a₀, naturality := fun _ _ K => homElimCounitApp_naturality a₀ K }⟩

/-- `r`, as an arrow of `Cat`. -/
abbrev homElimRArr : Arr Cat.{u, u} :=
  ⟨Γ, homElimCtx a₀, homElimR a₀⟩

/-- **`r` is a LARI**, `r ⊣ F` with identity unit and counit `ε`. -/
def homElimLari : (homElimRArr a₀).Lari where
  toRetraction := ⟨homElimRet a₀, homElimR_homElimRet a₀⟩
  counit := homElimCounit a₀
  hom_whiskerLeft_counit := Cat.Hom₂.ext (NatTrans.ext (funext fun _ => homElimCtx_hom_ext a₀ rfl))
  counit_whiskerRight_r := Cat.Hom₂.ext (NatTrans.ext (funext fun _ => rfl))

/-! ## Hom-elimination and Hom-computation -/

variable {a₀} (D : ICatLax.{u, u}.Ty (homElimCtx a₀))

/-- The square `(d ≫ 𝐪(r, D), 𝟙) : r ⟶ 𝐩 D` of a term `d` of `D⦃r⦄`. -/
def homElimSq (d : Tm(Γ, D⦃homElimR a₀⦄)) : homElimRArr a₀ ⟶ (∫ D).πArr :=
  ⟨d.sec ≫ 𝐪(homElimR a₀, D), 𝟙 (homElimCtx a₀), by
    kernel_exact congrArg (· ≫ homElimR a₀) d.sec_proj⟩

/-- **Hom-elimination**: the term `j(f, d)` of `D` in context `Γ ▹ b : A ▹ f : Homₐ(ā₀, b)`, the
chosen lift of the square `(d ≫ 𝐪(r, D), 𝟙)` of the AWFS on `Cat` from the coalgebra of the LARI
`r` to the algebra of the split opfibration `∫ D`. -/
def homElim (d : Tm(Γ, D⦃homElimR a₀⦄)) : Tm(homElimCtx a₀, D) where
  sec := AWFS.lift (A := catAWFS) (homElimLari a₀).toLCoalg (∫ D).ralg (homElimSq D d)
  sec_proj := AWFS.lift_comp_hom (A := catAWFS) (homElimLari a₀).toLCoalg (∫ D).ralg (homElimSq D d)

/-- **Hom-computation**: `j(refl_a₀, d) ≡ d`, the upper triangle of the chosen lift. -/
theorem homComp (d : Tm(Γ, D⦃homElimR a₀⦄)) : (homElim D d)⦃homElimR a₀⦄ = d :=
  (Tm.pull_unique (homElimR a₀) (homElim D d) d
    (AWFS.hom_comp_lift (A := catAWFS) (homElimLari a₀).toLCoalg (∫ D).ralg
      (homElimSq D d)).symm).symm

end Elim

/-! ## Stability under substitution -/

section Pull

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, A))

/-- The substitution `[a₀/a]` is natural in the context: both composites are
`(δ, b) ↦ (σ δ, b, a₀ (σ δ))`. -/
theorem q_sec_weak :
    𝐪(σ, A) ≫ (a₀⦃𝐩 A⦄).sec = (a₀⦃σ⦄⦃𝐩 (A⦃σ⦄)⦄).sec ≫ 𝐪(𝐪(σ, A), A⦃𝐩 A⦄) :=
  Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

/-- The twist of the Hom-type is stable under substitution, by the rule `pull_twist` and the
stability of the Hom-type (`pull_hom`). -/
theorem pull_twist_homFunctor :
    (twist (homFunctor A))⦃𝐪(𝐪(σ, A), A⦃𝐩 A⦄)⦄ = twist (homFunctor (A⦃σ⦄)) := by
  kernel_rfl'

/-- **The Hom-type `Homₐ(ā₀, b)` is stable under substitution**: along `𝐪(σ, A)`, it is that of
`A⦃σ⦄` based at `a₀⦃σ⦄`, by the naturality of `[a₀/a]` (`q_sec_weak`) and the stability of the
twist of the Hom-type (`pull_twist_homFunctor`). The kernel checks the two types to be equal by
`rfl` too, but slowly: it first compares `𝐪(σ, A)` with `[a₀/a]`, which differ. It is a rule, so
that the context extended by the substituted Hom-type is `homElimCtx a₀⦃σ⦄`. -/
@[rewrite_rule]
theorem homElimTy_pull :
    ((twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄)⦃𝐪(σ, A)⦄ =
      (twist (homFunctor (A⦃σ⦄)))⦃(a₀⦃σ⦄⦃𝐩 (A⦃σ⦄)⦄).sec⦄ := by
  kernel_exact (congrArg (fun τ => (twist (homFunctor A))⦃τ⦄) (q_sec_weak σ a₀)).trans
    (congrArg (fun T => T⦃(a₀⦃σ⦄⦃𝐩 (A⦃σ⦄)⦄).sec⦄) (pull_twist_homFunctor σ))

/-- **The substitution `σ⁺ : homElimCtx a₀⦃σ⦄ ⟶ homElimCtx a₀`**, the morphism
`𝐪(𝐪(σ, A), Homₐ(ā₀, b))` of the comprehension structures, whose domain is `homElimCtx a₀⦃σ⦄` by
the rule `homElimTy_pull`. It is `(δ, b, f) ↦ (σ δ, b, f)`. -/
def homElimCtxMap : homElimCtx a₀⦃σ⦄ ⟶ homElimCtx a₀ :=
  𝐪(𝐪(σ, A), (twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄)

/-- The substitution commutes with `r`. -/
theorem homElimR_homElimCtxMap : σ ≫ homElimR a₀ = homElimR a₀⦃σ⦄ ≫ homElimCtxMap σ a₀ := by
  kernel_rfl'

/-- The substitution commutes with the projections. -/
theorem homElimCtxMap_homElimRet : homElimCtxMap σ a₀ ≫ homElimRet a₀ = homElimRet a₀⦃σ⦄ ≫ σ := by
  kernel_rfl'

/-- The substitution commutes with the codomains. -/
theorem homElimCtxMap_homElimCod :
    homElimCtxMap σ a₀ ≫ homElimCod a₀ = homElimCod a₀⦃σ⦄ ≫ 𝐪(σ, A) := by
  kernel_rfl'

/-- The square `(σ, σ⁺) : r' ⟶ r` of `Arr Cat`, from the functor `r` of `a₀⦃σ⦄` to that of
`a₀`. -/
def homElimRArrMap : homElimRArr a₀⦃σ⦄ ⟶ homElimRArr a₀ :=
  ⟨σ, homElimCtxMap σ a₀, homElimR_homElimCtxMap σ a₀⟩

/-- **The substitution is a morphism of LARIs**: it commutes with `r`, with the projections `F`
and with the counits `ε`. -/
def homElimLariHom : (homElimLari a₀⦃σ⦄).Hom (homElimLari a₀) where
  toPreHom := ⟨homElimRArrMap σ a₀, homElimCtxMap_homElimRet σ a₀⟩
  counit_comm := Cat.Hom₂.ext (NatTrans.ext (funext fun _ => by kernel_rfl'))

variable {σ a₀} (D : ICatLax.{u, u}.Ty (homElimCtx a₀))

variable (σ) in
/-- **The reindexing of the motive `D` along `σ⁺` is a morphism of `R`-algebras**: its total
functor `𝐪(σ⁺, D)` preserves the chosen lifts. -/
def homElimAlgHom : (∫ (D⦃homElimCtxMap σ a₀⦄)).ralg ⟶ (∫ D).ralg :=
  (StrictTrans.unstraighten (u := (homElimCtxMap σ a₀).toFunctor)
    (StrictTrans.id ((homElimCtxMap σ a₀).toFunctor ⋙ D))).ralgHom

/-- The morphism of `R`-algebras is `𝐪(σ⁺, D)` on the total categories. -/
theorem homElimAlgHom_left : (homElimAlgHom σ D).hom.left = 𝐪(homElimCtxMap σ a₀, D) := by
  kernel_rfl'

variable (σ) in
/-- The square of the substituted premise `d⦃σ⦄`, whose type `D⦃r⦄⦃σ⦄` is `D⦃σ⁺⦄⦃r'⦄` by `rfl`,
is the reindexing of the square of `d`. -/
theorem homElimSq_pull (d : Tm(Γ, D⦃homElimR a₀⦄)) :
    (homElimLariHom σ a₀).toLCoalgHom.hom ≫ homElimSq D d =
      homElimSq (D⦃homElimCtxMap σ a₀⦄) d⦃σ⦄ ≫ (homElimAlgHom σ D).hom := by
  refine Arr.Hom.ext ?_ (by kernel_rfl')
  kernel_exact (congrArg (· ≫ 𝐪(homElimR a₀, D)) (Tm.pull_sec_q σ d)).symm

variable (σ) in
/-- **Hom-elimination is stable under substitution**: substituted along `σ⁺`, the term `j(f, d)`
is that of the substituted motive `D⦃σ⁺⦄` and premise `d⦃σ⦄`. -/
theorem homElim_pull (d : Tm(Γ, D⦃homElimR a₀⦄)) :
    (homElim D d)⦃homElimCtxMap σ a₀⦄ = homElim (D⦃homElimCtxMap σ a₀⦄) d⦃σ⦄ := by
  refine (Tm.pull_unique (homElimCtxMap σ a₀) (homElim D d) _ ?_).symm
  kernel_exact (AWFS.coalgHom_comp_lift_eq (A := catAWFS) (homElimLari a₀).toLCoalg (∫ D).ralg
    (homElimSq D d) (homElimLariHom σ a₀).toLCoalgHom (homElimAlgHom σ D)
    (homElimSq (D⦃homElimCtxMap σ a₀⦄) d⦃σ⦄) (homElimSq_pull σ D d)).symm

end Pull

end ComprehensionCategory.OverCat
