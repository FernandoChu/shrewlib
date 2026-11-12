import ComprehensionCategory.Model.OverCat.Shared.HomIntro
import Displayed.Opfibration.RAlgebra

/-!
# Hom-elimination

For a type `A` of the category model in context `Γ`, a type `X` in context `Γ ▹ a : A`, and a type
`D` of the category model in the context of the twisted Hom-type extended by `X`, the category model
validates the elimination and computation rules of the Hom-types (paper, `prop:hom-elim`):

```
     Γ ⊢ A type      Γ ▹ a : A ⊢ X type
     Γ ▹ b : A ▹ a : A ▹ f : Homₐ(ā, b) ▹ x : X ⊢ D type
     Γ ▹ a : A ▹ x : X ⊢ d : D[ā/a, a/b, refl_a/f]
  -------------------------------------------------------------- Hom-Elim
     Γ ▹ b : A ▹ a : A ▹ f : Homₐ(ā, b) ▹ x : X ⊢ j(f, x, d) : D

     Γ ▹ a : A ▹ x : X ⊢ j(refl_a, x, d) ≡ d : D[ā/a, a/b, refl_a/f]          Hom-Comp
```

* The context `Γ ▹ b : A ▹ a : A ▹ f : Homₐ(ā, b)` (`homCtx`) extends `Γ ▹ A ▹ A⦃𝐩 A⦄` by the twist
  of the Hom-type (`Shared/Twist`, `Shared/HomIntro`), in the displayed model. Its objects are the
  tuples `(γ, b, a, f : a ⟶ b)`, and its morphisms the tuples `(θ, β, α, e)` with `e` a proof of
  `A θ f ≫ β = α ≫ f'`, as in `prop:twist-hom` of the paper. The motive lives in its extension
  `elimCtx A X` by `X`, weakened along the domain `homDom : (γ, b, a, f) ↦ (γ, a)`.
* The substitution `[ā/a, a/b, refl_a/f]` is `reflSec : (γ, a) ↦ (γ, a, a, 𝟙 a)`, the extension of
  the diagonal by the term `refl` of Hom-Intro (`reflSec_eq`), and it extends to
  `r = homR : (γ, a, x) ↦ (γ, a, a, 𝟙 a, x)`, the morphism `𝐪(reflSec A, X⦃homDom A⦄)` of the
  category model (`homR_eq`), whose domain `Γ ▹ A ▹ X⦃homDom A⦄⦃reflSec A⦄` is `Γ ▹ A ▹ X` by
  `rfl`. So the premise `d : D[ā/a, a/b, refl_a/f]` is a term of `D⦃homR A X⦄`.

These functors are given by their values, so that the rules compute them, and are shown to be
the morphisms of the comprehension structures (`homDom_eq`, `reflSec_eq`, `homR_eq`, …).

## The proof, through the AWFS

As in the paper, Hom-Elim is the chosen lift of the comma AWFS on `Cat` (`TwoCategory.catAWFS`,
`TwoCategory.AWFS.lift`):

* `r` is a left adjoint right inverse (`homLari`), with retraction
  `F = 𝐪(homDom A, X) : (γ, b, a, f, x) ↦ (γ, a, x)` (`homRet`) and counit
  `ε : F ≫ r ⟶ 𝟙` with components `(𝟙, (f, 𝟙), 𝟙) : (γ, a, a, 𝟙, x) ⟶ (γ, b, a, f, x)`
  (`homCounit`). So `r` is an `L`-coalgebra (`Arr.Lari.toLCoalg`). The `X`-component of `ε` is a
  transport along the identity `(𝟙 γ, 𝟙 a)` of `Γ ▹ A`, computed componentwise, which the rule for
  the functor law of `X` does not see as an identity (`map_idMk_obj`).
* `D` is a type of the category model, so `∫ D` is a split opfibration, and its projection `𝐩 D`
  an `R`-algebra (`Displayed.ralg`).
* `homElim D d` is the chosen lift of the square `(d ≫ 𝐪(r, D), 𝟙) : r ⟶ 𝐩 D` (`homElimSq`). The
  lower triangle makes it a term of `D`, and the upper one is Hom-Comp
  (`homElim_pull_homR : (homElim D d)⦃homR A X⦄ = d`).

## Stability under substitution

For `σ : Δ ⟶ Γ`, the substitution `σ⁺ : elimCtx (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ⟶ elimCtx A X`
(`elimCtxMap`, the morphism `𝐪(𝐪(𝐪(𝐪(σ, A), A⦃𝐩 A⦄), Hom), X⦃homDom A⦄)` of the comprehension
structures, `homCtxMap_eq` and `elimCtxMap_eq`) commutes with `r`, with the retractions and with
the counits, all by `rfl`. So `(𝐪(𝐪(σ, A), X), σ⁺)` is a morphism of LARIs (`homLariHom`), hence of
`L`-coalgebras, and `𝐪(σ⁺, D)` preserves the chosen lifts, a morphism of `R`-algebras
(`homElimAlgHom`). The square of the substituted premise `d⦃𝐪(𝐪(σ, A), X)⦄`, whose type
`D⦃homR A X⦄⦃𝐪(𝐪(σ, A), X)⦄` is `D⦃σ⁺⦄⦃homR (A⦃σ⦄) (X⦃𝐪(σ, A)⦄)⦄` by `rfl`, is the reindexing of
that of `d` (`homElimSq_pull`), and by the functoriality of the chosen lifts
(`AWFS.coalgHom_comp_lift_eq`) and the uniqueness of substitutions of terms,

```
  j(f, x, d)⦃σ⁺⦄ = j(f, x, d⦃𝐪(𝐪(σ, A), X)⦄)          (homElim_pull)
```

with the motive `D⦃σ⁺⦄`. No transport is needed.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel TwoCategory

open scoped Displayed

variable {Γ : Cat.{u, u}}

section Elim

variable (A : ICatLax.{u, u}.Ty Γ) (X : ICatLax.{u, u}.Ty (Γ ▹ A))

/-! ## The context of Hom-elimination -/

/-- The context `Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b)`, extended in the displayed model by the twist
of the Hom-type. Its objects are the tuples `(((γ, b), a), f)` with `f : a ⟶ b` in `A γ`, and its
morphisms `(((θ, β), α), e)` the tuples of `θ : γ ⟶ γ'`, `β : A θ b ⟶ b'`, `α : A θ a ⟶ a'` and a
proof `e` of `A θ f ≫ β = α ≫ f'`. -/
abbrev homCtx : Cat.{u, u} :=
  Γ ▹ A ▹ A⦃𝐩 A⦄ ▹ twist (homFunctor A)

/-- The domain `homCtx A ⟶ Γ ▹ A`, `(γ, b, a, f) ↦ (γ, a)`. -/
def homDom : homCtx A ⟶ Γ ▹ A :=
  (show (homCtx A : Type u) ⥤ (Γ ▹ A : Cat.{u, u}) from
    { obj p := ⟨p.1.1.1, p.1.2⟩
      map k := ⟨k.base.base.base, k.base.fiber⟩
      map_id _ := rfl
      map_comp _ _ := rfl }).toCatHom

/-- The context `Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b) ▹ x : X` of the motive of Hom-elimination,
extended in the category model by `X`, weakened along the domain. Its objects are the tuples
`((γ, b, a, f), x)` with `x : X (γ, a)`. -/
abbrev elimCtx : Cat.{u, u} :=
  homCtx A ▹ X⦃homDom A⦄

/-- The reflexivity `Γ ▹ A ⟶ homCtx A`, `(γ, a) ↦ (γ, a, a, 𝟙 a)`. -/
def reflSec : Γ ▹ A ⟶ homCtx A :=
  (show (Γ ▹ A : Cat.{u, u}) ⥤ (homCtx A : Type u) from
    { obj p := ⟨⟨⟨p.1, p.2⟩, p.2⟩, CategoryStruct.id (obj := A.obj p.1) p.2⟩
      map k := ⟨⟨⟨k.base, k.fiber⟩, k.fiber⟩, ⟨⟨rfl⟩⟩⟩
      map_id _ := by kernel_rfl'
      map_comp _ _ := by kernel_rfl' }).toCatHom

/-- The reflexivity is a section of the domain. -/
theorem reflSec_homDom : reflSec A ≫ homDom A = 𝟙 (Γ ▹ A) :=
  rfl

/-- **The functor `r : Γ ▹ a : A ▹ x : X ⟶ elimCtx A X`**, `(γ, a, x) ↦ (γ, a, a, 𝟙 a, x)`: the
reflexivity, extended by `x`, which is in `X (γ, a)` since `reflSec A ≫ homDom A = 𝟙`. -/
def homR : Γ ▹ A ▹ X ⟶ elimCtx A X :=
  (show (Γ ▹ A ▹ X : Cat.{u, u}) ⥤ (elimCtx A X : Type u) from
    { obj q := ⟨(reflSec A).toFunctor.obj q.1, q.2⟩
      map k := ⟨(reflSec A).toFunctor.map k.base, k.fiber⟩
      map_id _ := by kernel_rfl'
      map_comp _ _ := by kernel_rfl' }).toCatHom

/-- **The retraction `F : elimCtx A X ⟶ Γ ▹ a : A ▹ x : X`**, `(γ, b, a, f, x) ↦ (γ, a, x)`. -/
def homRet : elimCtx A X ⟶ Γ ▹ A ▹ X :=
  (show (elimCtx A X : Type u) ⥤ (Γ ▹ A ▹ X : Cat.{u, u}) from
    { obj e := ⟨(homDom A).toFunctor.obj e.1, e.2⟩
      map k := ⟨(homDom A).toFunctor.map k.base, k.fiber⟩
      map_id _ := rfl
      map_comp _ _ := rfl }).toCatHom

/-- The retraction is the morphism `𝐪(homDom A, X)` of the category model. -/
theorem homRet_eq : homRet A X = 𝐪(homDom A, X) :=
  rfl

/-- `r ≫ F = 𝟙`. -/
theorem homR_homRet : homR A X ≫ homRet A X = 𝟙 (Γ ▹ A ▹ X) :=
  rfl

/-! ### In terms of the comprehension structures

The functors above are given by their values, for the rules to compute them. They are the
morphisms built from the comprehension structures of the category model and of the displayed
model, as in the paper. -/

/-- The domain is the projection of the twisted Hom-type followed by `𝐪(𝐩 A, A)`. -/
theorem homDom_eq : homDom A = 𝐩 (twist (homFunctor A)) ≫ 𝐪(𝐩 A, A) := by
  kernel_exact (congrArg (· ≫ 𝐪(𝐩 A, A))
    (DisplayedModel.proj_straightenObj (twistDisp (homFunctor A)))).symm

/-- **The reflexivity is the substitution `[a/b, refl_a/f]`**: the extension of the diagonal
`Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄` by the term `refl A` of Hom-Intro (`Shared/HomIntro`). -/
theorem reflSec_eq : reflSec A = consSec (diag A) ((refl A).castTy (twistedHom_eq A)) := by
  kernel_exact (DisplayedModel.consSec_straightenObj (diag A) (twistDisp (homFunctor A))
    (refl A)).symm

/-- **`r` is the substitution `[ā/a, a/b, refl_a/f]`, extended by `x`**: the morphism
`𝐪(reflSec A, X⦃homDom A⦄)`, whose domain `Γ ▹ A ▹ X⦃homDom A⦄⦃reflSec A⦄` is `Γ ▹ A ▹ X` by
`rfl`. -/
theorem homR_eq : homR A X = 𝐪(reflSec A, X⦃homDom A⦄) :=
  rfl

/-! ## The counit -/

/-- The identity of `(γ, a)`, computed componentwise as `(𝟙 γ, 𝟙 a)`. -/
abbrev idMk (q : (Γ ▹ A : Cat.{u, u})) : q ⟶ q :=
  (⟨𝟙 q.1, CategoryStruct.id (obj := A.obj q.1) q.2⟩ : Total.Hom q q)

variable {A} in
/-- The transport along an endomorphism equal to an identity is the identity, propositionally. -/
theorem map_obj_of_eq_id {q : (Γ ▹ A : Cat.{u, u})} (k : q ⟶ q) (hk : k = 𝟙 q) (x : X.obj q) :
    (X.map k).toFunctor.obj x = x := by
  subst hk
  rfl

/-- The transport along `(𝟙 γ, 𝟙 a)` is the identity, propositionally: the rule for the functor law
of `X` does not see `(𝟙 γ, 𝟙 a)` as an identity. -/
theorem map_idMk_obj (q : (Γ ▹ A : Cat.{u, u})) (x : X.obj q) :
    (X.map (idMk A q)).toFunctor.obj x = x :=
  map_obj_of_eq_id X (idMk A q) rfl x

variable {A} in
/-- The transport of a morphism along an endomorphism equal to an identity, followed by `eqToHom`,
is that morphism, up to the transports. -/
theorem map_map_comp_eqToHom_heq {q : (Γ ▹ A : Cat.{u, u})} (k : q ⟶ q) (hk : k = 𝟙 q)
    {y z : X.obj q} (ξ : y ⟶ z) (h : (X.map k).toFunctor.obj z = z) :
    (X.map k).toFunctor.map ξ ≫ eqToHom h ≍ ξ := by
  subst hk
  simp

variable {A} in
/-- The transport of `eqToHom` followed by a morphism is that morphism, up to the transports. -/
theorem map_eqToHom_comp_heq {q q' : (Γ ▹ A : Cat.{u, u})} (k : q ⟶ q') {y y' : X.obj q}
    (h : y' = y) {z : X.obj q'} (ξ : (X.map k).toFunctor.obj y ⟶ z) :
    (X.map k).toFunctor.map (eqToHom h) ≫ ξ ≍ ξ := by
  subst h
  simp

/-- Morphisms of `homCtx A` with the same base are equal: their components in the twisted Hom-type
are proofs of equations. -/
theorem homCtx_hom_ext {p p' : homCtx A} {k k' : p ⟶ p'} (h : k.base = k'.base) : k = k' := by
  obtain ⟨b, ⟨⟨_⟩⟩⟩ := k
  obtain ⟨b', ⟨⟨_⟩⟩⟩ := k'
  dsimp only at h
  subst h
  rfl

/-- The component at `e = (γ, b, a, f, x)` of the counit, `(𝟙, (f, 𝟙), 𝟙) : (γ, a, a, 𝟙, x) ⟶ e`. -/
def homCounitApp (e : elimCtx A X) : (homRet A X ≫ homR A X).toFunctor.obj e ⟶ e :=
  ⟨⟨⟨⟨𝟙 e.1.1.1.1, e.1.2⟩, CategoryStruct.id (obj := A.obj e.1.1.1.1) e.1.1.2⟩, ⟨⟨rfl⟩⟩⟩,
    eqToHom (map_idMk_obj A X ((homDom A).toFunctor.obj e.1) e.2)⟩

/-- The counit is natural: its base components commute by the equation `A θ f ≫ β = α ≫ f'` of
morphisms of `homCtx A`, and its `X`-components are transports. -/
theorem homCounitApp_naturality {e e' : elimCtx A X} (K : e ⟶ e') :
    (homRet A X ≫ homR A X).toFunctor.map K ≫ homCounitApp A X e' =
      homCounitApp A X e ≫ K := by
  refine Total.Hom.ext' (homCtx_hom_ext A (Total.Hom.ext'
    (Total.Hom.ext' rfl (heq_of_eq K.base.fiber.down.down.symm)) HEq.rfl)) ?_
  kernel_exact (map_map_comp_eqToHom_heq X (idMk A ((homDom A).toFunctor.obj e'.1)) rfl K.fiber
    (map_idMk_obj A X _ e'.2)).trans
      (map_eqToHom_comp_heq X ((homDom A).toFunctor.map K.base) (map_idMk_obj A X _ e.2)
        K.fiber).symm

/-- **The counit `ε : F ≫ r ⟶ 𝟙`**, with components `(𝟙, (f, 𝟙), 𝟙) : (γ, a, a, 𝟙, x) ⟶ e` at
`e = (γ, b, a, f, x)`. -/
def homCounit : homRet A X ≫ homR A X ⟶ 𝟙 (elimCtx A X) :=
  ⟨{ app := homCounitApp A X, naturality := fun _ _ K => homCounitApp_naturality A X K }⟩

omit A X in
/-- `eqToHom h` is heterogeneously equal to the identity. -/
theorem eqToHom_heq_id {C : Type u} [Category.{u} C] {y x : C} (h : y = x) : eqToHom h ≍ 𝟙 x := by
  subst h
  rfl

/-- `r`, as an arrow of `Cat`. -/
abbrev homRArr : Arr Cat.{u, u} :=
  ⟨Γ ▹ A ▹ X, elimCtx A X, homR A X⟩

/-- **`r` is a LARI**, `r ⊣ F` with identity unit and counit `ε`. -/
def homLari : (homRArr A X).Lari where
  toRetraction := ⟨homRet A X, homR_homRet A X⟩
  counit := homCounit A X
  hom_whiskerLeft_counit := Cat.Hom₂.ext (NatTrans.ext (funext fun q =>
    Total.Hom.ext' (homCtx_hom_ext A rfl) (by
      kernel_exact eqToHom_heq_id (map_idMk_obj A X _ q.2))))
  counit_whiskerRight_r := Cat.Hom₂.ext (NatTrans.ext (funext fun e =>
    Total.Hom.ext' rfl (by kernel_exact eqToHom_heq_id (map_idMk_obj A X _ e.2))))

/-! ## Hom-elimination and Hom-computation -/

variable {A X} (D : ICatLax.{u, u}.Ty (elimCtx A X))

/-- The square `(d ≫ 𝐪(r, D), 𝟙) : r ⟶ 𝐩 D` of a term `d` of `D⦃r⦄`. -/
def homElimSq (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : homRArr A X ⟶ (∫ D).πArr :=
  ⟨d.sec ≫ 𝐪(homR A X, D), 𝟙 (elimCtx A X), by
    kernel_exact congrArg (· ≫ homR A X) d.sec_proj⟩

/-- **Hom-elimination**: the term `j(f, x, d)` of `D` in context
`Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b) ▹ x : X`, the chosen lift of the square `(d ≫ 𝐪(r, D), 𝟙)`
of the AWFS on `Cat` from the coalgebra of the LARI `r` to the algebra of the split opfibration
`∫ D`. -/
def homElim (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : Tm(elimCtx A X, D) where
  sec := AWFS.lift (A := catAWFS) (homLari A X).toLCoalg (∫ D).ralg (homElimSq D d)
  sec_proj := AWFS.lift_comp_hom (A := catAWFS) (homLari A X).toLCoalg (∫ D).ralg (homElimSq D d)

/-- **Hom-computation**: `j(refl_a, x, d) ≡ d`, the upper triangle of the chosen lift. -/
theorem homElim_pull_homR (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : (homElim D d)⦃homR A X⦄ = d :=
  (Tm.pull_unique (homR A X) (homElim D d) d
    (AWFS.hom_comp_lift (A := catAWFS) (homLari A X).toLCoalg (∫ D).ralg
      (homElimSq D d)).symm).symm

end Elim

/-! ## Stability under substitution -/

section Pull

variable {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatLax.{u, u}.Ty Γ) (X : ICatLax.{u, u}.Ty (Γ ▹ A))

/-- The substitution `homCtx (A⦃σ⦄) ⟶ homCtx A`, `(δ, b, a, f) ↦ (σ δ, b, a, f)`. -/
def homCtxMap : homCtx (A⦃σ⦄) ⟶ homCtx A :=
  (show (homCtx (A⦃σ⦄) : Type u) ⥤ (homCtx A : Type u) from
    { obj p := ⟨⟨⟨σ.toFunctor.obj p.1.1.1, p.1.1.2⟩, p.1.2⟩, p.2⟩
      map k := ⟨⟨⟨σ.toFunctor.map k.base.base.base, k.base.base.fiber⟩, k.base.fiber⟩, k.fiber⟩
      map_id _ := by kernel_rfl'
      map_comp _ _ := by kernel_rfl' }).toCatHom

/-- The substitution is the morphism `𝐪(𝐪(𝐪(σ, A), A⦃𝐩 A⦄), Hom_A(ā, b))` of the comprehension
structures, whose domain is `homCtx (A⦃σ⦄)` by the rules `pull_twist` and `pull_q_pull_proj`. -/
theorem homCtxMap_eq : homCtxMap σ A = 𝐪(𝐪(𝐪(σ, A), A⦃𝐩 A⦄), twist (homFunctor A)) := by
  kernel_rfl'

/-- The substitution commutes with the domains. -/
theorem homCtxMap_homDom : homCtxMap σ A ≫ homDom A = homDom (A⦃σ⦄) ≫ 𝐪(σ, A) := by
  kernel_rfl'

/-- The substitution `elimCtx (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ⟶ elimCtx A X`,
`(δ, b, a, f, x) ↦ (σ δ, b, a, f, x)`. -/
def elimCtxMap : elimCtx (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ⟶ elimCtx A X :=
  (show (elimCtx (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) : Type u) ⥤ (elimCtx A X : Type u) from
    { obj e := ⟨(homCtxMap σ A).toFunctor.obj e.1, e.2⟩
      map k := ⟨(homCtxMap σ A).toFunctor.map k.base, k.fiber⟩
      map_id _ := by kernel_rfl'
      map_comp _ _ := by kernel_rfl' }).toCatHom

/-- The substitution is the morphism `𝐪(homCtxMap σ A, X⦃homDom A⦄)` of the category model, whose
domain is `elimCtx (A⦃σ⦄) (X⦃𝐪(σ, A)⦄)` by `homCtxMap_homDom`. -/
theorem elimCtxMap_eq : elimCtxMap σ A X = 𝐪(homCtxMap σ A, X⦃homDom A⦄) := by
  kernel_rfl'

/-- The substitution commutes with `r`. -/
theorem homR_elimCtxMap :
    𝐪(𝐪(σ, A), X) ≫ homR A X = homR (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ≫ elimCtxMap σ A X := by
  kernel_rfl'

/-- The substitution commutes with the retractions. -/
theorem elimCtxMap_homRet :
    elimCtxMap σ A X ≫ homRet A X = homRet (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ≫ 𝐪(𝐪(σ, A), X) := by
  kernel_rfl'

/-- The square `(𝐪(𝐪(σ, A), X), σ⁺) : r' ⟶ r` of `Arr Cat`, from the functor `r` of `A⦃σ⦄` and
`X⦃𝐪(σ, A)⦄` to that of `A` and `X`. -/
def homRArrMap : homRArr (A⦃σ⦄) (X⦃𝐪(σ, A)⦄) ⟶ homRArr A X :=
  ⟨𝐪(𝐪(σ, A), X), elimCtxMap σ A X, homR_elimCtxMap σ A X⟩

/-- **The substitution is a morphism of LARIs**: it commutes with `r`, with the retractions `F` and
with the counits `ε`. -/
def homLariHom : (homLari (A⦃σ⦄) (X⦃𝐪(σ, A)⦄)).Hom (homLari A X) where
  toPreHom := ⟨homRArrMap σ A X, elimCtxMap_homRet σ A X⟩
  counit_comm := Cat.Hom₂.ext (NatTrans.ext (funext fun _ => by kernel_rfl'))

variable {A X} (D : ICatLax.{u, u}.Ty (elimCtx A X))

/-- **The reindexing of the motive `D` along `σ⁺` is a morphism of `R`-algebras**: its total functor
`𝐪(σ⁺, D)` preserves the chosen lifts. -/
def homElimAlgHom : (∫ (D⦃elimCtxMap σ A X⦄)).ralg ⟶ (∫ D).ralg :=
  (StrictTrans.unstraighten (u := (elimCtxMap σ A X).toFunctor)
    (StrictTrans.id ((elimCtxMap σ A X).toFunctor ⋙ D))).ralgHom

/-- The morphism of `R`-algebras is `𝐪(σ⁺, D)` on the total categories. -/
theorem homElimAlgHom_left : (homElimAlgHom σ D).hom.left = 𝐪(elimCtxMap σ A X, D) := by
  kernel_rfl'

/-- The substituted premise: `d⦃𝐪(𝐪(σ, A), X)⦄`, whose type `D⦃r⦄⦃𝐪(𝐪(σ, A), X)⦄` is
`D⦃σ⁺⦄⦃r'⦄` by `rfl`, as `𝐪(𝐪(σ, A), X) ≫ r = r' ≫ σ⁺` holds by `rfl`. -/
def homElimPremisePull (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) :
    Tm(Δ ▹ A⦃σ⦄ ▹ X⦃𝐪(σ, A)⦄, D⦃elimCtxMap σ A X⦄⦃homR (A⦃σ⦄) (X⦃𝐪(σ, A)⦄)⦄) :=
  d⦃𝐪(𝐪(σ, A), X)⦄

/-- The square of the substituted premise is the reindexing of the square of `d`. -/
theorem homElimSq_pull (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) :
    (homLariHom σ A X).toLCoalgHom.hom ≫ homElimSq D d =
      homElimSq (D⦃elimCtxMap σ A X⦄) (homElimPremisePull σ D d) ≫ (homElimAlgHom σ D).hom := by
  refine Arr.Hom.ext ?_ rfl
  kernel_exact (congrArg (· ≫ 𝐪(homR A X, D)) (Tm.pull_sec_q 𝐪(𝐪(σ, A), X) d)).symm

/-- **Hom-elimination is stable under substitution**: substituted along `σ⁺`, the term
`j(f, x, d)` is that of the substituted motive `D⦃σ⁺⦄` and premise `d⦃𝐪(𝐪(σ, A), X)⦄`. -/
theorem homElim_pull (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) :
    (homElim D d)⦃elimCtxMap σ A X⦄ =
      homElim (D⦃elimCtxMap σ A X⦄) (homElimPremisePull σ D d) := by
  refine (Tm.pull_unique (elimCtxMap σ A X) (homElim D d) _ ?_).symm
  kernel_exact (AWFS.coalgHom_comp_lift_eq (A := catAWFS) (homLari A X).toLCoalg (∫ D).ralg
    (homElimSq D d) (homLariHom σ A X).toLCoalgHom (homElimAlgHom σ D)
    (homElimSq (D⦃elimCtxMap σ A X⦄) (homElimPremisePull σ D d)) (homElimSq_pull σ D d)).symm

end Pull

end ComprehensionCategory.OverCat
