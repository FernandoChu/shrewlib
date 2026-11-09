import ComprehensionCategory.Model.OverCat.CatOp.Basic
import ComprehensionCategory.Term
import Displayed.Displayed.Section

/-!
# Terms in the contravariant category model

A term `t : Tm(Γ, A)` of a type `A : Γᵒᵖ ⥤ Cat` is a section of the projection `Γ ⋉⁻ A ⥤ Γ`. The
term `tmMk obj map _ _` is the section `γ ↦ (γ, obj γ)`, from values `obj γ : A γ` and transports
`map f : obj γ ⟶ A f (obj γ')`, compatible with identities and composites; its equation
`sec ≫ 𝐩 A = 𝟙 Γ` holds by `rfl`. The variable `var A : Tm(Γ ▹ A, A⦃𝐩 A⦄)` is `(γ, a) ↦ a`, and
its section is the diagonal `diag A : Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄`.

For the constant type `constTy Γ K` at a category `K`, whose transports are identities, the terms
are the functors `Γ ⥤ K` (`Tm.constEquiv`), naturally in `Γ`, as in the category model.

This is the dual of `OverCat/Cat/Term.lean`.

More generally, the terms of any type `A` are the sections of its unstraightening
(`Tm.sectionEquiv`, `Displayed/Displayed/Section`): the term of a section `S` is `S.total`, and the
section of a term transports its values along the equalities of their first components with the
points of `Γ`.
-/

universe u

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Opposite Displayed Displayed.Fibration.Straightening

open scoped Displayed

variable {Γ Δ : Cat.{u, u}}

/-- **The term of `A` with values `obj γ : A γ`** and transports `map f : obj γ ⟶ A f (obj γ')`:
the section `γ ↦ (γ, obj γ)` of the projection, which is a section by `rfl`. -/
def tmMk {A : ICatOpLax.{u, u}.Ty Γ} (obj : ∀ γ : Γ, A.obj (op γ))
    (map : ∀ {γ γ' : Γ} (f : γ ⟶ γ'), obj γ ⟶ (A.map f.op).toFunctor.obj (obj γ'))
    (map_id : ∀ γ : Γ, map (𝟙 γ) = 𝟙 (obj γ))
    (map_comp : ∀ {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ''),
      map (f ≫ g) = map f ≫ (A.map f.op).toFunctor.map (map g)) : Tm(Γ, A) where
  sec := (show Γ ⥤ Γ ⋉⁻ A from
    { obj γ := (∫⁻ A).tot (obj γ)
      map f := (∫⁻ A).totalMk f (map f)
      map_id γ := congrArg ((∫⁻ A).totalMk (𝟙 γ)) (map_id γ)
      map_comp f g := congrArg ((∫⁻ A).totalMk (f ≫ g)) (map_comp f g) }).toCatHom
  sec_proj := rfl

/-- **The variable of `A`**: the term of `A⦃𝐩 A⦄` in context `Γ ▹ A`, `(γ, a) ↦ a`. -/
def var (A : ICatOpLax.{u, u}.Ty Γ) : Tm(Γ ▹ A, A⦃𝐩 A⦄) :=
  tmMk (A := A⦃𝐩 A⦄) (fun x => x.2) (fun f => f.fiber) (fun _ => rfl) fun _ _ => rfl

/-- **The diagonal** `Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄`, `(γ, a) ↦ ((γ, a), a)`: the section of the
variable of `A`. -/
def diag (A : ICatOpLax.{u, u}.Ty Γ) : Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄ :=
  (var A).sec

/-! ## Terms of constant types -/

/-- The constant type at a category `K`: `γ ↦ K`, with identity transports. -/
def constTy (Γ : Cat.{u, u}) (K : Cat.{u, u}) : ICatOpLax.{u, u}.Ty Γ where
  obj _ := K
  map _ := 𝟙 K
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The constant types are closed: they are stable under substitution. -/
theorem pull_constTy (σ : Δ ⟶ Γ) (K : Cat.{u, u}) : (constTy Γ K)⦃σ⦄ = constTy Δ K :=
  rfl

variable {K : Cat.{u, u}}

namespace Tm

/-- The functor `Γ ⥤ K` of a term of the constant type at `K`: its values. -/
def toConst (t : Tm(Γ, constTy Γ K)) : Γ ⥤ K where
  obj γ := Sigma.snd (t.sec.toFunctor.obj γ)
  map f := Total.Hom.fiber (t.sec.toFunctor.map f)
  map_id γ := congrArg (fun F => (Total.Hom.fiber F :
      @Quiver.Hom K _ (Sigma.snd (t.sec.toFunctor.obj γ)) (Sigma.snd (t.sec.toFunctor.obj γ))))
    (t.sec.toFunctor.map_id γ)
  map_comp {γ _ γ''} f g := congrArg (fun F => (Total.Hom.fiber F :
      @Quiver.Hom K _ (Sigma.snd (t.sec.toFunctor.obj γ)) (Sigma.snd (t.sec.toFunctor.obj γ''))))
    (t.sec.toFunctor.map_comp f g)

/-- The term of the constant type at `K` with the values of a functor `Γ ⥤ K`. -/
def ofConst (F : Γ ⥤ K) : Tm(Γ, constTy Γ K) :=
  tmMk (fun γ => F.obj γ) (fun f => F.map f) (fun γ => F.map_id γ) fun f g => F.map_comp f g

theorem toConst_ofConst (F : Γ ⥤ K) : toConst (ofConst F) = F :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- A term of a constant type is that of its values: the first component of `t.sec γ` is `γ`, by
`t.sec_proj`. -/
theorem ofConst_toConst (t : Tm(Γ, constTy Γ K)) : ofConst (toConst t) = t := by
  have h := congrArg Cat.Hom.toFunctor t.sec_proj
  have hobj : ∀ γ : Γ, (ofConst (toConst t)).sec.toFunctor.obj γ = t.sec.toFunctor.obj γ :=
    fun γ => Sigma.ext (Functor.congr_obj h γ).symm HEq.rfl
  exact Tm.ext (Cat.Hom.ext (Functor.hext hobj fun _ _ f =>
    Total.Hom.hext (hobj _) (hobj _) (Functor.hcongr_hom h f).symm HEq.rfl))

/-- **The terms of the constant type at `K` are the functors `Γ ⥤ K`.** -/
def constEquiv : Tm(Γ, constTy Γ K) ≃ (Γ ⥤ K) where
  toFun := toConst
  invFun := ofConst
  left_inv := ofConst_toConst
  right_inv := toConst_ofConst

/-- The values in `K` of morphisms of `Γ ⋉⁻ constTy Γ K` respect heterogeneous equality. -/
theorem fiber_heq {p p' q q' : Γ ⋉⁻ constTy Γ K} (hp : p = p') (hq : q = q') {F : p ⟶ q}
    {G : p' ⟶ q'} (h : F ≍ G) :
    (Total.Hom.fiber F : @Quiver.Hom K _ (Sigma.snd p) (Sigma.snd q)) ≍
      (Total.Hom.fiber G : @Quiver.Hom K _ (Sigma.snd p') (Sigma.snd q')) := by
  subst hp hq
  cases eq_of_heq h
  rfl

/-- `toConst` commutes with substitution: `𝐪(σ, constTy Γ K)` keeps the values, and the
substituted term is over `t` along it. -/
theorem toConst_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, constTy Γ K)) :
    toConst (Γ := Δ) t⦃σ⦄ = σ.toFunctor ⋙ toConst t := by
  have h := congrArg Cat.Hom.toFunctor (Displayed.Tm.pull_sec_q σ t)
  exact Functor.hext
    (fun δ => congrArg (fun p : Γ ⋉⁻ constTy Γ K => @id K (Sigma.snd p)) (Functor.congr_obj h δ))
    fun δ δ' f => fiber_heq (Functor.congr_obj h δ) (Functor.congr_obj h δ')
      (Functor.hcongr_hom h f)

/-- `ofConst` commutes with substitution. -/
theorem ofConst_pull (σ : Δ ⟶ Γ) (F : Γ ⥤ K) :
    (ofConst F)⦃σ⦄ = ofConst (σ.toFunctor ⋙ F) :=
  (ofConst_toConst (Γ := Δ) (ofConst F)⦃σ⦄).symm.trans (congrArg ofConst
    ((toConst_pull σ (ofConst F)).trans (congrArg (σ.toFunctor ⋙ ·) (toConst_ofConst F))))

end Tm

/-! ## Terms as sections -/

/-- The section of the unstraightening of `A` given by a term: its values, transported along the
equalities of their first components with the points of `Γ`. -/
def Tm.toSection {A : ICatOpLax.{u, u}.Ty Γ} (t : Tm(Γ, A)) : (∫⁻ A).Section :=
  Section.ofFunctor t.sec.toFunctor (congrArg Cat.Hom.toFunctor t.sec_proj)

/-- The term of a section of the unstraightening of `A`. -/
def Tm.ofSection {A : ICatOpLax.{u, u}.Ty Γ} (S : (∫⁻ A).Section) : Tm(Γ, A) where
  sec := S.total.toCatHom
  sec_proj := rfl

/-- **The terms of `A` are the sections of its unstraightening.** -/
def Tm.sectionEquiv {A : ICatOpLax.{u, u}.Ty Γ} : Tm(Γ, A) ≃ (∫⁻ A).Section where
  toFun := Tm.toSection
  invFun := Tm.ofSection
  left_inv _ := Tm.ext (Cat.Hom.ext (Section.total_ofFunctor _ _))
  right_inv S := Section.ofFunctor_total S


end ComprehensionCategory.CatOpModel
