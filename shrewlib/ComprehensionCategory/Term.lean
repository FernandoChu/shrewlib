import ComprehensionCategory.Basic

/-!
# Terms in a comprehension category

The terms of a type `A` in context `Γ`, `Tm(Γ, A)`, are the sections of its projection: the
morphisms `t.sec : Γ ⟶ Γ ▹ A` with `t.sec ≫ 𝐩 A = 𝟙 Γ`.

The substitution `t⦃σ⦄ : Tm(Δ, A⦃σ⦄)` of a term along `σ : Δ ⟶ Γ` (`Tm.pull`) is the
factorization of `σ ≫ t.sec` through the pullback square of `𝐪(σ, A)`: it is the unique section
`s` of `𝐩 A⦃σ⦄` with `s.sec ≫ 𝐪(σ, A) = σ ≫ t.sec` (`Tm.pull_sec_q`, `Tm.pull_unique`). The
factorization is given by the cartesian morphism of `cod C` that the comprehension functor sends
the chosen lift of `σ` at `A` to, as data, so that it computes. Over a split comprehension
category, substitution of terms is functorial (`Tm.pull_id`, `Tm.pull_comp`), as `𝐪(𝟙 Γ, A)` and
`𝐪(τ ≫ σ, A)` are `𝟙` and `𝐪(τ, A⦃σ⦄) ≫ 𝐪(σ, A)` by the rules for the chosen lifts.

A term can be transported along an equality of types (`Tm.castTy`), with the same section up to
heterogeneous equality. A morphism `σ : Δ ⟶ Γ` extends by a term `t : Tm(Δ, A⦃σ⦄)` to the morphism
`consSec σ t = t.sec ≫ 𝐪(σ, A) : Δ ⟶ Γ ▹ A` over `σ` (`consSec_proj`): with `σ` the section of a
term `b : Tm(Γ, A)`, this pairs `b` with a term of a type in context `Γ ▹ A`. Over a split
comprehension category, extension commutes with precomposition (`comp_consSec`) and with the
morphisms `𝐪` (`consSec_comp_q`), and it respects heterogeneously equal terms over equal morphisms
(`consSec_congr`).

Conversely, the terms of `A⦃σ⦄` are the morphisms `Δ ⟶ Γ ▹ A` over `σ`, by extension and
factorization through the pullback square of `𝐪(σ, A)` (`Tm.liftEquiv`), so that two terms are
equal if their extensions are (`Tm.sec_heq_of_consSec`). Hence the sections of the projection
`Γ ▹ A ▹ T ⟶ Γ`, for types `A` and `T` of two comprehension categories, are the pairs of a term `x`
of `A` and a term of `T⦃x⦄` (`Tm.sigmaEquiv`), and the sections of a context isomorphic to
`Γ ▹ A` over `Γ` are the terms of `A` (`Tm.equivOfIso`).

The notation `Tm(Γ, A)` for `D.Tm A`, for `A` over `Γ`, is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`. As there, the comprehension category `D` is inferred from the type
of `A`. The notation `t⦃σ⦄` for `t.pull σ` is that of the substitution of types, `A⦃σ⦄`, whose
elaborator tells them apart by the type of `t`.
-/

universe v u v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- The terms of the type `A` in context `Γ`: the sections of its projection `𝐩 A`. -/
@[ext]
structure Tm (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] {Γ : C} (A : D.Ty Γ) where
  /-- The section. -/
  sec : Γ ⟶ Γ ▹ A
  /-- It is a section of the projection. -/
  sec_proj : sec ≫ 𝐩 A = 𝟙 Γ

/-- `Tm(Γ, A)` is the type `D.Tm A` of the terms of the type `A` in context `Γ`. -/
scoped notation "Tm(" ctx ", " ty ")" => Displayed.Tm _ (Γ := ctx) ty

open Lean PrettyPrinter Delaborator SubExpr in
/-- Displays `D.Tm A`, for `A` over `Γ`, as `Tm(Γ, A)`. -/
@[scoped delab app.Displayed.Tm]
def delabTm : Delab := whenPPOption getPPNotation <| withOverApp 7 do
  let Γ ← withNaryArg 5 delab
  let A ← withNaryArg 6 delab
  `(Tm($Γ, $A))

namespace Tm

variable {D : Displayed.{v₂, u₂} C} [Fib D] [Comprehension D] {Δ Γ : C} (σ : Δ ⟶ Γ)
  {A : D.Ty Γ}

/-- `σ ≫ t.sec`, as a morphism of `cod C` over `σ` from the identity of `Δ` to the projection of
`A`: what the substitution of `t` along `σ` factors. -/
def pullCone (t : Tm(Γ, A)) :
    (⟨Δ, 𝟙 Δ⟩ : (cod C).Ob Δ) ⟶[𝟙 Δ ≫ σ] (D.compr).obj A :=
  ⟨σ ≫ t.sec, congrArg (σ ≫ ·) t.sec_proj⟩

/-- **The substitution of a term** along `σ : Δ ⟶ Γ`: the factorization of `σ ≫ t.sec` through
the pullback square of `𝐪(σ, A)`. -/
def pull (t : Tm(Γ, A)) : Tm(Δ, A⦃σ⦄) where
  sec := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (pullCone σ t)).1
  sec_proj := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (pullCone σ t)).2

/-- Displays `t.pull σ` as `t⦃σ⦄`. -/
@[scoped app_unexpander Tm.pull]
def unexpandPull : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t⦃$σ⦄)
  | _ => throw ()

/-- The substituted term is over `t` along `𝐪(σ, A)`. -/
theorem pull_sec_q (t : Tm(Γ, A)) : t⦃σ⦄.sec ≫ 𝐪(σ, A) = σ ≫ t.sec :=
  congrArg Subtype.val ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_fac (𝟙 Δ)
    (pullCone σ t))

/-- `Tm.pull_sec_q`, followed by a morphism. -/
theorem pull_sec_q_assoc (t : Tm(Γ, A)) {X : C} (h : Γ ▹ A ⟶ X) :
    t⦃σ⦄.sec ≫ 𝐪(σ, A) ≫ h = σ ≫ t.sec ≫ h := by
  rw [← Category.assoc, pull_sec_q, Category.assoc]

/-- **The substituted term is the unique section over `t` along `𝐪(σ, A)`.** -/
theorem pull_unique (t : Tm(Γ, A)) (s : Tm(Δ, A⦃σ⦄)) (h : s.sec ≫ 𝐪(σ, A) = σ ≫ t.sec) :
    s = t⦃σ⦄ :=
  Tm.ext (congrArg Subtype.val ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_uniq
    (χ := pullCone σ t)
    (⟨s.sec, s.sec_proj⟩ : CodHom (𝟙 Δ) ⟨Δ, 𝟙 Δ⟩ ((D.compr).obj (D.pull σ A)))
    (CodHom.ext h)))

end Tm

namespace Tm

variable {D : Displayed.{v₂, u₂} C} [SplitComprehension D] {Γ : C} {A : D.Ty Γ}

/-- Substitution of terms along the identity is the identity. -/
theorem pull_id (t : Tm(Γ, A)) : t⦃𝟙 Γ⦄ = t :=
  (pull_unique (𝟙 Γ) t t rfl).symm

/-- Substitution of terms along a composite is the composite of the substitutions. -/
theorem pull_comp {Δ Θ : C} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (t : Tm(Γ, A)) :
    t⦃τ ≫ σ⦄ = t⦃σ⦄⦃τ⦄ :=
  (pull_unique (τ ≫ σ) t t⦃σ⦄⦃τ⦄
    (((congrArg (· ≫ 𝐪(σ, A)) (pull_sec_q τ t⦃σ⦄)).trans
      (congrArg (τ ≫ ·) (pull_sec_q σ t)) :))).symm

end Tm

/-! ## Transport and extension -/

section Cons

variable {D : Displayed.{v₂, u₂} C} [Fib D] [Comprehension D] {Δ Γ : C}

/-- The transport of a term along an equality of types. -/
def Tm.castTy {A B : D.Ty Γ} (h : A = B) (t : Tm(Γ, A)) : Tm(Γ, B) :=
  h ▸ t

/-- The transported term has the same section, up to heterogeneous equality. -/
theorem Tm.castTy_sec_heq {A B : D.Ty Γ} (h : A = B) (t : Tm(Γ, A)) :
    (t.castTy h).sec ≍ t.sec := by
  subst h
  rfl

/-- **The extension of `σ : Δ ⟶ Γ` by a term `t : Tm(Δ, A⦃σ⦄)`**, the morphism
`Δ ⟶ Γ ▹ A` over `σ` whose second component is `t`. -/
def consSec (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Δ, A⦃σ⦄)) : Δ ⟶ Γ ▹ A :=
  t.sec ≫ 𝐪(σ, A)

/-- The extension of `σ` lies over `σ`. -/
theorem consSec_proj (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Δ, A⦃σ⦄)) : consSec σ t ≫ 𝐩 A = σ := by
  rw [consSec, Category.assoc, D.q_proj σ A, ← Category.assoc, t.sec_proj, Category.id_comp]

/-- Extensions along equal morphisms by terms with heterogeneously equal sections are equal. -/
theorem consSec_congr {σ σ' : Δ ⟶ Γ} (hσ : σ = σ') {A : D.Ty Γ} {t : Tm(Δ, A⦃σ⦄)}
    {t' : Tm(Δ, A⦃σ'⦄)} (ht : t.sec ≍ t'.sec) : consSec σ t = consSec σ' t' := by
  subst hσ
  obtain rfl := Tm.ext (eq_of_heq ht)
  rfl

/-- The substitution of a transported term has the same section as that of the term, up to
heterogeneous equality. -/
theorem Tm.pull_castTy_sec_heq (σ : Δ ⟶ Γ) {A B : D.Ty Γ} (h : A = B) (t : Tm(Γ, A)) :
    (t.castTy h)⦃σ⦄.sec ≍ t⦃σ⦄.sec := by
  subst h
  rfl

end Cons

section ConsSplit

variable {D : Displayed.{v₂, u₂} C} [SplitComprehension D] {Θ Δ Γ : C}

/-- **Extension commutes with precomposition**: `τ ≫ consSec σ t = consSec (τ ≫ σ) t⦃τ⦄`. -/
theorem comp_consSec (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Δ, A⦃σ⦄)) :
    τ ≫ consSec σ t = consSec (τ ≫ σ) t⦃τ⦄ :=
  (congrArg (· ≫ 𝐪(σ, A)) (Tm.pull_sec_q τ t)).symm

/-- **Extension commutes with the morphisms `𝐪`**: `consSec τ t ≫ 𝐪(σ, A) = consSec (τ ≫ σ) t`,
where `t` is a term of `A⦃σ⦄⦃τ⦄`, that is of `A⦃τ ≫ σ⦄`. -/
theorem consSec_comp_q (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Θ, A⦃σ⦄⦃τ⦄)) :
    consSec τ t ≫ 𝐪(σ, A) = consSec (τ ≫ σ) t :=
  rfl

end ConsSplit

/-! ## Terms as morphisms -/

section Lift

variable {D : Displayed.{v₂, u₂} C} [Fib D] [Comprehension D] {Δ Γ : C}

/-- A morphism `s : Δ ⟶ Γ ▹ A` over `σ`, as a morphism of `cod C` over `σ` from the identity of
`Δ` to the projection of `A`. -/
def Tm.liftCone (σ : Δ ⟶ Γ) {A : D.Ty Γ} (s : Δ ⟶ Γ ▹ A) (h : s ≫ 𝐩 A = σ) :
    (⟨Δ, 𝟙 Δ⟩ : (cod C).Ob Δ) ⟶[𝟙 Δ ≫ σ] (D.compr).obj A :=
  ⟨s, h⟩

/-- The term of `A⦃σ⦄` of a morphism `s : Δ ⟶ Γ ▹ A` over `σ`: its factorization through the
pullback square of `𝐪(σ, A)`. -/
def Tm.ofLift (σ : Δ ⟶ Γ) {A : D.Ty Γ} (s : Δ ⟶ Γ ▹ A) (h : s ≫ 𝐩 A = σ) : Tm(Δ, A⦃σ⦄) where
  sec := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (Tm.liftCone σ s h)).1
  sec_proj := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (Tm.liftCone σ s h)).2

/-- **The terms of `A⦃σ⦄` are the morphisms `Δ ⟶ Γ ▹ A` over `σ`**, by extension (`consSec`) and
factorization through the pullback square of `𝐪(σ, A)`. -/
def Tm.liftEquiv (σ : Δ ⟶ Γ) (A : D.Ty Γ) :
    Tm(Δ, A⦃σ⦄) ≃ {s : Δ ⟶ Γ ▹ A // s ≫ 𝐩 A = σ} where
  toFun t := ⟨consSec σ t, consSec_proj σ t⟩
  invFun s := Tm.ofLift σ s.1 s.2
  left_inv t := (Tm.ext (congrArg Subtype.val
    ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_uniq
      (χ := Tm.liftCone σ (consSec σ t) (consSec_proj σ t))
      (⟨t.sec, t.sec_proj⟩ : CodHom (𝟙 Δ) ⟨Δ, 𝟙 Δ⟩ ((D.compr).obj (D.pull σ A)))
      (CodHom.ext rfl)))).symm
  right_inv s := Subtype.ext (congrArg Subtype.val
    ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_fac (𝟙 Δ) (Tm.liftCone σ s.1 s.2)))

/-- The terms of `A` are the sections of its projection. -/
def Tm.secEquiv (A : D.Ty Γ) : Tm(Γ, A) ≃ {s : Γ ⟶ Γ ▹ A // s ≫ 𝐩 A = 𝟙 Γ} where
  toFun t := ⟨t.sec, t.sec_proj⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Terms across an isomorphism of contexts**: for `e : X ≅ Γ ▹ A` over `Γ`, the sections of the
projection `p : X ⟶ Γ` are the terms of `A`. -/
def Tm.equivOfIso {X : C} {p : X ⟶ Γ} {A : D.Ty Γ} (e : X ≅ Γ ▹ A) (he : e.hom ≫ 𝐩 A = p) :
    {s : Γ ⟶ X // s ≫ p = 𝟙 Γ} ≃ Tm(Γ, A) where
  toFun s := ⟨s.1 ≫ e.hom, (congrArg (s.1 ≫ ·) he).trans s.2⟩
  invFun t := ⟨t.sec ≫ e.inv, (congrArg (fun q => t.sec ≫ e.inv ≫ q) he.symm).trans
    ((congrArg (fun q => t.sec ≫ q ≫ 𝐩 A) e.inv_hom_id).trans t.sec_proj)⟩
  left_inv s := Subtype.ext (congrArg (s.1 ≫ ·) e.hom_inv_id)
  right_inv t := Tm.ext (congrArg (t.sec ≫ ·) e.inv_hom_id)

/-- Terms of `A` at equal morphisms are heterogeneously equal if their extensions are equal. -/
theorem Tm.sec_heq_of_consSec {A : D.Ty Γ} {r r' : Δ ⟶ Γ} (hr : r = r') {y : Tm(Δ, A⦃r⦄)}
    {y' : Tm(Δ, A⦃r'⦄)} (h : consSec r y = consSec r' y') : y.sec ≍ y'.sec := by
  subst hr
  obtain rfl := (Tm.liftEquiv r A).injective (Subtype.ext h)
  rfl

variable {E : Displayed.{v₃, u₃} C} [Fib E] [Comprehension E]

/-- **The pairs of a term `x` of `A` and a term of `T` at `x`**, for `T` a type of another
comprehension category in context `Γ ▹ A`, are the sections of the projection
`Γ ▹ A ▹ T ⟶ Γ`. -/
def Tm.sigmaEquiv (A : D.Ty Γ) (T : E.Ty (Γ ▹ A)) :
    (Σ x : Tm(Γ, A), Tm(Γ, T⦃x.sec⦄)) ≃ {s : Γ ⟶ Γ ▹ A ▹ T // s ≫ 𝐩 T ≫ 𝐩 A = 𝟙 Γ} :=
  (Equiv.sigmaCongrRight fun x : Tm(Γ, A) => Tm.liftEquiv x.sec T).trans
    { toFun p := ⟨p.2.1, (congrArg (· ≫ 𝐩 A) p.2.2).trans p.1.sec_proj⟩
      invFun s := ⟨⟨s.1 ≫ 𝐩 T, s.2⟩, ⟨s.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨x, _⟩, s, h⟩
        dsimp only at h
        subst h
        rfl
      right_inv _ := rfl }

end Lift

end Displayed
