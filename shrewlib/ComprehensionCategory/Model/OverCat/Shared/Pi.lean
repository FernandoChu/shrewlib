import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.Model.OverCat.CatOp.Term
import ComprehensionCategory.TypeFormers.Pi
import Displayed.Fibration.Straightening.Pi

/-!
# Π-types of the category model over the contravariant one

For a type `A : Γᵒᵖ ⥤ Cat` of the contravariant category model and a type `B : Γ ⋉ A ⥤ Cat` of the
category model in context `Γ ▹ A`, the total category of `∫⁻ A`, the Π-type `Π[A] B` is the
functor `piFunctor A B : Γ ⥤ Cat`:

* its value at `γ` is the category of sections of `∫ B` over the fibre `A γ` (`PiFib`), the
  functors `s` choosing `s x : B (γ, x)` and `s φ : B (𝟙, φ) (s x) ⟶ s x'`, with the vertical
  natural transformations;
* its action along `g : γ ⟶ γ'` transports a section along the chosen lifts `(g, 𝟙)`
  (`pushObj`): `x' ↦ B (g, 𝟙) (s (A g x'))`. That the transport of `s φ'` has the right type is
  the rule `obj_totalClift_fibreIncl` of `Displayed/Fibration/Straightening/Pi`.

It is stable under substitution by `rfl`, checked in the kernel (`pull_piTy`), so it is a rule
through `PrePi.pull_pi`. This is where `A` must be contravariant: a section over `A γ` is
transported along `A g : A γ' ⥤ A γ`.

The sections of the unstraightening of `Π[A] B` are those of the dependent product
`piDisp A (∫ B)` (`piFunctorSectionEquiv`), whose sections are those of `∫ B` over `Γ ⋉ A`
(`piSectionEquiv`), which are the terms of `B` (`CatModel.Tm.sectionEquiv`). Abstraction
`piLam` and application `piApp` are these bijections, so they are inverse. Abstraction is stable
under substitution (`piLam_pull`): the section of `t⦃𝐪(σ, A)⦄` restricted to the fibre at `δ` is
that of `t` at `σ δ`, and so are their transports. Hence `HasPi ICatOpLax ICatLax` (`hasPi`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Opposite Displayed Displayed.Fibration.Straightening

open scoped Displayed

open Displayed.Opfibration.Straightening (unstraightenObj)

variable {Γ : Cat.{u, u}} (A : Γᵒᵖ ⥤ Cat.{u, u}) (B : (∫⁻ A).Total ⥤ Cat.{u, u})

/-- The unstraightening of `B`, displayed over the total category of `∫⁻ A`. -/
abbrev piE : Displayed.{u, u} (∫⁻ A).Total := unstraightenObj (A := Cat.of (∫⁻ A).Total) B

/-- The fibre of the Π-type at `γ`: the sections of `B` over `A γ`. -/
abbrev PiFib (γ : Γ) : Type u := (fibreDisp A (piE A B) γ).Section

variable {A B}

/-- The transport of a section `s` over `A γ` along `g : γ ⟶ γ'`, a section over `A γ'`: its
value at `x'` is that of `s` at `A g x'`, transported along the chosen lift `(g, 𝟙)`, and its
transport along `φ'` is the image of that of `s` along `A g φ'`. That image lies over
`(𝟙, A g φ') ≫ (g, 𝟙)`, and the rules `obj_totalClift_fibreIncl` and `map_totalClift_fibreIncl`
make it a morphism over `(g, 𝟙) ≫ (𝟙, φ')`, as required. -/
def pushObj {γ γ' : Γ} (g : γ ⟶ γ') (s : PiFib A B γ) : PiFib A B γ' where
  obj x' := (B.map ((∫⁻ A).totalClift g x')).toFunctor.obj (s.obj ((A.map g.op).toFunctor.obj x'))
  map {_ y'} φ' :=
    (B.map ((∫⁻ A).totalClift g y')).toFunctor.map (s.map ((A.map g.op).toFunctor.map φ'))
  map_id x' := by
    kernel_exact congrArg (B.map ((∫⁻ A).totalClift g x')).toFunctor.map
      (s.map_id ((A.map g.op).toFunctor.obj x'))
  map_comp {_ _ z'} φ' ψ' := by
    kernel_exact congrArg (B.map ((∫⁻ A).totalClift g z')).toFunctor.map
      (s.map_comp ((A.map g.op).toFunctor.map φ') ((A.map g.op).toFunctor.map ψ'))

/-- The transport of a morphism of sections along `g`: the images of its components along the chosen
lifts `(g, 𝟙)`. -/
def pushHom {γ γ' : Γ} (g : γ ⟶ γ') {s t : PiFib A B γ} (α : s ⟶ t) :
    pushObj g s ⟶ pushObj g t where
  app x' := (B.map ((∫⁻ A).totalClift g x')).toFunctor.map (α.app ((A.map g.op).toFunctor.obj x'))
  naturality {_ y'} φ' := by
    kernel_exact congrArg (B.map ((∫⁻ A).totalClift g y')).toFunctor.map
      (α.naturality ((A.map g.op).toFunctor.map φ'))

/-- The transport of the sections over `A γ` along `g`, a functor to the sections over `A γ'`. -/
def pushFunctor {γ γ' : Γ} (g : γ ⟶ γ') : PiFib A B γ ⥤ PiFib A B γ' where
  obj s := pushObj g s
  map α := pushHom g α
  map_id _ := Section.Hom.ext fun _ => rfl
  map_comp _ _ := Section.Hom.ext fun _ => rfl

/-- Transport along the identity is the identity. -/
theorem pushObj_id {γ : Γ} (s : PiFib A B γ) : pushObj (𝟙 γ) s = s :=
  Section.ext (fun _ => by kernel_rfl') fun _ => by kernel_rfl'

/-- Transport along a composite is the composite of the transports. -/
theorem pushObj_comp {γ γ' γ'' : Γ} (g : γ ⟶ γ') (g' : γ' ⟶ γ'') (s : PiFib A B γ) :
    pushObj (g ≫ g') s = pushObj g' (pushObj g s) :=
  Section.ext (fun _ => by kernel_rfl') fun _ => by kernel_rfl'

variable (A B) in
/-- **The Π-type** of `B` over `A`: the functor sending `γ` to the category of sections of `B` over
`A γ`, and `g` to the transport along `g`. -/
def piFunctor : Γ ⥤ Cat.{u, u} where
  obj γ := Cat.of (PiFib A B γ)
  map g := (pushFunctor g).toCatHom
  map_id _ := Cat.Hom.ext (Functor.hext pushObj_id fun s t _ =>
    Section.Hom.hext (pushObj_id s) (pushObj_id t) fun _ => HEq.rfl)
  map_comp g g' := Cat.Hom.ext (Functor.hext (pushObj_comp g g') fun s t _ =>
    Section.Hom.hext (pushObj_comp g g' s) (pushObj_comp g g' t) fun _ => HEq.rfl)

/-! ## Sections -/

open Displayed.Opfibration.Straightening in
/-- The section of `piDisp` of a section of the unstraightening of the Π-type: the same objects, and
the components of its morphisms, which are morphisms of sections from the transported ones. -/
def toPiSection (S : (unstraightenObj (piFunctor A B)).Section) :
    (piDisp A (piE A B)).Section where
  obj γ := S.obj γ
  map g := ⟨fun x' => (S.map g).app x', fun φ' => by kernel_exact (S.map g).naturality φ'⟩
  map_id γ := PiHom.ext fun x => by
    kernel_exact congrArg (fun h => Section.Hom.app h x) (S.map_id γ)
  map_comp g g' := PiHom.ext fun x => by
    kernel_exact congrArg (fun h => Section.Hom.app h x) (S.map_comp g g')

open Displayed.Opfibration.Straightening in
/-- The section of the unstraightening of the Π-type of a section of `piDisp`. -/
def ofPiSection' (T : (piDisp A (piE A B)).Section) :
    (unstraightenObj (piFunctor A B)).Section where
  obj γ := T.obj γ
  map g := ⟨fun x' => (T.map g).app x', fun φ' => by kernel_exact (T.map g).naturality φ'⟩
  map_id γ := Section.Hom.ext fun x => by
    kernel_exact congrArg (fun h => PiHom.app h x) (T.map_id γ)
  map_comp g g' := Section.Hom.ext fun x => by
    kernel_exact congrArg (fun h => PiHom.app h x) (T.map_comp g g')

open Displayed.Opfibration.Straightening in
/-- **The sections of the unstraightening of the Π-type are those of `piDisp`.** -/
def piFunctorSectionEquiv :
    (unstraightenObj (piFunctor A B)).Section ≃ (piDisp A (piE A B)).Section where
  toFun := toPiSection
  invFun := ofPiSection'
  left_inv _ := Section.ext (fun _ => rfl) fun _ => HEq.rfl
  right_inv _ := Section.ext (fun _ => rfl) fun _ => HEq.rfl

/-! ## Π-types -/

section Model

variable {Γ : Cat.{u, u}} (A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ)
  (B : Opfibration.Straightening.ICatLax.{u, u}.Ty (Γ ▹ A))

/-- **The Π-type** of `B` over `A`, a type of the category model. -/
def piTy : Opfibration.Straightening.ICatLax.{u, u}.Ty Γ :=
  piFunctor A B

/-- The Π-type is stable under substitution, by `rfl` in the kernel. -/
theorem pull_piTy {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) :
    Fib.pull σ (piTy A B) = piTy (Fib.pull σ A) (Fib.pull 𝐪(σ, A) B) := by
  kernel_rfl'

end Model

/-- The Π-types of the category model over the contravariant one, stable under substitution. -/
instance prePi : PrePi Fibration.Straightening.ICatOpLax.{u, u, u, u}
    Opfibration.Straightening.ICatLax.{u, u, u, u} where
  pi A B := piTy A B
  pull_pi σ A B := pull_piTy A B σ

section Model

variable {Γ : Cat.{u, u}} {A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ}
  {B : Opfibration.Straightening.ICatLax.{u, u}.Ty (Γ ▹ A)}

/-- **Abstraction**: a term of `B` in context `Γ ▹ A` as a term of the Π-type, through the
sections of `B`, of `piDisp` and of the Π-type. -/
def piLam (t : Tm(Γ ▹ A, B)) : Tm(Γ, piTy A B) :=
  CatModel.Tm.ofSection (ofPiSection' (piSection (CatModel.Tm.toSection t)))

/-- **Application**: a term of the Π-type as a term of `B` in context `Γ ▹ A`. -/
def piApp (t : Tm(Γ, piTy A B)) : Tm(Γ ▹ A, B) :=
  CatModel.Tm.ofSection (ofPiSection (toPiSection (CatModel.Tm.toSection t)))

/-- Application after abstraction is the identity. -/
theorem piApp_piLam (t : Tm(Γ ▹ A, B)) : piApp (piLam t) = t :=
  calc piApp (piLam t)
      = CatModel.Tm.ofSection (ofPiSection (toPiSection
          (ofPiSection' (piSection (CatModel.Tm.toSection t))))) :=
        congrArg (fun X => CatModel.Tm.ofSection (ofPiSection (toPiSection X)))
          (CatModel.Tm.sectionEquiv.right_inv _)
    _ = CatModel.Tm.ofSection (ofPiSection (piSection (CatModel.Tm.toSection t))) :=
        congrArg (fun Y => CatModel.Tm.ofSection (ofPiSection Y))
          (piFunctorSectionEquiv.right_inv _)
    _ = CatModel.Tm.ofSection (CatModel.Tm.toSection t) :=
        congrArg CatModel.Tm.ofSection (ofPiSection_piSection _)
    _ = t := CatModel.Tm.sectionEquiv.left_inv t

/-- Abstraction after application is the identity. -/
theorem piLam_piApp (t : Tm(Γ, piTy A B)) : piLam (piApp t) = t :=
  calc piLam (piApp t)
      = (CatModel.Tm.ofSection (ofPiSection' (piSection
          (ofPiSection (toPiSection (CatModel.Tm.toSection t))))) : Tm(Γ, piTy A B)) :=
        congrArg (fun X => CatModel.Tm.ofSection (ofPiSection' (piSection X)))
          (CatModel.Tm.sectionEquiv.right_inv _)
    _ = (CatModel.Tm.ofSection (ofPiSection' (toPiSection (CatModel.Tm.toSection t))) :
          Tm(Γ, piTy A B)) :=
        congrArg (fun Y => CatModel.Tm.ofSection (ofPiSection' Y)) (piSection_ofPiSection _)
    _ = (CatModel.Tm.ofSection (CatModel.Tm.toSection t) : Tm(Γ, piTy A B)) :=
        congrArg CatModel.Tm.ofSection (piFunctorSectionEquiv.left_inv _)
    _ = t := CatModel.Tm.sectionEquiv.left_inv t

/-- The fibres of the Π-type of `A⦃σ⦄` and `B⦃𝐪(σ, A)⦄` at `δ` are those of the Π-type of `A` and
`B` at `σ δ`. -/
theorem fibreDisp_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (δ : Δ) :
    fibreDisp (Fib.pull σ A) (piE (Fib.pull σ A) (Fib.pull 𝐪(σ, A) B)) δ =
      fibreDisp A (piE A B) (σ.toFunctor.obj δ) := by
  kernel_rfl'

/-- The restrictions to the fibres of the section of `t⦃𝐪(σ, A)⦄` are those of `t`, at the images
along `σ`. -/
theorem piSection_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ ▹ A, B)) (δ : Δ) :
    (piSection (CatModel.Tm.toSection t⦃𝐪(σ, A)⦄)).obj δ ≍
      (piSection (CatModel.Tm.toSection t)).obj (σ.toFunctor.obj δ) :=
  Section.hext (fibreDisp_pull σ δ) (fun x => by
    kernel_exact CatModel.Tm.toSection_pull_obj 𝐪(σ, A) t ((∫⁻ (Fib.pull σ A)).tot x))
    fun {_ _} φ => by
      kernel_exact CatModel.Tm.toSection_pull_map 𝐪(σ, A) t
        ((fibreIncl (Fib.pull σ A) δ).toFunctor.map φ)

/-- Heterogeneously equal functions, between equal types, send heterogeneously equal arguments to
heterogeneously equal values. -/
theorem apply_heq {α α' β β' : Type u} (hα : α = α') (hβ : β = β') {f : α → β} {g : α' → β'}
    (hf : f ≍ g) {a : α} {a' : α'} (ha : a ≍ a') : f a ≍ g a' := by
  subst hα hβ
  cases hf
  cases ha
  rfl

/-- The fibres of the Π-type of `A⦃σ⦄` and `B⦃𝐪(σ, A)⦄` are those of the Π-type of `A` and `B`. -/
theorem piFib_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (δ : Δ) :
    PiFib (Fib.pull σ A) (Fib.pull 𝐪(σ, A) B) δ = PiFib A B (σ.toFunctor.obj δ) := by
  kernel_rfl'

/-- The transport of the Π-type of `A⦃σ⦄` and `B⦃𝐪(σ, A)⦄` along `f` is that of the Π-type of `A`
and `B` along `σ f`. -/
theorem pushObj_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {δ δ' : Δ} (f : δ ⟶ δ') :
    pushObj (A := Fib.pull σ A) (B := Fib.pull 𝐪(σ, A) B) f ≍
      pushObj (A := A) (B := B) (σ.toFunctor.map f) := by
  kernel_rfl'

/-- The transports of the restricted sections of `t⦃𝐪(σ, A)⦄` along `f` are those of `t` along
`σ f`. -/
theorem pushObj_piSection_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ ▹ A, B)) {δ δ' : Δ}
    (f : δ ⟶ δ') :
    pushObj f ((piSection (CatModel.Tm.toSection t⦃𝐪(σ, A)⦄)).obj δ) ≍
      pushObj (σ.toFunctor.map f) ((piSection (CatModel.Tm.toSection t)).obj (σ.toFunctor.obj δ)) :=
  apply_heq (piFib_pull σ δ) (piFib_pull σ δ') (pushObj_pull σ f) (piSection_pull σ t δ)

/-- **Abstraction is stable under substitution**: by uniqueness of the substitution of terms, it
suffices that `piLam t⦃𝐪(σ, A)⦄` lies over `piLam t` along `𝐪(σ, Π[A] B)`, which holds since the
restricted sections of `t⦃𝐪(σ, A)⦄` and their transports are those of `t`. -/
theorem piLam_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ ▹ A, B)) :
    @Eq (Tm(Δ, (Π[A] B)⦃σ⦄)) (piLam t : Tm(Γ, Π[A] B))⦃σ⦄ (piLam t⦃𝐪(σ, A)⦄) := by
  refine (Displayed.Tm.pull_unique σ (piLam t) (piLam t⦃𝐪(σ, A)⦄) ?_).symm
  have hobj : ∀ δ : Δ,
      ((piLam t⦃𝐪(σ, A)⦄).sec ≫ 𝐪(σ, Π[A] B)).toFunctor.obj δ =
        (σ ≫ (piLam t).sec).toFunctor.obj δ := fun δ => by
    refine Sigma.ext ?_ ?_
    · kernel_rfl'
    · kernel_exact piSection_pull σ t δ
  have hmap : ∀ (δ δ' : Δ) (f : δ ⟶ δ'),
      ((piLam t⦃𝐪(σ, A)⦄).sec ≫ 𝐪(σ, Π[A] B)).toFunctor.map f ≍
        (σ ≫ (piLam t).sec).toFunctor.map f := fun δ δ' f => by
    refine Total.Hom.hext (hobj δ) (hobj δ') ?_ ?_
    · kernel_rfl'
    refine Section.Hom.hext_of_eq (fibreDisp_pull σ δ') (pushObj_piSection_pull σ t f)
      (piSection_pull σ t δ') ?hX ?hY fun x => ?_
    case hX => kernel_rfl'
    case hY => kernel_rfl'
    kernel_exact CatModel.Tm.toSection_pull_map 𝐪(σ, A) t ((∫⁻ (Fib.pull σ A)).totalClift f x)
  kernel_exact Cat.Hom.ext (Functor.hext hobj hmap)

end Model

/-- **The category model has Π-types over the contravariant one**: abstraction and application
are inverse, through the sections of `B` over the fibres of `A`, and stable under substitution. -/
instance hasPi : HasPi Fibration.Straightening.ICatOpLax.{u, u, u, u}
    Opfibration.Straightening.ICatLax.{u, u, u, u} where
  lam t := piLam t
  app t := piApp t
  app_lam t := piApp_piLam t
  lam_app t := piLam_piApp t
  lam_pull σ _ _ t := piLam_pull σ t

end ComprehensionCategory.OverCat
