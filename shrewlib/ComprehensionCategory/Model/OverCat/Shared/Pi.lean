import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.Model.OverCat.CatOp.Term
import ComprehensionCategory.TypeFormers.Pi
import Displayed.Fibration.Straightening.Pi

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

/-- The two factorizations of `(g, A g φ')` in the total category of `∫⁻ A`, through
`(γ, A g y')` and through `(γ', x')`. -/
theorem totalClift_comm {γ γ' : Γ} (g : γ ⟶ γ') {x' y' : A.obj (op γ')} (φ' : x' ⟶ y') :
    (fibreIncl A γ).toFunctor.map ((A.map g.op).toFunctor.map φ') ≫ (∫⁻ A).totalClift g y' =
      (∫⁻ A).totalClift g x' ≫ (fibreIncl A γ').toFunctor.map φ' := by
  kernel_rfl'

/-- `B` sends the two factorizations of `(g, A g φ')` to the same functor: the transport of
`b : B (γ, A g x')` along `(g, 𝟙)` then `(𝟙, φ')` is that along `(𝟙, A g φ')` then `(g, 𝟙)`. The
rules for `B` split `B` of each composite into a different composite, so this is propositional. -/
theorem push_eq {γ γ' : Γ} (g : γ ⟶ γ') {x' y' : A.obj (op γ')} (φ' : x' ⟶ y')
    (b : B.obj ((∫⁻ A).tot ((A.map g.op).toFunctor.obj x'))) :
    (B.map ((fibreIncl A γ').toFunctor.map φ')).toFunctor.obj
        ((B.map ((∫⁻ A).totalClift g x')).toFunctor.obj b) =
      (B.map ((∫⁻ A).totalClift g y')).toFunctor.obj
        ((B.map ((fibreIncl A γ).toFunctor.map ((A.map g.op).toFunctor.map φ'))).toFunctor.obj b) :=
  (congrArg (fun F : (∫⁻ A).tot ((A.map g.op).toFunctor.obj x') ⟶ (∫⁻ A).tot y' =>
    (B.map F).toFunctor.obj b) (totalClift_comm g φ')).symm

/-- The transport of a section `s` over `A γ` along `g : γ ⟶ γ'`, a section over `A γ'`: its
value at `x'` is that of `s` at `A g x'`, transported along the chosen lift `(g, 𝟙)`, and its
transport along `φ'` is the image of that of `s` along `A g φ'`, after `push_eq`. -/
def pushObj {γ γ' : Γ} (g : γ ⟶ γ') (s : PiFib A B γ) : PiFib A B γ' where
  obj x' := (B.map ((∫⁻ A).totalClift g x')).toFunctor.obj (s.obj ((A.map g.op).toFunctor.obj x'))
  map {_ y'} φ' := eqToHom (push_eq g φ' _) ≫
    (B.map ((∫⁻ A).totalClift g y')).toFunctor.map (s.map ((A.map g.op).toFunctor.map φ'))
  map_id x' := by
    have h := congrArg (fun m => eqToHom (push_eq g (𝟙 x') (s.obj ((A.map g.op).toFunctor.obj x')))
      ≫ (B.map ((∫⁻ A).totalClift g x')).toFunctor.map m) (s.map_id ((A.map g.op).toFunctor.obj x'))
    kernel_exact h.trans (eqToHom_refl _ _)
  map_comp {x' y' z'} φ' ψ' := by
    -- The two composite functors from `B (γ, A g y')` to `B (γ', z')` agree.
    have hF := congrArg (fun F : (∫⁻ A).tot ((A.map g.op).toFunctor.obj y') ⟶ (∫⁻ A).tot z' =>
      (B.map F).toFunctor) (totalClift_comm g ψ')
    have h₁ := Functor.congr_hom hF (s.map ((A.map g.op).toFunctor.map φ'))
    have h₂ := congrArg (fun m => eqToHom (push_eq g (φ' ≫ ψ') (s.obj ((A.map g.op).toFunctor.obj x')))
      ≫ (B.map ((∫⁻ A).totalClift g z')).toFunctor.map m)
      (s.map_comp ((A.map g.op).toFunctor.map φ') ((A.map g.op).toFunctor.map ψ'))
    have h₃ := (eqToHom_trans (push_eq g (φ' ≫ ψ') (s.obj ((A.map g.op).toFunctor.obj x')))
      (Functor.congr_obj hF _)).trans
      (eqToHom_map (B.map ((fibreIncl A γ').toFunctor.map ψ')).toFunctor
        (push_eq g φ' (s.obj ((A.map g.op).toFunctor.obj x')))).symm
    kernel_exact h₂.trans ((congrArg (fun m => eqToHom (push_eq g (φ' ≫ ψ')
      (s.obj ((A.map g.op).toFunctor.obj x'))) ≫ m ≫ (B.map ((∫⁻ A).totalClift g z')).toFunctor.map
        (s.map ((A.map g.op).toFunctor.map ψ'))) h₁).trans
      (congrArg (· ≫ (B.map ((∫⁻ A).totalClift g y') ≫
          B.map ((fibreIncl A γ').toFunctor.map ψ')).toFunctor.map
          (s.map ((A.map g.op).toFunctor.map φ')) ≫
          eqToHom (push_eq g ψ' (s.obj ((A.map g.op).toFunctor.obj y'))) ≫
          (B.map ((∫⁻ A).totalClift g z')).toFunctor.map (s.map ((A.map g.op).toFunctor.map ψ')))
        h₃))

/-- The transport of a morphism of sections along `g`: the images of its components along the chosen
lifts `(g, 𝟙)`. -/
def pushHom {γ γ' : Γ} (g : γ ⟶ γ') {s t : PiFib A B γ} (α : s ⟶ t) : pushObj g s ⟶ pushObj g t where
  app x' := (B.map ((∫⁻ A).totalClift g x')).toFunctor.map (α.app ((A.map g.op).toFunctor.obj x'))
  naturality {x' y'} φ' := by
    have hF := congrArg (fun F : (∫⁻ A).tot ((A.map g.op).toFunctor.obj x') ⟶ (∫⁻ A).tot y' =>
      (B.map F).toFunctor) (totalClift_comm g φ')
    have h₁ := Functor.congr_hom hF (α.app ((A.map g.op).toFunctor.obj x'))
    have hn := congrArg (B.map ((∫⁻ A).totalClift g y')).toFunctor.map
      (α.naturality ((A.map g.op).toFunctor.map φ'))
    have h₃ := (eqToHom_trans (push_eq g φ' (s.obj ((A.map g.op).toFunctor.obj x')))
      (Functor.congr_obj hF (s.obj ((A.map g.op).toFunctor.obj x')))).trans (eqToHom_refl _ _)
    kernel_exact (congrArg (eqToHom (push_eq g φ' (s.obj ((A.map g.op).toFunctor.obj x'))) ≫ ·)
      hn).trans ((congrArg (fun m => eqToHom (push_eq g φ' (s.obj ((A.map g.op).toFunctor.obj x')))
        ≫ m ≫ (B.map ((∫⁻ A).totalClift g y')).toFunctor.map
          (t.map ((A.map g.op).toFunctor.map φ'))) h₁).trans
      (congrArg (· ≫ (B.map ((∫⁻ A).totalClift g x') ≫
          B.map ((fibreIncl A γ').toFunctor.map φ')).toFunctor.map
          (α.app ((A.map g.op).toFunctor.obj x')) ≫
          eqToHom (push_eq g φ' (t.obj ((A.map g.op).toFunctor.obj x'))) ≫
          (B.map ((∫⁻ A).totalClift g y')).toFunctor.map (t.map ((A.map g.op).toFunctor.map φ')))
        h₃))

/-- The transport of the sections over `A γ` along `g`, a functor to the sections over `A γ'`. -/
def pushFunctor {γ γ' : Γ} (g : γ ⟶ γ') : PiFib A B γ ⥤ PiFib A B γ' where
  obj s := pushObj g s
  map α := pushHom g α
  map_id _ := Section.Hom.ext fun _ => rfl
  map_comp _ _ := Section.Hom.ext fun _ => rfl

/-- A morphism preceded by an `eqToHom` is heterogeneously equal to it. -/
theorem eqToHom_comp_heq {C : Type u} [Category.{u} C] {X Y Z : C} (h : X = Y) (f : Y ⟶ Z) :
    eqToHom h ≫ f ≍ f := by
  subst h
  exact heq_of_eq (Category.id_comp f)

/-- Transport along the identity is the identity. -/
theorem pushObj_id {γ : Γ} (s : PiFib A B γ) : pushObj (𝟙 γ) s = s :=
  Section.ext (fun _ => by kernel_rfl') fun {x _} φ => by
    kernel_exact eqToHom_comp_heq (push_eq (𝟙 γ) φ (s.obj x)) (s.map φ)

/-- Transport along a composite is the composite of the transports. -/
theorem pushObj_comp {γ γ' γ'' : Γ} (g : γ ⟶ γ') (g' : γ' ⟶ γ'') (s : PiFib A B γ) :
    pushObj (g ≫ g') s = pushObj g' (pushObj g s) :=
  Section.ext (fun _ => by kernel_rfl') fun {x y} φ => by
    have h := (congrArg (eqToHom (push_eq g' φ ((pushObj g s).obj ((A.map g'.op).toFunctor.obj x)))
      ≫ ·) (eqToHom_map (B.map ((∫⁻ A).totalClift g' y)).toFunctor
        (push_eq g ((A.map g'.op).toFunctor.map φ)
          (s.obj ((A.map g.op).toFunctor.obj ((A.map g'.op).toFunctor.obj x)))))).trans
      (eqToHom_trans _ _)
    kernel_exact heq_of_eq (congrArg (· ≫ (B.map ((∫⁻ A).totalClift g' y)).toFunctor.map
      ((B.map ((∫⁻ A).totalClift g ((A.map g'.op).toFunctor.obj y))).toFunctor.map
        (s.map ((A.map g.op).toFunctor.map ((A.map g'.op).toFunctor.map φ))))) h.symm)

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

end ComprehensionCategory.OverCat
