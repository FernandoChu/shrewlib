import DoubleDisplayed.D2SFib.Fibred.DProf
import DoubleDisplayed.D2SFib.Fibred.D2SFibDisp
import DoubleDisplayed.D2SFib.Straightening.Unstraighten

/-!
# Unstraightening of dependent profunctors, over `ICatStr`

The unstraightening `Unstraightening P` of a dependent profunctor `P : (∫ F)ᵒᵖ.Total ⥤ Cat` is a
split D2SFib over `∫ F` (`DoubleDisplayed/D2SFib/Straightening/Unstraighten.lean`). Here we extend
it to the morphisms of dependent profunctors over arbitrary strict transformations, which makes it
natural in `A` and `F`: a natural transformation
`κ : P ⟶ τ.dualTotal ⋙ P'` gives the map of D2SFibs over `τ.unstraighten` with the components of
`κ` on objects and morphisms (`unstraightenMap`), and the unstraightening is a vertical functor
`unstraighten : VertFunctor DProf D2SFibDisp` over `ICatStr`.

As for the transformations between functors on the same category, the components of `κ` on
objects and morphisms have their own heads, `tobj` and `tmor`, and their naturality along the
chosen horizontal and vertical morphisms of `(∫ F)ᵒᵖ.Total` is a set of rules. Along
`dualHoriz α x` it is the transport `hobj` of `P'` along `u α`, and along `dualVert β` the
transport `vobj` of `P'` along `τ β`, since `τ.dualTotal` sends these chosen morphisms to the chosen
morphisms of `(∫ G)ᵒᵖ.Total` by `rfl`. The latter is stated with `τ.unstraighten β` rather than
`τ.map β`, its unfolding: a vertical identity or composite of `∫ F` goes to one of `∫ G` in the
form `B.id b` or `β ≫ᵈ γ` on which the rules of `Unstraightening` are keyed, while `τ.map` computes
it to `𝟙` or `≫` of `G`, which the kernel does not match against these keys. The components of a
composite `κ ≫ whiskerLeft τ.dualTotal κ'` are rules too, so that `tobj` and `tmor` are kept when
it is unfolded. With these rules, `unstraightenMap κ` is a functor and preserves the chosen lifts
by `rfl`.
-/

universe u

namespace DoubleDisplayed.D2SFib.Fibred

open CategoryTheory Displayed DoubleDisplayed D2SFib Displayed.Opfibration.Straightening
  DoubleDisplayed.D2SFib.Straightening DoubleDisplayed.D2SFib.Straightening.Unstraightening

open scoped Displayed DoubleDisplayed

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}}
  {τ : StrictTrans F (u.toFunctor ⋙ G)} {P : (∫ F)ᵒᵖ.Total ⥤ Cat.{u, u}}
  {P' : (∫ G)ᵒᵖ.Total ⥤ Cat.{u, u}}

/-! ## The components of a morphism of dependent profunctors -/

section Components

/-- The component of `κ : P ⟶ τ.dualTotal ⋙ P'`, on objects. -/
def tobj (κ : P ⟶ τ.dualTotal ⋙ P') {x : (∫ F)ᵒᵖ.Total} (c : P.obj x) :
    P'.obj (τ.dualTotal.obj x) :=
  (κ.app x).toFunctor.obj c

/-- The component of `κ : P ⟶ τ.dualTotal ⋙ P'`, on morphisms. -/
def tmor (κ : P ⟶ τ.dualTotal ⋙ P') {x : (∫ F)ᵒᵖ.Total} {c c' : P.obj x} (θ : c ⟶ c') :
    tobj κ c ⟶ tobj κ c' :=
  (κ.app x).toFunctor.map θ

variable (κ : P ⟶ τ.dualTotal ⋙ P') {a a' : A}

theorem tapp_hmap (α : a ⟶ a') (x : F.obj a) :
    hmap P α x ⋙ (κ.app ((∫ F)ᵒᵖ.tot ((∫ F).push α x))).toFunctor =
      (κ.app ((∫ F)ᵒᵖ.tot x)).toFunctor ⋙ hmap P' (u.toFunctor.map α) (τ.toObj.obj x) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualHoriz (B := ∫ F) α x))

theorem tapp_vmap {x y : F.obj a} (β : x ⟶ y) :
    vmap P (B := ∫ F) β ⋙ (κ.app _).toFunctor =
      (κ.app _).toFunctor ⋙ vmap P' (B := ∫ G) (τ.unstraighten.toPre.map (f := 𝟙 a) β) :=
  congrArg Cat.Hom.toFunctor (κ.naturality (dualVert (B := ∫ F) β))

theorem tmor_hmor_heq (α : a ⟶ a') (x : F.obj a) {c c' : P.obj ((∫ F)ᵒᵖ.tot x)} (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) ≍ hmor P' (u.toFunctor.map α) (τ.toObj.obj x) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_hmap κ α x) θ

theorem tmor_vmor_heq {x y : F.obj a} (β : x ⟶ y) {c c' : P.obj ((∫ F)ᵒᵖ.tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P (B := ∫ F) β θ) ≍
      vmor P' (B := ∫ G) (τ.unstraighten.toPre.map (f := 𝟙 a) β) (tmor κ θ) :=
  Functor.hcongr_hom (tapp_vmap κ β) θ

@[rewrite_rule]
theorem tobj_hobj (α : a ⟶ a') (x : F.obj a) (c : P.obj ((∫ F)ᵒᵖ.tot x)) :
    tobj κ (hobj P α x c) = hobj P' (u.toFunctor.map α) (τ.toObj.obj x) (tobj κ c) :=
  Functor.congr_obj (tapp_hmap κ α x) c

@[rewrite_rule]
theorem tobj_vobj {x y : F.obj a} (β : x ⟶ y) (c : P.obj ((∫ F)ᵒᵖ.tot y)) :
    tobj κ (vobj P (B := ∫ F) β c) =
      vobj P' (B := ∫ G) (τ.unstraighten.toPre.map (f := 𝟙 a) β) (tobj κ c) :=
  Functor.congr_obj (tapp_vmap κ β) c

@[rewrite_rule]
theorem tmor_id {x : (∫ F)ᵒᵖ.Total} (c : P.obj x) : tmor κ (𝟙 c) = 𝟙 _ :=
  (κ.app x).toFunctor.map_id c

@[rewrite_rule]
theorem tmor_comp {x : (∫ F)ᵒᵖ.Total} {c c' c'' : P.obj x} (θ : c ⟶ c') (θ' : c' ⟶ c'') :
    tmor κ (θ ≫ θ') = tmor κ θ ≫ tmor κ θ' :=
  (κ.app x).toFunctor.map_comp θ θ'

@[rewrite_rule]
theorem tmor_hmor (α : a ⟶ a') (x : F.obj a) {c c' : P.obj ((∫ F)ᵒᵖ.tot x)} (θ : c ⟶ c') :
    tmor κ (hmor P α x θ) = hmor P' (u.toFunctor.map α) (τ.toObj.obj x) (tmor κ θ) :=
  eq_of_heq (tmor_hmor_heq κ α x θ)

@[rewrite_rule]
theorem tmor_vmor {x y : F.obj a} (β : x ⟶ y) {c c' : P.obj ((∫ F)ᵒᵖ.tot y)} (θ : c ⟶ c') :
    tmor κ (vmor P (B := ∫ F) β θ) =
      vmor P' (B := ∫ G) (τ.unstraighten.toPre.map (f := 𝟙 a) β) (tmor κ θ) :=
  eq_of_heq (tmor_vmor_heq κ β θ)

/-! The components of composites of morphisms of dependent profunctors, as rules, so that the
heads `tobj` and `tmor` are kept when a composite is unfolded. -/

variable {A'' : Cat.{u, u}} {u' : A' ⟶ A''} {H : A'' ⥤ Cat.{u, u}}
  {σ : StrictTrans G (u'.toFunctor ⋙ H)} {P'' : (∫ H)ᵒᵖ.Total ⥤ Cat.{u, u}}

@[rewrite_rule]
theorem tobj_compNat (κ' : P' ⟶ σ.dualTotal ⋙ P'') {x : (∫ F)ᵒᵖ.Total} (c : P.obj x) :
    tobj (u := u ≫ u') (τ := StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ))
      (P' := P'') (κ ≫ Functor.whiskerLeft τ.dualTotal κ') c = tobj κ' (tobj κ c) := rfl

@[rewrite_rule]
theorem tmor_compNat (κ' : P' ⟶ σ.dualTotal ⋙ P'') {x : (∫ F)ᵒᵖ.Total} {c c' : P.obj x}
    (θ : c ⟶ c') :
    tmor (u := u ≫ u') (τ := StrictTrans.vcomp τ (StrictTrans.whiskerLeft u.toFunctor σ))
      (P' := P'') (κ ≫ Functor.whiskerLeft τ.dualTotal κ') θ = tmor κ' (tmor κ θ) := rfl

end Components

/-! ## `unstraighten` -/

/-- The unstraightening of a dependent profunctor is a split D2SFib. The instance
`Unstraightening.instSplitD2SFib` does not apply to it, since `DProf.Ob F` is not reducibly a type
of functors. -/
instance {A : Cat.{u, u}} {F : ICatStr.Ob A} (P : DProf.Ob F) : SplitD2SFib (Unstraightening P) :=
  Unstraightening.instSplitD2SFib P

/-- **The unstraightening of a morphism of dependent profunctors** `κ : P ⟶ τ.dualTotal ⋙ P'`
over `τ`: the map of D2SFibs over `τ.unstraighten` given by the components of `κ`. -/
def unstraightenMap (κ : P ⟶ τ.dualTotal ⋙ P') :
    D2SFibMap τ.unstraighten (Unstraightening P) (Unstraightening P') where
  toObj :=
    { obj := fun c => tobj κ c
      map := fun θ => tmor κ θ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
      obj_pull := by intros; rfl
      obj_push := by intros; rfl }
  map_pullLift := by intros; rfl
  map_pushLift := by intros; rfl

/-- **The unstraightening over `ICatStr`**: dependent profunctors go to their unstraightenings,
and their morphisms over `τ` to maps of D2SFibs over `τ.unstraighten`. -/
def unstraighten : VertFunctor DProf.{u} D2SFibDisp.{u} where
  obj P := unstraightenObj P
  map κ := unstraightenMap κ
  map_id _ := rfl
  map_comp _ _ := D2SFibMap.ext (DDFunctor.ext (fun _ => rfl) fun _ => HEq.rfl)

end DoubleDisplayed.D2SFib.Fibred
