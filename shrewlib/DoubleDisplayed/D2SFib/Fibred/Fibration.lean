import DoubleDisplayed.D2SFib.Fibred.Equivalence
import DoubleDisplayed.Fibration
import Tactic.KernelTactic

/-!
# `DProf` and `D2SFibDisp` are fibred over `ICatStr`

Both categories are split fibrations over `ICatStr`, and the straightening and unstraightening
are cartesian functors between them, so that `straighteningEquiv` is an equivalence of fibred
categories over `ICatStr`.

* `DProf` is the Grothendieck construction of a contravariant functor, so it is split by
  precomposition: the pullback of `P'` along `τ` is `τ.dualTotal ⋙ P'`, with the identity as
  chosen lift (`DProf.splitDDFib`).
* `D2SFibDisp` is split by reindexing: the pullback of a D2SFib `C'` along `τ` is its reindexing
  along `τ.unstraighten`, with `D2SFibMap.reindexLift` as chosen lift (`D2SFibDisp.splitDDFib`).
  Reindexing is strictly functorial, so this fibration is split, while the fibration of D2SFibs
  presented as functors into a total category, by pullback, is not.
-/

universe u

namespace DoubleDisplayed

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed DoubleDisplayed

/-! ## Dependent profunctors -/

/-- The chosen pullback of a dependent profunctor along a strict transformation is the
precomposition with its `dualTotal`, with the identity as chosen lift. -/
instance DProf.ddFib : DDFib DProf.{u} where
  pull {_ _ u _ G} τ (P' : (∫ (G : _ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u}) :=
    StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P'
  clift {_ _ u _ G} τ (P' : (∫ (G : _ ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤ Cat.{u, u}) :=
    𝟙 (StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P')
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => χ
      lift_fac := fun {_ _ _} _ {_} _ => NatTrans.ext (funext fun _ => rfl)
      lift_uniq := fun {_ _ _ _ _ _} _ h => (NatTrans.ext (funext fun _ => rfl)).trans h }

instance DProf.preSplitDDFib : PreSplitDDFib DProf.{u} where
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **`DProf` is a split fibration over `ICatStr`**, by precomposition. -/
instance DProf.splitDDFib : SplitDDFib DProf.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := NatTrans.ext (funext fun _ => rfl)

/-! ## D2SFibs -/

/-- The chosen pullback of a D2SFib along a strict transformation `τ` is its reindexing along
`τ.unstraighten`, with `D2SFibMap.reindexLift` as chosen lift. -/
instance D2SFibDisp.ddFib : DDFib D2SFibDisp.{u} where
  pull {_ _ u F _} τ E :=
    (⟨E.C.reindex (StrictTrans.unstraighten (u := u.toFunctor) τ).toDispFunctor⟩ :
      D2SFibCat (∫ (F : _ ⥤ Cat.{u, u})))
  clift {_ _ u _ _} τ E := D2SFibMap.reindexLift (StrictTrans.unstraighten (u := u.toFunctor) τ) E.C
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => D2SFibMap.liftReindex _ _ χ
      lift_fac := fun {_ _ _} _ {_} _ => rfl
      lift_uniq := fun {_ _ _ _ _ _} _ h => by subst h; rfl }

instance D2SFibDisp.preSplitDDFib : PreSplitDDFib D2SFibDisp.{u} where
  pull_id _ := rfl
  pull_comp _ _ _ := rfl

/-- **`D2SFibDisp` is a split fibration over `ICatStr`**, by reindexing. -/
instance D2SFibDisp.splitDDFib : SplitDDFib D2SFibDisp.{u} where
  clift_id _ := rfl
  clift_comp _ _ _ := rfl

/-! ## The straightening and unstraightening are cartesian -/

namespace D2SFib.Fibred

section Pull

open DoubleDisplayed.D2SFib.Straightening

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}}
  (τ : StrictTrans F (u.toFunctor ⋙ G)) (P' : (∫ G)ᵒᵖ.Total ⥤ Cat.{u, u})

/-! The unstraightening of `τ.dualTotal ⋙ P'` is the reindexing of that of `P'` along
`τ.unstraighten`. The two agree field by field by `rfl`, but the kernel does not accept an `rfl`
between the structures, so the equations go through extensionality. -/

theorem unstraightening_dualTotal_comp :
    Unstraightening (τ.dualTotal ⋙ P') =
      (Unstraightening P').reindex τ.unstraighten.toDispFunctor :=
  DoubleDisplayed.ext_heq (by kernel_rfl') (by kernel_rfl') (by kernel_rfl') (by kernel_rfl')

theorem unstraightenObj_dualTotal_comp :
    D2SFib.Straightening.unstraightenObj (τ.dualTotal ⋙ P') =
      (⟨(Unstraightening P').reindex τ.unstraighten.toDispFunctor⟩ : D2SFibCat (∫ F)) :=
  D2SFibCat.ext (unstraightening_dualTotal_comp τ P')
    (SplitD2SFib.hext (unstraightening_dualTotal_comp τ P') (by kernel_rfl') (by kernel_rfl')
      (by kernel_rfl') (by kernel_rfl'))

end Pull


/-- **The straightening is a cartesian functor**: the straightening of the reindexing of `C'`
along `τ.unstraighten` is `τ.dualTotal ⋙ straightenObj C'`. -/
def straightenCartesian : DDCartesianFunctor D2SFibDisp.{u} DProf.{u} where
  toPre := { toVertFunctor := straighten, obj_pull := fun _ _ => rfl }
  map_clift _ _ := rfl

end D2SFib.Fibred

end DoubleDisplayed
