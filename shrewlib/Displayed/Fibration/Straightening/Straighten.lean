import Displayed.Fibration.SplitFibLax
import Displayed.Fibration.Straightening.ICatOpLax
import Rules.Opposite

/-!
# Straightening split fibrations

The straightening of a split fibration `D` over `A` is the functor `Aᵒᵖ ⥤ Cat` of its fibres
`a ↦ D.Fiber a`, with the pullback functors `pullFunctor f`. It is a functor by `rfl`, since the
splitting laws and the functoriality of `pullMap` are rules.

A displayed functor `H` over `u : A ⟶ B` between split fibrations straightens to the lax
transformation `straightenMap H : LaxTrans (straightenObj X) (reindex u (straightenObj Y))`, whose
components are `H` on the fibres, and whose 2-cells `H (pull f y) ⟶ pull (u f) (H y)` are the
cartesian factorizations of `H (clift f y)`: they measure how far `H` is from preserving the
chosen lifts. This is the vertical functor `straighten : SplitFibLax ⟶ ICatOpLax`. This is the dual
of `Opfibration/Straightening/Straighten.lean`.
-/

universe u

namespace Displayed.Fibration.Straightening

open CategoryTheory Opposite Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : SplitFibOb A)

/-- **The straightening of a split fibration** `D`: its fibres, with the pullback functors. -/
def straightenObj : Aᵒᵖ ⥤ Cat.{u, u} where
  obj a := Cat.of (X.toDisplayed.Fiber a.unop)
  map f := (X.toDisplayed.pullFunctor f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X}

/-- **The straightening of a displayed functor** `H` over `u` between split fibrations: the lax
transformation with components `H` on the fibres, and with 2-cells the cartesian factorizations of
the images of the chosen lifts. -/
def straightenMap {B : Cat.{u, u}} {u : A ⟶ B} {Y : SplitFibOb B}
    (H : DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed) :
    LaxTrans (straightenObj X) (reindex u.toFunctor (straightenObj Y)) where
  app a :=
    { obj x := H.obj x
      map β := (H.map β : H.obj _ ⟶ _)
      map_id _ := rfl
      map_comp _ _ := rfl }
  naturality f y := Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f y))
  naturality_naturality {a a'} f {x y} φ := by
    -- Both sides are the cartesian factorization of `H (pullMap f φ ≫ clift f y)`, which is
    -- `H (clift f x ≫ φ)`.
    change (H.map (f := 𝟙 a) (X.toDisplayed.pullMap f φ) : H.obj _ ⟶ H.obj _) ≫
        Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f y)) =
      Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f x)) ≫
        Y.toDisplayed.pullMap (u.toFunctor.map f) (H.map (f := 𝟙 a') φ : H.obj x ⟶ H.obj y)
    calc _ = Y.toDisplayed.cartesianFactor
            (H.map (f := 𝟙 a) (X.toDisplayed.pullMap f φ) ≫ᵈ H.map (X.toDisplayed.clift f y)) :=
          (Y.toDisplayed.cartesianFactor_comp (f := 𝟙 _) (g := u.toFunctor.map f)
            (H.map (f := 𝟙 a) (X.toDisplayed.pullMap f φ)) (H.map (X.toDisplayed.clift f y))).symm
      _ = Y.toDisplayed.cartesianFactor
            (H.map (f := 𝟙 a ≫ f) (X.toDisplayed.pullMap f φ ≫ᵈ X.toDisplayed.clift f y)) :=
          congrArg _ (H.map_comp (f := 𝟙 a) (g := f) _ _).symm
      _ = Y.toDisplayed.cartesianFactor
            (H.map (f := f ≫ 𝟙 a') (X.toDisplayed.clift f x ≫ᵈ φ)) :=
          congrArg (fun t => Y.toDisplayed.cartesianFactor (H.map t))
            (X.toDisplayed.pullMap_clift f φ)
      _ = Y.toDisplayed.cartesianFactor
            (H.map (X.toDisplayed.clift f x) ≫ᵈ H.map (f := 𝟙 a') φ) :=
          congrArg _ (H.map_comp (f := f) (g := 𝟙 a') _ _)
      _ = _ := Y.toDisplayed.cartesianFactor_comp _ _

/-- The 2-cells of the straightening of a composite: the factorization of `K (H (clift f y))` is
`K` of that of `H (clift f y)` followed by that of `K (clift (u f) (H y))`. -/
theorem straightenMap_comp_naturality {B C : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ C}
    {Y : SplitFibOb B} {Z : SplitFibOb C} (H : DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed)
    (K : DispFunctor v.toFunctor Y.toDisplayed Z.toDisplayed) {a a' : A} (f : a ⟶ a')
    (y : X.toDisplayed.Ob a') :
    Z.toDisplayed.cartesianFactor (K.map (H.map (X.toDisplayed.clift f y))) =
      K.map (f := 𝟙 _) (Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f y))) ≫ᵈ
        Z.toDisplayed.cartesianFactor (K.map (Y.toDisplayed.clift (u.toFunctor.map f) (H.obj y))) :=
  calc _ = Z.toDisplayed.cartesianFactor (K.map (f := 𝟙 _ ≫ u.toFunctor.map f)
          (Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f y)) ≫ᵈ
            Y.toDisplayed.clift (u.toFunctor.map f) (H.obj y))) :=
        congrArg (fun t => Z.toDisplayed.cartesianFactor (K.map t))
          (Y.toDisplayed.cartesianFactor_comp_clift _).symm
    _ = Z.toDisplayed.cartesianFactor
          (K.map (f := 𝟙 _) (Y.toDisplayed.cartesianFactor (H.map (X.toDisplayed.clift f y))) ≫ᵈ
            K.map (Y.toDisplayed.clift (u.toFunctor.map f) (H.obj y))) :=
        congrArg _ (K.map_comp (f := 𝟙 _) (g := u.toFunctor.map f) _ _)
    _ = _ := Z.toDisplayed.cartesianFactor_comp _ _

/-- **The straightening of split fibrations**: a split fibration goes to the functor of its
fibres, and a displayed functor to the lax transformation `straightenMap`. -/
def straighten : VertFunctor SplitFibLax.{u} ICatOpLax.{u} where
  obj X := straightenObj X
  map H := straightenMap H
  map_id _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)
  map_comp H K := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl)
    (fun f y => heq_of_eq (straightenMap_comp_naturality H K f y))

end Displayed.Fibration.Straightening
