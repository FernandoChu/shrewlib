import Displayed.Opfibration.SplitOpfibLax
import Displayed.Opfibration.Straightening.ICatLax

/-!
# Straightening split opfibrations

The straightening of a split opfibration `D` over `A` is the functor `A ⥤ Cat` of its fibres
`a ↦ D.Fiber a`, with the pushforward functors `pushFunctor f`. It is a functor by `rfl`, since the
splitting laws and the functoriality of `pushMap` are rules.

A displayed functor `H` over `u : A ⟶ B` between split opfibrations straightens to the lax
transformation `straightenMap H : LaxTrans (straightenObj X) (u ⋙ straightenObj Y)`, whose
components are `H` on the fibres, and whose 2-cells `push (u f) (H x) ⟶ H (push f x)` are the
opcartesian factorizations of `H (olift f x)`: they measure how far `H` is from preserving the
chosen lifts. This is the vertical functor `straighten : SplitOpfibLax ⟶ ICatLax`.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : SplitOpfibOb A)

/-- **The straightening of a split opfibration** `D`: its fibres, with the pushforward
functors. -/
def straightenObj : A ⥤ Cat.{u, u} where
  obj a := Cat.of (X.toDisplayed.Fiber a)
  map f := (X.toDisplayed.pushFunctor f).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X}

/-- **The straightening of a displayed functor** `H` over `u` between split opfibrations: the lax
transformation with components `H` on the fibres, and with 2-cells the opcartesian factorizations
of the images of the chosen lifts. -/
def straightenMap {B : Cat.{u, u}} {u : A ⟶ B} {Y : SplitOpfibOb B}
    (H : DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed) :
    LaxTrans (straightenObj X) (u.toFunctor ⋙ straightenObj Y) where
  app a :=
    { obj x := H.obj x
      map β := (H.map β : H.obj _ ⟶ _)
      map_id _ := rfl
      map_comp _ _ := rfl }
  naturality f x := Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f x))
  naturality_naturality {a a'} f {x y} φ := by
    -- Both sides are the opcartesian factorization of `H (φ ≫ olift f y)`, which is
    -- `H (olift f x ≫ pushMap f φ)`.
    change Y.toDisplayed.pushMap (u.toFunctor.map f) (H.map (f := 𝟙 a) φ : H.obj x ⟶ H.obj y) ≫
        Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f y)) =
      Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f x)) ≫
        (H.map (f := 𝟙 a') (X.toDisplayed.pushMap f φ) : H.obj _ ⟶ H.obj _)
    calc _ = Y.toDisplayed.opcartesianFactor
            (H.map (f := 𝟙 a) φ ≫ᵈ H.map (X.toDisplayed.olift f y)) :=
          (Y.toDisplayed.opcartesianFactor_comp _ _).symm
      _ = Y.toDisplayed.opcartesianFactor
            (H.map (f := 𝟙 a ≫ f) (φ ≫ᵈ X.toDisplayed.olift f y)) :=
          congrArg _ (H.map_comp (f := 𝟙 a) (g := f) φ _).symm
      _ = Y.toDisplayed.opcartesianFactor
            (H.map (f := f ≫ 𝟙 a') (X.toDisplayed.olift f x ≫ᵈ X.toDisplayed.pushMap f φ)) :=
          congrArg (fun t => Y.toDisplayed.opcartesianFactor (H.map t))
            (X.toDisplayed.vert_olift f φ)
      _ = Y.toDisplayed.opcartesianFactor
            (H.map (X.toDisplayed.olift f x) ≫ᵈ H.map (f := 𝟙 a') (X.toDisplayed.pushMap f φ)) :=
          congrArg _ (H.map_comp (f := f) (g := 𝟙 a') _ _)
      _ = _ := Y.toDisplayed.opcartesianFactor_comp _ _
  naturality_id _ := rfl
  naturality_comp _ _ _ := rfl

/-- The 2-cells of the straightening of a composite: the factorization of `K (H (olift f x))` is
that of `K (olift (u f) (H x))` followed by `K` of that of `H (olift f x)`. -/
theorem straightenMap_comp_naturality {B C : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ C}
    {Y : SplitOpfibOb B} {Z : SplitOpfibOb C}
    (H : DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed)
    (K : DispFunctor v.toFunctor Y.toDisplayed Z.toDisplayed) {a a' : A} (f : a ⟶ a')
    (x : X.toDisplayed.Ob a) :
    Z.toDisplayed.opcartesianFactor (K.map (H.map (X.toDisplayed.olift f x))) =
      Z.toDisplayed.opcartesianFactor (K.map (Y.toDisplayed.olift (u.toFunctor.map f) (H.obj x))) ≫ᵈ
        K.map (f := 𝟙 _) (Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f x))) :=
  calc _ = Z.toDisplayed.opcartesianFactor (K.map (f := u.toFunctor.map f ≫ 𝟙 _)
          (Y.toDisplayed.olift (u.toFunctor.map f) (H.obj x) ≫ᵈ
            Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f x)))) :=
        congrArg (fun t => Z.toDisplayed.opcartesianFactor (K.map t))
          (Y.toDisplayed.olift_comp_opcartesianFactor _).symm
    _ = Z.toDisplayed.opcartesianFactor
          (K.map (Y.toDisplayed.olift (u.toFunctor.map f) (H.obj x)) ≫ᵈ
            K.map (f := 𝟙 _) (Y.toDisplayed.opcartesianFactor (H.map (X.toDisplayed.olift f x)))) :=
        congrArg _ (K.map_comp (f := u.toFunctor.map f) (g := 𝟙 _) _ _)
    _ = _ := Z.toDisplayed.opcartesianFactor_comp _ _

/-- **The straightening of split opfibrations**: a split opfibration goes to the functor of its
fibres, and a displayed functor to the lax transformation `straightenMap`. -/
def straighten : VertFunctor SplitOpfibLax.{u} ICatLax.{u} where
  obj X := straightenObj X
  map H := straightenMap H
  map_id _ := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl) (fun _ _ => HEq.rfl)
  map_comp H K := LaxTrans.ext' (fun _ _ => rfl) (fun _ _ _ _ => HEq.rfl)
    (fun f x => heq_of_eq (straightenMap_comp_naturality H K f x))

end Displayed.Opfibration.Straightening
