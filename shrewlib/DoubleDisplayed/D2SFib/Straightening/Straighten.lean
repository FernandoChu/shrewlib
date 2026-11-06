import DoubleDisplayed.D2SFib.Straightening.DProf
import DoubleDisplayed.D2SFib.D2SFibStr
import Displayed.Opfibration.DualOp
import Displayed.Opfibration.Straightening.Str

/-!
# Straightening: from D2SFibs to dependent profunctors

The straightening of a split D2SFib `C` over a split opfibration `B` is the functor
`⟨a, b⟩ ↦ C.Fiber b` on the total category of the dual opfibration `Bᵒᵖ`, with a morphism
`⟨α, β⟩` sent to `pushFunctor α ⋙ pullFunctor β` (`straightenObj`). Since the functoriality and
interchange of `push`/`pull` and of `pushMap`/`pullMap` hold definitionally, `straightenObj C` is a
functor by `rfl`.

Here `B` is any split opfibration, not the unstraightening of a functor, so `straightenObj C` is a
functor out of `Bᵒᵖ.Total`. As a dependent profunctor, the straightening of `C` is a functor out of
`(∫ (straightenObj B ⋙ opFunctor')).Total`, over the functor `straightenObj B` of the fibres of `B`
(`straightenDProf`). That category has the same objects and morphisms as `Bᵒᵖ.Total`: pairs
`⟨a, x⟩` with `x` over `a`, and pairs of `α : a ⟶ a'` and a vertical morphism `β : x' ⟶ push α x`.
So `straightenDProf C` has the values of `straightenObj C`, written out again, rather than as a
composite with the identity of these categories, which the rules `Functor.id_comp` and
`Functor.comp_id` would make slow. The values are first defined on `Bᵒᵖ.Total`, whose objects are
reducibly over `B`, so that instance search finds the categories `C.Fiber b`.

A map `Φ` of D2SFibs over an opcartesian functor `H` gives the natural transformation whose
components are the fiber functors of `Φ` (`straightenStrMap`). Its naturality holds by `rfl`: `Φ`
commutes with `pushMap` and `pullMap`, by the rules of `D2SFibMap`. This makes the straightening a
doubly displayed functor `straighten : D2SFibStr ⟶ DProf` over the straightening
`straightenStr : SplitOpfibStr ⟶ ICatStr` of split opfibrations, which sends `B` to the functor
`straightenObj B : A ⥤ Cat` of its fibres.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed Displayed.Opfibration.Straightening

open Displayed.Opfibration.Straightening (ICatStr StrictTrans)

section Obj

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₂, u₂} A} [SplitOpfib B]

set_option maxHeartbeats 400000 in
-- `map_comp` holds by `rfl`, through the rules for `push`, `pull`, `pushMap` and `pullMap`;
-- checking it unfolds both composites of functors.
/-- **The straightening of a D2SFib** `C`: the functor `Bᵒᵖ.Total ⥤ Cat`, `⟨a, b⟩ ↦ C.Fiber b`,
with a morphism `⟨α, β⟩` sent to `pushFunctor α ⋙ pullFunctor β`. -/
def straightenObj (C : DoubleDisplayed.{v₃, u₃} B) [SplitD2SFib C] :
    Bᵒᵖ.Total ⥤ Cat.{v₃, u₃} where
  obj x := Cat.of (C.Fiber x.2)
  map {x _} F := (pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem straightenObj_map_toFunctor (C : DoubleDisplayed.{v₃, u₃} B) [SplitD2SFib C]
    {x x' : Bᵒᵖ.Total} (F : x ⟶ x') :
    ((straightenObj C).map F).toFunctor
      = pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber := rfl

/-- `straightenObj C` sends a chosen horizontal morphism to the pushforward functor. -/
theorem straightenObj_map_dualHoriz (C : DoubleDisplayed.{v₃, u₃} B) [SplitD2SFib C]
    {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    ((straightenObj C).map (dualHoriz α b)).toFunctor = pushFunctor (C := C) α b := rfl

/-- `straightenObj C` sends a chosen vertical morphism to the pullback functor. -/
theorem straightenObj_map_dualVert (C : DoubleDisplayed.{v₃, u₃} B) [SplitD2SFib C]
    {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    ((straightenObj C).map (dualVert β)).toFunctor = pullFunctor (C := C) β := rfl

end Obj

section Map

variable {A A' : Type u₁} [Category.{v₁} A] [Category.{v₁} A'] {u : A ⥤ A'}
  {B : Displayed.{v₂, u₂} A} {B' : Displayed.{v₂, u₂} A'} [SplitOpfib B]
  [SplitOpfib B'] {H : OpcartesianFunctor u B B'} {C : DoubleDisplayed.{v₃, u₃} B}
  {C' : DoubleDisplayed.{v₃, u₃} B'} [SplitD2SFib C] [SplitD2SFib C']

/-- The natural transformation `straightenObj C ⟶ H.dualOp.total ⋙ straightenObj C'` of a map `Φ`
of D2SFibs over `H`, whose components are the fiber functors of `Φ`. -/
def straightenStrMap (Φ : D2SFibMap H C C') :
    straightenObj C ⟶ H.dualOp.total ⋙ straightenObj C' where
  app x := (Φ.toDDFunctor.fiber x.2).toCatHom
  naturality _ _ _ := rfl

end Map

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {B : SplitOpfibOb.{u, u, u, u} A}
  {B' : SplitOpfibOb.{u, u, u, u} A'}

/-- **The straightening of a D2SFib** `C` over `B`, as a dependent profunctor over the functor
`straightenObj B` of the fibres of `B`: the values of `straightenObj C`, `⟨a, x⟩ ↦ C.Fiber x`, and
a morphism `⟨α, β⟩` goes to `pushFunctor α ⋙ pullFunctor β`. -/
def straightenDProf (E : D2SFibCat.{u, u, u, u, v₃, u₃} B.toDisplayed) :
    DProf.{u, v₃, u₃}.Ob (Opfibration.Straightening.straightenObj B) where
  obj x := (straightenObj E.C).obj x
  map F := (straightenObj E.C).map ⟨F.base, F.fiber⟩
  map_id x := (straightenObj E.C).map_id x
  map_comp F G := (straightenObj E.C).map_comp (X := _) (Y := _) (Z := _) ⟨F.base, F.fiber⟩
    ⟨G.base, G.fiber⟩

/-- **The straightening of a map of D2SFibs** `Φ` over `H`: the natural transformation whose
components are the fiber functors of `Φ`. -/
def straightenMap {H : OpcartesianFunctor u.toFunctor B.toDisplayed B'.toDisplayed}
    {E : D2SFibCat.{u, u, u, u, v₃, u₃} B.toDisplayed}
    {E' : D2SFibCat.{u, u, u, u, v₃, u₃} B'.toDisplayed} (Φ : D2SFibMap H E.C E'.C) :
    DProf.Hom (Opfibration.Straightening.straightenStr.map H) (straightenDProf E)
      (straightenDProf E') where
  app x := (straightenStrMap Φ).app x
  naturality _ _ _ := rfl

/-- **The straightening of D2SFibs**, a doubly displayed functor over the straightening
`SplitOpfibStr ⟶ ICatStr` of split opfibrations: a D2SFib goes to its straightening, and a map
of D2SFibs over `H` to the morphism of dependent profunctors given by its fiber functors. -/
def straighten :
    DDFunctor Opfibration.Straightening.straightenStr D2SFibStr.{u, u, u, u, v₃, u₃}
      DProf.{u, v₃, u₃} where
  obj E := straightenDProf E
  map Φ := straightenMap Φ

end DoubleDisplayed.D2SFib.Straightening
