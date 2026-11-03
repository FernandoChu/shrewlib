import DoubleDisplayed.D2SFib.DProf
import DoubleDisplayed.D2SFib.D2SFibStr
import DoubleDisplayed.D2SFib.Straightening.Straighten
import Displayed.Opfibration.Straightening.Str

/-!
# Straightening of D2SFibs into dependent profunctors

The straightening `straightenObj C : Bᵒᵖ.Total ⥤ Cat` of a split D2SFib `C` over a split
opfibration `B` sends `⟨a, x⟩` to the fiber of `C` over `x`, and a morphism `⟨α, β⟩` to
`pushFunctor α ⋙ pullFunctor β` (`DoubleDisplayed/D2SFib/Straightening/Straighten.lean`). Here we
make it a doubly displayed functor `straighten : D2SFibStr ⟶ DProf` over the straightening
`straightenStr : SplitOpfibStr ⟶ ICatStr` of split opfibrations, which sends `B` to the functor
`straightenObj B : A ⥤ Cat` of its fibres.

So the straightening of `C` is a dependent profunctor over `straightenObj B`, a functor out of the
total category of the dual of `∫ (straightenObj B)` (`straightenDProf`). That category has the same
objects and morphisms as `Bᵒᵖ.Total`: pairs `⟨a, x⟩` with `x` over `a`, and pairs of `α : a ⟶ a'`
and a vertical morphism `β : x' ⟶ push α x`. So `straightenDProf C` has the values of
`straightenObj C`, written out again, rather than as a composite with the identity of these
categories, which the rules `Functor.id_comp` and `Functor.comp_id` would make slow.

A map `Φ` of D2SFibs over an opcartesian functor `H` gives the natural transformation whose
components are the fiber functors of `Φ` (`straightenMap`). Its naturality holds by `rfl`: `Φ`
commutes with `pushMap` and `pullMap`, by the rules of `D2SFibMap`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed Displayed.Opfibration.Straightening

open Displayed.Opfibration.Straightening (ICatStr StrictTrans)

section Map

variable {A A' : Type u₁} [Category.{v₁} A] [Category.{v₁} A'] {u : A ⥤ A'}
  {B : Displayed.{v₁, u₁, v₂, u₂} A} {B' : Displayed.{v₁, u₁, v₂, u₂} A'} [SplitOpfib B]
  [SplitOpfib B'] {H : OpcartesianFunctor u B B'} {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}
  {C' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B'} [SplitD2SFib C] [SplitD2SFib C']

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
  map_id _ := rfl
  map_comp _ _ := rfl

end DoubleDisplayed.D2SFib.Straightening
