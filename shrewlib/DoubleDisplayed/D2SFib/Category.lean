import DoubleDisplayed.D2SFib.Map

/-!
# The category of dependent 2-sided split fibrations

We bundle D2SFibs over `B` into the category `D2SFibCat B`, the displayed adaptation of the
category of dependent 2-sided split fibrations between `A` and `B`. Its morphisms are the maps of
D2SFibs over the identity of `B` (`D2SFibMap (OpcartesianFunctor.id B)`, `D2SFib/Map.lean`): the
vertical functors preserving the chosen cartesian and opcartesian lifts on the nose. Its laws hold
by `rfl`.

Bundled D2SFibs, and the D2SFib structures on a doubly displayed category, are determined by their
data (`D2SFibCat.ext`, `SplitD2SFib.ext`, `SplitD2SFib.hext`), the cartesian and opcartesian
structures of the chosen lifts being subsingletons.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

/-- Bundled D2SFibs: the objects of the category `D2SFibCat B`. -/
structure D2SFibCat (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] where
  /-- The underlying doubly displayed category. -/
  C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B
  /-- Its D2SFib structure. -/
  [str : SplitD2SFib C]

attribute [instance] D2SFibCat.str

/-- D2SFib structures on `C` are determined by their chosen pullbacks, pushforwards and lifts,
the cartesian and opcartesian structures being subsingletons. -/
theorem D2SFib.ext {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} {d d' : D2SFib C}
    (hpull : @D2SFib.pull _ _ _ _ C d = @D2SFib.pull _ _ _ _ C d')
    (hpullLift : @D2SFib.pullLift _ _ _ _ C d ≍ @D2SFib.pullLift _ _ _ _ C d')
    (hpush : @D2SFib.push _ _ _ _ C d = @D2SFib.push _ _ _ _ C d')
    (hpushLift : @D2SFib.pushLift _ _ _ _ C d ≍ @D2SFib.pushLift _ _ _ _ C d') : d = d' := by
  obtain ⟨pull, pullLift, isCart, push, pushLift, isOpcart⟩ := d
  obtain ⟨pull', pullLift', isCart', push', pushLift', isOpcart'⟩ := d'
  change @pull = @pull' at hpull
  subst hpull
  change @pullLift ≍ @pullLift' at hpullLift
  obtain rfl := eq_of_heq hpullLift
  change @push = @push' at hpush
  subst hpush
  change @pushLift ≍ @pushLift' at hpushLift
  obtain rfl := eq_of_heq hpushLift
  obtain rfl : @isCart = @isCart' := by
    funext a b b' β c
    exact Subsingleton.elim _ _
  obtain rfl : @isOpcart = @isOpcart' := by
    funext a a' α b c
    exact Subsingleton.elim _ _
  rfl

/-- Split D2SFib structures on `C` are determined by their chosen pullbacks, pushforwards and
lifts. -/
theorem SplitD2SFib.ext {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} {s s' : SplitD2SFib C}
    (h : s.toPreSplitD2SFib.toD2SFib = s'.toPreSplitD2SFib.toD2SFib) : s = s' := by
  cases s with | mk =>
  cases s' with | mk =>
  rename_i p _ _ _ _ _ p' _ _ _ _ _
  cases p
  cases p'
  subst h
  rfl

/-- Split D2SFib structures on equal doubly displayed categories with the same chosen pullbacks,
pushforwards and lifts are equal, heterogeneously. -/
theorem SplitD2SFib.hext {C C' : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B} (hC : C = C')
    {s : SplitD2SFib C} {s' : SplitD2SFib C'}
    (hpull : @D2SFib.pull _ _ _ _ C s.toPreSplitD2SFib.toD2SFib ≍
      @D2SFib.pull _ _ _ _ C' s'.toPreSplitD2SFib.toD2SFib)
    (hpullLift : @D2SFib.pullLift _ _ _ _ C s.toPreSplitD2SFib.toD2SFib ≍
      @D2SFib.pullLift _ _ _ _ C' s'.toPreSplitD2SFib.toD2SFib)
    (hpush : @D2SFib.push _ _ _ _ C s.toPreSplitD2SFib.toD2SFib ≍
      @D2SFib.push _ _ _ _ C' s'.toPreSplitD2SFib.toD2SFib)
    (hpushLift : @D2SFib.pushLift _ _ _ _ C s.toPreSplitD2SFib.toD2SFib ≍
      @D2SFib.pushLift _ _ _ _ C' s'.toPreSplitD2SFib.toD2SFib) : s ≍ s' := by
  subst hC
  exact heq_of_eq (SplitD2SFib.ext (D2SFib.ext (eq_of_heq hpull) hpullLift (eq_of_heq hpush)
    hpushLift))

/-- Bundled D2SFibs are determined by their doubly displayed categories and D2SFib structures. -/
theorem D2SFibCat.ext {E E' : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B} (hC : E.C = E'.C)
    (hstr : E.str ≍ E'.str) : E = E' := by
  obtain @⟨C, s⟩ := E
  obtain @⟨C', s'⟩ := E'
  change C = C' at hC
  subst hC
  change s ≍ s' at hstr
  obtain rfl := eq_of_heq hstr
  rfl

/-- The category structure on bundled D2SFibs. -/
instance : Category (D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  Hom E E' := D2SFibMap (OpcartesianFunctor.id B) E.C E'.C
  id E := D2SFibMap.id E.C
  comp F G := F.comp G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end DoubleDisplayed
