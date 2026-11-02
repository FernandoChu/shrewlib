import Displayed.Fibration.Basic
import Tactic.KernelTactic

/-!
# Cartesian functors

A *cartesian functor* `CartesianFunctor u D E` between cloven fibrations `D` over `A` and `E` over
`B` is a displayed functor `H` over `u : A ⥤ B` preserving the chosen cartesian lifts on the nose:

* on objects, `H (pull f y) = pull (u f) (H y)` (`PreCartesianFunctor.obj_pull`);
* on lifts, `H (clift f y) = clift (u f) (H y)` (`CartesianFunctor.map_clift`).

Both are rewrite rules. The rule on objects makes the equation on lifts well typed as a plain
equation, so the functor preserving the chosen pullbacks (`PreCartesianFunctor`) is a field of
`CartesianFunctor` rather than a parent, as for `D2SFibHom`.

This is the strict notion, for cleavages, stronger than preserving cartesian morphisms
(`DispFunctor.PreservesCartesian`), which is what is usually called a cartesian functor. A vertical
cartesian functor does preserve all cartesian morphisms (`CartesianFunctor.isCartesianMap`), since
every cartesian morphism is a vertical isomorphism followed by a chosen lift. Cartesian functors
have identities and compose, over the identity and composite functors, with laws by `rfl`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A displayed functor over `u` preserving the chosen pullbacks on objects. This axiom is a
rewrite rule. -/
structure PreCartesianFunctor (u : A ⥤ B) (D : Displayed.{v₁, u₁, v₃, u₃} A)
    (E : Displayed.{v₂, u₂, v₄, u₄} B) [Fib D] [Fib E] extends DispFunctor u D E where
  /-- Preserves the chosen pullbacks on objects. -/
  obj_pull : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'),
    obj (Fib.pull f y) = Fib.pull (u.map f) (obj y)

attribute [rewrite_rule] PreCartesianFunctor.obj_pull

/-- **A cartesian functor**: a displayed functor over `u` preserving the chosen cartesian lifts
strictly. -/
structure CartesianFunctor (u : A ⥤ B) (D : Displayed.{v₁, u₁, v₃, u₃} A)
    (E : Displayed.{v₂, u₂, v₄, u₄} B) [Fib D] [Fib E] where
  /-- The underlying displayed functor, preserving the chosen pullbacks. -/
  toPre : PreCartesianFunctor u D E
  /-- Preserves the chosen cartesian lifts. -/
  map_clift : ∀ {a a' : A} (f : a ⟶ a') (y : D.Ob a'),
    toPre.map (Fib.clift f y) = Fib.clift (u.map f) (toPre.obj y)

attribute [rewrite_rule] CartesianFunctor.map_clift

namespace CartesianFunctor

variable {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₃, u₃} A} {E : Displayed.{v₂, u₂, v₄, u₄} B} [Fib D]
  [Fib E]

/-- The underlying displayed functor. -/
abbrev toDispFunctor (H : CartesianFunctor u D E) : DispFunctor u D E :=
  H.toPre.toDispFunctor

/-- The identity cartesian functor. -/
protected def id (D : Displayed.{v₁, u₁, v₃, u₃} A) [Fib D] : CartesianFunctor (𝟭 A) D D where
  toPre := { toDispFunctor := DispFunctor.id D, obj_pull := fun _ _ => rfl }
  map_clift _ _ := rfl

/-- Composition of cartesian functors, over the composite functor. -/
def comp {C : Type u₅} [Category.{v₅} C] {v : B ⥤ C} {E' : Displayed.{v₅, u₅, v₆, u₆} C} [Fib E']
    (H : CartesianFunctor u D E) (K : CartesianFunctor v E E') : CartesianFunctor (u ⋙ v) D E' where
  toPre := { toDispFunctor := H.toDispFunctor.comp K.toDispFunctor, obj_pull := fun _ _ => rfl }
  map_clift _ _ := rfl

end CartesianFunctor

/-- **A vertical cartesian functor preserves cartesian morphisms**: the chosen lifts go to chosen
lifts, which are cartesian. -/
def CartesianFunctor.isCartesianMap {D : Displayed.{v₁, u₁, v₃, u₃} A}
    {E : Displayed.{v₁, u₁, v₄, u₄} A} [Fib D] [Fib E] (H : CartesianFunctor (𝟭 A) D E) :
    H.toDispFunctor.PreservesCartesian :=
  VertFunctor.isCartesianMapOfClift H.toDispFunctor
    fun f y => by kernel_exact E.isCartesianClift f (H.toDispFunctor.obj y)

end Displayed
