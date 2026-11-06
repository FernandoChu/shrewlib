import Displayed.Opfibration.DualOp

/-!
# Opcartesian functors

An *opcartesian functor* `OpcartesianFunctor u D E` between cloven opfibrations `D` over `A` and
`E` over `B` is a displayed functor `H` over `u : A ⥤ B` preserving the chosen opcartesian lifts on
the nose:

* on objects, `H (push f x) = push (u f) (H x)` (`PreOpcartesianFunctor.obj_push`);
* on lifts, `H (olift f x) = olift (u f) (H x)` (`OpcartesianFunctor.map_olift`).

Both are rewrite rules. As for `CartesianFunctor` (`Fibration/CartesianFunctor.lean`), of which
this is the dual, the functor preserving the chosen pushforwards (`PreOpcartesianFunctor`) is a
field of `OpcartesianFunctor` rather than a parent, so that the rule on objects makes the equation
on lifts well typed. An opcartesian functor preserves the transport `pushMap` (`map_pushMap`) and
the opcartesian factorizations (`map_opcartesianFactor`), as rules. Opcartesian functors have
identities and compose, with laws by `rfl`.

Between split opfibrations, an opcartesian functor `H` over `u` induces a displayed functor
`H.dualOp : DispFunctor u Dᵒᵖ Eᵒᵖ` between the dual opfibrations (`Opfibration/DualOp.lean`),
which is `H` on the vertical morphisms `y ⟶ push f x` of `Dᵒᵖ`. The functors it induces between
the total categories preserve identities and composites, as rules.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A displayed functor over `u` preserving the chosen pushforwards on objects. This axiom is a
rewrite rule. -/
structure PreOpcartesianFunctor (u : A ⥤ B) (D : Displayed.{v₃, u₃} A)
    (E : Displayed.{v₄, u₄} B) [Opfib D] [Opfib E] extends DispFunctor u D E where
  /-- Preserves the chosen pushforwards on objects. -/
  obj_push : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a),
    obj (Opfib.push f x) = Opfib.push (u.map f) (obj x) := by intros; rfl

attribute [rewrite_rule] PreOpcartesianFunctor.obj_push

/-- **An opcartesian functor**: a displayed functor over `u` preserving the chosen opcartesian
lifts strictly. -/
structure OpcartesianFunctor (u : A ⥤ B) (D : Displayed.{v₃, u₃} A)
    (E : Displayed.{v₄, u₄} B) [Opfib D] [Opfib E] where
  /-- The underlying displayed functor, preserving the chosen pushforwards. -/
  toPre : PreOpcartesianFunctor u D E
  /-- Preserves the chosen opcartesian lifts. The right-hand side is stated with `E.olift` rather
  than `Opfib.olift`, its unfolding, so that rules keyed on `E.olift`, such as `vert_olift`, apply
  to it. -/
  map_olift : ∀ {a a' : A} (f : a ⟶ a') (x : D.Ob a),
    toPre.map (Opfib.olift f x) = E.olift (u.map f) (toPre.obj x) := by intros; rfl

attribute [rewrite_rule] OpcartesianFunctor.map_olift

namespace OpcartesianFunctor

variable {u : A ⥤ B} {D : Displayed.{v₃, u₃} A} {E : Displayed.{v₄, u₄} B}

section

variable [Opfib D] [Opfib E]

/-- The underlying displayed functor. -/
abbrev toDispFunctor (H : OpcartesianFunctor u D E) : DispFunctor u D E :=
  H.toPre.toDispFunctor

/-- Opcartesian functors are determined by their underlying displayed functors. -/
theorem ext {H K : OpcartesianFunctor u D E} (h : H.toDispFunctor = K.toDispFunctor) : H = K := by
  obtain ⟨⟨H, _⟩, _⟩ := H
  obtain ⟨⟨K, _⟩, _⟩ := K
  obtain rfl : H = K := h
  rfl

/-- The identity opcartesian functor. -/
protected def id (D : Displayed.{v₃, u₃} A) [Opfib D] : OpcartesianFunctor (𝟭 A) D D where
  toPre := { toDispFunctor := DispFunctor.id D }

/-- Composition of opcartesian functors, over the composite functor. -/
def comp {C : Type u₅} [Category.{v₅} C] {v : B ⥤ C} {E' : Displayed.{v₆, u₆} C}
    [Opfib E'] (H : OpcartesianFunctor u D E) (K : OpcartesianFunctor v E E') :
    OpcartesianFunctor (u ⋙ v) D E' where
  toPre := { toDispFunctor := H.toDispFunctor.comp K.toDispFunctor }

end

/-- **An opcartesian functor preserves transport**: `H (pushMap f β) = pushMap (u f) (H β)`. -/
@[rewrite_rule]
theorem map_pushMap [Opfib D] [Opfib E] (H : OpcartesianFunctor u D E) {a a' : A} (f : a ⟶ a')
    {x y : D.Fiber a} (β : x ⟶ y) :
    H.toPre.map (D.pushMap f β) = E.pushMap (u.map f) (H.toPre.map β : H.toPre.obj x ⟶ _) := by
  refine IsOpcartesian.hom_ext (φ := E.olift (u.map f) (H.toPre.obj x))
    (E.isOpcartesianOlift _ _) ?_
  refine (congrArg H.toPre.map (D.olift_pushMap f β)).trans ?_
  -- The rule `DispFunctor.map_comp` matches the base morphism of `H.toPre.map` structurally, and
  -- here it is `f` rather than `𝟙 a ≫ f`.
  refine (H.toPre.map_comp (f := 𝟙 a) (g := f) β (D.olift f y)).trans ?_
  exact (E.olift_pushMap (u.map f) (H.toPre.map β : H.toPre.obj x ⟶ _)).symm

/-- **An opcartesian functor preserves the opcartesian factorizations**:
`H (opcartesianFactor φ) = opcartesianFactor (H φ)`. -/
@[rewrite_rule]
theorem map_opcartesianFactor [Opfib D] [Opfib E] (H : OpcartesianFunctor u D E) {a a' : A}
    {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) :
    H.toPre.map (D.opcartesianFactor φ) = E.opcartesianFactor (H.toPre.map φ) := by
  refine E.opcartesianFactor_uniq _ _ ?_
  refine (H.toPre.map_comp (f := f) (g := 𝟙 a') (D.olift f x) (D.opcartesianFactor φ)).symm.trans ?_
  exact congrArg H.toPre.map (D.olift_comp_opcartesianFactor φ)

variable [SplitOpfib D] [SplitOpfib E]

/-- **The dual of an opcartesian functor** between split opfibrations: the displayed functor
`Dᵒᵖ ⟶ Eᵒᵖ` over `u` given by `H` on the vertical morphisms `y ⟶ push f x`. -/
def dualOp (H : OpcartesianFunctor u D E) : DispFunctor u Dᵒᵖ Eᵒᵖ where
  obj x := H.toPre.obj x
  map {_ _ _ _ y} φ := (H.toPre.map φ : H.toPre.obj y ⟶ _)

/-! The functors that the identities and composites of opcartesian functors induce between the
total categories of the dual opfibrations are the identities and composites, as rules. -/

@[rewrite_rule]
theorem dualOp_total_id : (OpcartesianFunctor.id D).dualOp.total = 𝟭 _ := rfl

@[rewrite_rule]
theorem dualOp_total_comp {C : Type u₅} [Category.{v₅} C] {v : B ⥤ C}
    {E' : Displayed.{v₆, u₆} C} [SplitOpfib E'] (H : OpcartesianFunctor u D E)
    (K : OpcartesianFunctor v E E') : (H.comp K).dualOp.total = H.dualOp.total ⋙ K.dualOp.total :=
  rfl

end OpcartesianFunctor

end Displayed
