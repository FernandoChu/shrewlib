import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat
import CategoryTheory.Opposite.Discrete
import Logic.EmptyUniqueAxiom

/-!
# op-Disc as a rule

With uniqueness of empty types as an axiom (`emptyUnique`, `Logic/EmptyUniqueAxiom`), op-Disc holds
with no hypothesis, and is a rewrite rule, oriented from the opposite to the type. A discrete type
`B` reaches the category model in several forms, and the rules must agree on all of them, or the
contexts that Lift-Ext identifies by `rfl` stop being identified:

* `comp_opFunctor'_disc`: `B.toFunctor ⋙ opFunctor' ↦ B.toFunctor`, the opposite unfolded, the form
  in which the twist uses it (`Shared/Twist`, through the dependent 2-sided Grothendieck
  construction). So the morphisms of `Γ ▹ Bᵒᵖ` that the twist is built from are those of `Γ ▹ B`;
* `op_disc_toFunctor`: `B.toFunctorᵒᵖ ↦ B.toFunctor`, the opposite in the category model, which
  the first rule reaches only after unfolding `CatModel.op`;
* `op_disc_comp`: `(σ ⋙ B.toFunctor)ᵒᵖ ↦ σ ⋙ B.toFunctor`, the same for a substitution of
  `B.toFunctor` in the category model, unfolded. It is only definitionally `(B⦃σ⦄).toFunctor`, on
  which the second rule fires. Without it, the context `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ` of the Hom-type of a
  discrete type `A` differs from its form in the category model (`homDisc_eq`);
* `comp_comp_opFunctor'_disc`: `(σ ⋙ B.toFunctor) ⋙ opFunctor' ↦ σ ⋙ B.toFunctor`, the same
  with the opposite unfolded. Without it, the inclusion of the category model into the displayed
  model no longer commutes with substitution by `rfl` for the Hom-type of `B`, whose context has
  this form (`Applications/Yoneda`);
* `op_disc_forget`: `(forgetComprehensionMap.toPre.obj B)ᵒᵖ ↦ B.toFunctor`, the opposite of `B`
  seen in the category model through the inclusion (Lift-Form). Without it, the opposite of `B` in
  the discrete model, seen in the category model, is no longer the opposite there of `B` seen in
  the category model, and the Hom-type of the discrete model is no longer that of the category
  model at the terms of `B` (`homDiscAt_eq`, in `Applications/Yoneda`);
* `op_disc`: `Bᵒᵖ ↦ ⟨B.toFunctor, B.isDiscrete⟩`, the opposite in the discrete model. Its
  right-hand side is `B` up to the extensionality of structures, and is stated as a constructor:
  the kernel reduces the projection `Bᵒᵖ.toFunctor` by rewriting `Bᵒᵖ`, and the projection of the
  variable `B` would not reduce, so that `Bᵒᵖ.toFunctor` would no longer be `B.toFunctor`. The
  elaborator turns a structure instance `{ toFunctor := B.toFunctor, .. }` into `B`, hence the
  explicit `IDiscOb.mk`. Without this rule, the kernel no longer checks `(Bᵒᵖ)ᵒᵖ = B` by `rfl`.

So the context extensions `Γ ▹ Bᵒᵖ` and `Γ ▹ B` are the same, by `rfl`, and Twist-Disc is an
equation between types in this context (`Shared/TwistDisc`).

The rules identify the morphisms `x ⟶ y` of the opposite of a fibre of `B`, which are the morphisms
`y ⟶ x` of the fibre once the opposite is unfolded, with the morphisms `x ⟶ y` of the fibre. These
are different types, equal only by the axiom, and no rule can identify them. So a term built in the
opposite of a discrete type, such as a morphism `β : x ⟶ y` of a fibre seen as one from `y` to `x`
in `Bᵒᵖ`, has a type that the rules make that of a morphism from `y` to `x` of `B`. Proofs avoid
such terms, as `Shared/TwistDisc` does by first making the morphisms of the discrete fibres
identities, or are checked without the rules (`Shared/HomDisc`): only `Shared/TwistDisc`, through
it `Applications/Yoneda`, and the `Readme`s import this file. A discrete type in a form that none of
the rules matches, such as a Σ-type of discrete types in the category model, keeps its opposite.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- **op-Disc for the unfolded opposite, as a rule**: the pointwise opposite of a discrete type,
seen in the category model, is the type. The right-hand side is `B.toFunctor` as a structure, so
that the projections of the opposite reduce after the rule fires. -/
@[rewrite_rule]
theorem comp_opFunctor'_disc (B : IDisc.{u, u}.Ty Γ) :
    B.toFunctor ⋙ opFunctor' =
      CategoryTheory.Functor.mk B.toFunctor.obj B.toFunctor.map B.toFunctor.map_id
        B.toFunctor.map_comp :=
  comp_opFunctor'_of_isDiscrete emptyUnique B.toFunctor B.isDiscrete

/-- **op-Disc in the category model, as a rule**: the opposite of a discrete type, seen in the
category model, is the type, as a structure. -/
@[rewrite_rule]
theorem op_disc_toFunctor (B : IDisc.{u, u}.Ty Γ) :
    CatModel.op B.toFunctor =
      CategoryTheory.Functor.mk B.toFunctor.obj B.toFunctor.map B.toFunctor.map_id
        B.toFunctor.map_comp :=
  comp_opFunctor'_of_isDiscrete emptyUnique B.toFunctor B.isDiscrete

/-- **op-Disc in the category model for a substituted discrete type, as a rule**: the opposite of
`B.toFunctor⦃σ⦄`, unfolded to `σ ⋙ B.toFunctor`, is the type. -/
@[rewrite_rule]
theorem op_disc_comp {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (B : IDisc.{u, u}.Ty Γ) :
    CatModel.op (σ.toFunctor ⋙ B.toFunctor) = σ.toFunctor ⋙ B.toFunctor :=
  comp_opFunctor'_of_isDiscrete emptyUnique _ fun _ => B.isDiscrete _

/-- **op-Disc for the unfolded opposite of a substituted discrete type, as a rule**: the pointwise
opposite of `σ ⋙ B.toFunctor` is the type, as a structure. -/
@[rewrite_rule]
theorem comp_comp_opFunctor'_disc {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (B : IDisc.{u, u}.Ty Γ) :
    (σ.toFunctor ⋙ B.toFunctor) ⋙ opFunctor' =
      CategoryTheory.Functor.mk (σ.toFunctor ⋙ B.toFunctor).obj (σ.toFunctor ⋙ B.toFunctor).map
        (σ.toFunctor ⋙ B.toFunctor).map_id (σ.toFunctor ⋙ B.toFunctor).map_comp :=
  comp_opFunctor'_of_isDiscrete emptyUnique _ fun _ => B.isDiscrete _

/-- **op-Disc for a discrete type seen in the category model through the inclusion, as a rule**: the
opposite of `forgetComprehensionMap.toPre.obj B` (Lift-Form) is the type, as a structure. -/
@[rewrite_rule]
theorem op_disc_forget (B : IDisc.{u, u}.Ty Γ) :
    CatModel.op (forgetComprehensionMap.toPre.obj B) =
      CategoryTheory.Functor.mk B.toFunctor.obj B.toFunctor.map B.toFunctor.map_id
        B.toFunctor.map_comp :=
  comp_opFunctor'_of_isDiscrete emptyUnique B.toFunctor B.isDiscrete

/-- **op-Disc, as a rule**: a discrete type is its own opposite. The right-hand side is `B` as a
structure, so that the projections of `Bᵒᵖ` reduce after the rule fires. -/
@[rewrite_rule]
theorem op_disc (B : IDisc.{u, u}.Ty Γ) : Bᵒᵖ = IDiscOb.mk B.toFunctor B.isDiscrete :=
  op_eq_self emptyUnique B

/-- The context extensions by a discrete type and by its opposite are the same, by `rfl`. -/
example (B : IDisc.{u, u}.Ty Γ) : (Γ ▹ Bᵒᵖ : Cat.{u, u}) = Γ ▹ B :=
  rfl

/-- The context extensions by `Bᵒᵖ` in the discrete model and by its opposite in the category model
are the same (Lift-Ext), by `rfl`, as without the rules. -/
example (B : IDisc.{u, u}.Ty Γ) : (Γ ▹ Bᵒᵖ : Cat.{u, u}) = Γ ▹ CatModel.op B.toFunctor :=
  rfl

/-- op-Disc commutes with substitution, by `rfl`. -/
example {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (B : IDisc.{u, u}.Ty Γ) : (Bᵒᵖ)⦃σ⦄ = B⦃σ⦄ :=
  rfl

/-- The opposite is involutive, by `rfl`, as without the rules. -/
example (B : IDisc.{u, u}.Ty Γ) : (Bᵒᵖ)ᵒᵖ = B :=
  rfl

end ComprehensionCategory.OverCat
