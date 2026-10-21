import Rules.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The laws of pullback cones as rewrite rules

The equation `t.fst ≫ f ↦ t.snd ≫ g` of a pullback cone `t` over `f` and `g`, and the equations
`lift ≫ t.fst ↦ h`, `lift ≫ t.snd ↦ k` of the morphisms induced by a limit cone, also
reassociated, so that the reassociated composites `t.fst ≫ f ≫ k` rewrite too. Likewise for the
chosen pullbacks `pullback f g` of `HasPullbacks`.
-/

open CategoryTheory Limits

attribute [rewrite_rule] PullbackCone.condition PullbackCone.condition_assoc
  PullbackCone.IsLimit.lift_fst PullbackCone.IsLimit.lift_snd
  PullbackCone.IsLimit.lift_fst_assoc PullbackCone.IsLimit.lift_snd_assoc
  pullback.condition pullback.condition_assoc pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
