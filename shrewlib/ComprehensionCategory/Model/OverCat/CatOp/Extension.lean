import Displayed.Fibration.Straightening.Unstraighten

/-!
# Context extension in the contravariant category model

The context extension of `F : Aᵒᵖ ⥤ Cat` in the contravariant category model is the total category
of its unstraightening, `A ⋉⁻ F := (∫⁻ F).Total`: objects are pairs `(a, x)` with `x : F a`, and a
morphism `(a, x) ⟶ (a', y)` is a pair `(f, φ)` with `φ : x ⟶ F f y`. Its identities are `(𝟙, 𝟙)`
and its composites `(f ≫ g, φ ≫ F f ψ)`, by `rfl`.

This is the dual of `OverCat/Cat/Extension.lean`.
-/

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Displayed Displayed.Fibration.Straightening

/-- `A ⋉⁻ F` is the total category of the unstraightening of `F : Aᵒᵖ ⥤ Cat`. -/
scoped notation:65 Γ:65 " ⋉⁻ " F:66 => Displayed.Total (A := Γ) (unstraightenObj F)

end ComprehensionCategory.CatOpModel
