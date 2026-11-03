import Displayed.Opfibration.Straightening.Unstraighten

/-!
# Context extension in the category model

The context extension of `F : A ⥤ Cat` in the category model is the total category of its
unstraightening, `A ⋉ F := (∫ F).Total`: objects are pairs `(a, x)` with `x : F a`,
and a morphism `(a, x) ⟶ (a', y)` is a pair `(f, φ)` with `φ : F f x ⟶ y`. Its identities are
`(𝟙, 𝟙)` and its composites `(f ≫ g, F g φ ≫ ψ)`, by `rfl`. A lax transformation
`α : LaxTrans F (u ⋙ G)` induces the functor `(unstraightenMap α).total : A ⋉ F ⥤ B ⋉ G`, sending
`(f, φ)` to `(u f, α.naturality f x ≫ α φ)`.
-/

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-- `A ⋉ F` is the total category of the unstraightening of `F : A ⥤ Cat`. -/
scoped notation:65 Γ:65 " ⋉ " F:66 => Displayed.Total (A := Γ) (unstraightenObj F)

end ComprehensionCategory.CatModel
