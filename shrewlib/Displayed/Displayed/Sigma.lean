import Displayed.Displayed.Total

/-!
# The composite of displayed categories

For `D` displayed over `A` and `E` displayed over the total category `D.Total`, the composite
`D.sigmaDisp E` is displayed over `A`: its objects over `a` are pairs `⟨x, b⟩` of `x : D.Ob a` and
`b` over `⟨a, x⟩`, and its morphisms over `f` are pairs `⟨φ, ψ⟩` of `φ : x ⟶[f] y` and
`ψ : b ⟶[(f, φ)] c`. Its laws are those of `D` and `E`, which hold definitionally.

Its total category is the total category of `E`, up to reassociating the pairs
(`sigmaAssoc` and `sigmaUnassoc`), over `A` and with both composites the identity by `rfl`.

`Opfibration/Sigma.lean` shows that opfibrations compose.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] (D : Displayed.{v₂, u₂} A)
  (E : Displayed.{v₃, u₃} D.Total)

/-- The composite of `D` and of `E` displayed over `D.Total`: objects over `a` are pairs of
`x : D.Ob a` and `b : E.Ob ⟨a, x⟩`, and morphisms over `f` are pairs of `φ : x ⟶[f] y` and
`ψ : b ⟶[(f, φ)] c`. -/
def sigmaDisp : Displayed.{max v₂ v₃, max u₂ u₃} A where
  Ob a := Σ x : D.Ob a, E.Ob (D.tot x)
  Hom f X Y := Σ φ : X.1 ⟶[f] Y.1, E.Hom (D.totalMk f φ) X.2 Y.2
  id X := ⟨𝟙ᵈ X.1, 𝟙ᵈ X.2⟩
  comp φ ψ := ⟨φ.1 ≫ᵈ ψ.1, φ.2 ≫ᵈ ψ.2⟩

/-- `(a, (x, b)) ↦ ((a, x), b)`. -/
def sigmaAssoc : (D.sigmaDisp E).Total ⥤ E.Total where
  obj X := E.tot (a := D.tot X.2.1) X.2.2
  map k := E.totalMk (D.totalMk k.base k.fiber.1) k.fiber.2
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `((a, x), b) ↦ (a, (x, b))`, inverse to `sigmaAssoc`. -/
def sigmaUnassoc : E.Total ⥤ (D.sigmaDisp E).Total where
  obj X := (D.sigmaDisp E).tot (a := X.1.1) ⟨X.1.2, X.2⟩
  map k := (D.sigmaDisp E).totalMk k.base.base ⟨k.base.fiber, k.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem sigmaAssoc_sigmaUnassoc : D.sigmaAssoc E ⋙ D.sigmaUnassoc E = 𝟭 _ :=
  rfl

theorem sigmaUnassoc_sigmaAssoc : D.sigmaUnassoc E ⋙ D.sigmaAssoc E = 𝟭 _ :=
  rfl

/-- Reassociating lies over `A`. -/
theorem sigmaAssoc_π : D.sigmaAssoc E ⋙ E.π ⋙ D.π = (D.sigmaDisp E).π :=
  rfl

theorem sigmaUnassoc_π : D.sigmaUnassoc E ⋙ (D.sigmaDisp E).π = E.π ⋙ D.π :=
  rfl

end Displayed
