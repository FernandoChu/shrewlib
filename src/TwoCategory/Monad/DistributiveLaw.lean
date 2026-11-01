import TwoCategory.Monad.Basic

/-!
# Distributive laws of a 2-comonad over a 2-monad

A *distributive law* of a 2-comonad `L` over a 2-monad `R` on a 2-category `C` is a 2-natural
transformation `λ_x : L (R x) ⟶ R (L x)` compatible with the unit and multiplication of `R` and
the counit and comultiplication of `L`:
```
L η_x ≫ λ_x = η_{L x}                       λ_x ≫ R ε_x = ε_{R x}
L μ_x ≫ λ_x = λ_{R x} ≫ R λ_x ≫ μ_{L x}     λ_x ≫ R δ_x = δ_{R x} ≫ L λ_x ≫ λ_{L x}
```
As for 2-monads (`TwoCategory.Monad.Basic`), the 1-dimensional naturality of `λ` is a rule, so its
2-dimensional naturality is stated without transport, and the 1-dimensional data
(`PreDistributiveLaw`) is a field of `DistributiveLaw` rather than a parent.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {C : Type u} [TwoCategory.{w, v} C]

/-- The 1-dimensional data of a distributive law of a 2-comonad `L` over a 2-monad `R`: a
1-natural transformation `L R ⟶ R L` compatible with the units, counits, multiplications and
comultiplications. -/
structure PreDistributiveLaw (L : PreTwoComonad C) (R : PreTwoMonad C) where
  /-- The component `L (R x) ⟶ R (L x)`. -/
  app (x : C) : L.T.obj (R.T.obj x) ⟶ R.T.obj (L.T.obj x)
  naturality {x y : C} (m : x ⟶ y) : L.T.map (R.T.map m) ≫ app y = app x ≫ R.T.map (L.T.map m)
  unit (x : C) : L.T.map (R.η x) ≫ app x = R.η (L.T.obj x)
  mult (x : C) :
    L.T.map (R.μ x) ≫ app x = app (R.T.obj x) ≫ R.T.map (app x) ≫ R.μ (L.T.obj x)
  counit (x : C) : app x ≫ R.T.map (L.ε x) = L.ε (R.T.obj x)
  comult (x : C) :
    app x ≫ R.T.map (L.δ x) = L.δ (R.T.obj x) ≫ L.T.map (app x) ≫ app (L.T.obj x)

attribute [rewrite_rule] PreDistributiveLaw.naturality

namespace PreDistributiveLaw

variable {L : PreTwoComonad C} {R : PreTwoMonad C} (D : PreDistributiveLaw L R)

@[rewrite_rule]
theorem naturality_assoc {x y z : C} (m : x ⟶ y) (k : R.T.obj (L.T.obj y) ⟶ z) :
    L.T.map (R.T.map m) ≫ D.app y ≫ k = D.app x ≫ R.T.map (L.T.map m) ≫ k :=
  congrArg (· ≫ k) (D.naturality m)

end PreDistributiveLaw

/-- A distributive law of a 2-comonad `L` over a 2-monad `R`: a `PreDistributiveLaw` that is also
2-natural. -/
structure DistributiveLaw (L : TwoComonad C) (R : TwoMonad C) where
  /-- The 1-dimensional data. -/
  toPreDistributiveLaw : PreDistributiveLaw L.toPreTwoComonad R.toPreTwoMonad
  naturality₂ {x y : C} {m n : x ⟶ y} (α : m ⟶ n) :
    L.toPreTwoComonad.T.map₂ (R.toPreTwoMonad.T.map₂ α) ▷ toPreDistributiveLaw.app y =
      toPreDistributiveLaw.app x ◁ R.toPreTwoMonad.T.map₂ (L.toPreTwoComonad.T.map₂ α)

/-- The component `L (R x) ⟶ R (L x)`. -/
abbrev DistributiveLaw.app {L : TwoComonad C} {R : TwoMonad C} (D : DistributiveLaw L R)
    (x : C) : L.T.obj (R.T.obj x) ⟶ R.T.obj (L.T.obj x) :=
  D.toPreDistributiveLaw.app x

end CategoryTheory.TwoCategory
