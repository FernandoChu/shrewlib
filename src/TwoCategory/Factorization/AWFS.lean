import TwoCategory.Constructions.Arrow
import TwoCategory.Monad.DistributiveLaw

/-!
# AWFSs on a 2-category

An AWFS on a 2-category `B` (Bourke–Garner, *AWFS I*, here strict and 2-categorical) is a
2-comonad `L` and a 2-monad `R` on the arrow 2-category `Arr B` such that:

* `L` and `R` form a 2-functorial factorization: each arrow `f` factors as `f = L f ≫ R f`, each
  square `m : f ⟶ g` as `L m ≫ R m` with `L m = (m.left, E m)` and `R m = (E m, m.right)` sharing
  their middle component, and likewise each 2-cell of squares;
* the counit of `L` is the square `(𝟙, R f) : L f ⟶ f`, and the unit of `R` is the square
  `(L f, 𝟙) : f ⟶ R f`;
* the squares `(δ_f.right, μ_f.left) : L (R f) ⟶ R (L f)`, formed by the comultiplication of `L`
  and the multiplication of `R`, are a distributive law of `L` over `R`
  (`TwoCategory.Monad.DistributiveLaw`).

The equations of objects, that `L f` starts at the domain of `f`, `R f` ends at its codomain, and
`L f` ends where `R f` starts, are rules, so the equations of 1-cells are stated without transport;
likewise the equations of 1-cells are rules, so those of 2-cells are stated without transport. As
the fields of a structure are local variables while it is elaborated, these come in three layers,
each a field of the next: `AWFSData` (objects), `PreAWFS` (1-cells) and `AWFS` (2-cells). Some
equations follow from the others, such as `L f ≫ R f = f` from the form of the counit, but are
fields so that they are rules.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable (B : Type u) [TwoCategory.{w, v} B]

/-- The data of an AWFS on `B`: a 2-comonad `L` and a 2-monad `R` on `Arr B` such that `L f` starts
at the domain of `f`, `R f` ends at its codomain, and `L f` ends where `R f` starts. -/
structure AWFSData where
  /-- The left 2-comonad. -/
  L : TwoComonad (Arr B)
  /-- The right 2-monad. -/
  R : TwoMonad (Arr B)
  L_obj_dom (f : Arr B) : (L.T.obj f).dom = f.dom
  R_obj_cod (f : Arr B) : (R.T.obj f).cod = f.cod
  L_obj_cod (f : Arr B) : (L.T.obj f).cod = (R.T.obj f).dom

attribute [rewrite_rule] AWFSData.L_obj_dom AWFSData.R_obj_cod AWFSData.L_obj_cod

/-- The 1-dimensional part of an AWFS on `B`: `L` and `R` factor arrows and squares, the counit of
`L` and the unit of `R` are the squares of the factorization, and the squares formed by the
comultiplication of `L` and the multiplication of `R` are a distributive law of `L` over `R`. -/
structure PreAWFS where
  /-- The 2-comonad and the 2-monad. -/
  toAWFSData : AWFSData B
  fac (f : Arr B) : (toAWFSData.L.T.obj f).hom ≫ (toAWFSData.R.T.obj f).hom = f.hom
  L_map_left {f g : Arr B} (m : f ⟶ g) : (toAWFSData.L.T.map m).left = m.left
  R_map_right {f g : Arr B} (m : f ⟶ g) : (toAWFSData.R.T.map m).right = m.right
  L_map_right {f g : Arr B} (m : f ⟶ g) :
    (toAWFSData.L.T.map m).right = (toAWFSData.R.T.map m).left
  ε_left (f : Arr B) : (toAWFSData.L.ε f).left = 𝟙 f.dom
  ε_right (f : Arr B) : (toAWFSData.L.ε f).right = (toAWFSData.R.T.obj f).hom
  η_left (f : Arr B) : (toAWFSData.R.η f).left = (toAWFSData.L.T.obj f).hom
  η_right (f : Arr B) : (toAWFSData.R.η f).right = 𝟙 f.cod
  /-- The distributive law of `L` over `R`. -/
  dist : DistributiveLaw toAWFSData.L toAWFSData.R
  dist_left (f : Arr B) : (dist.app f).left = (toAWFSData.L.δ f).right
  dist_right (f : Arr B) : (dist.app f).right = (toAWFSData.R.μ f).left

attribute [rewrite_rule] PreAWFS.fac PreAWFS.L_map_left PreAWFS.R_map_right PreAWFS.L_map_right
  PreAWFS.ε_left PreAWFS.ε_right PreAWFS.η_left PreAWFS.η_right PreAWFS.dist_left
  PreAWFS.dist_right

@[rewrite_rule]
theorem PreAWFS.fac_assoc {B : Type u} [TwoCategory.{w, v} B] (A : PreAWFS B) (f : Arr B) {z : B}
    (k : f.cod ⟶ z) :
    (A.toAWFSData.L.T.obj f).hom ≫ (A.toAWFSData.R.T.obj f).hom ≫ k = f.hom ≫ k :=
  congrArg (· ≫ k) (A.fac f)

/-- An AWFS on `B`: a `PreAWFS` whose factorization is 2-functorial, factoring each 2-cell of
squares `α` into `L α` and `R α` sharing their middle component. -/
structure AWFS where
  /-- The 1-dimensional part. -/
  toPreAWFS : PreAWFS B
  L_map₂_left {f g : Arr B} {m n : f ⟶ g} (α : m ⟶ n) :
    (toPreAWFS.toAWFSData.L.T.map₂ α).left = α.left
  R_map₂_right {f g : Arr B} {m n : f ⟶ g} (α : m ⟶ n) :
    (toPreAWFS.toAWFSData.R.T.map₂ α).right = α.right
  L_map₂_right {f g : Arr B} {m n : f ⟶ g} (α : m ⟶ n) :
    (toPreAWFS.toAWFSData.L.T.map₂ α).right = (toPreAWFS.toAWFSData.R.T.map₂ α).left

attribute [rewrite_rule] AWFS.L_map₂_left AWFS.R_map₂_right AWFS.L_map₂_right

end CategoryTheory.TwoCategory
