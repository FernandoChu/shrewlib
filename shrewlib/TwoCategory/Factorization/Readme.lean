import TwoCategory.Factorization.AWFS
import TwoCategory.Factorization.Lifting
import TwoCategory.Factorization.Comma.Readme

/-!
# AWFSs in a 2-category

* `AWFS`: AWFSs on a 2-category `B`, a 2-comonad `L` and a 2-monad `R` on `Arr B` forming a
  2-functorial factorization, whose counit and unit are the squares of the factorization, and with
  a distributive law of `L` over `R` formed by the comultiplication and the multiplication. The
  equations of objects and of 1-cells are rules, so those of 1-cells and of 2-cells are stated
  without transport.
* `Lifting`: the chosen diagonal fillers of an AWFS. A square `m : f ⟶ g` from an `L`-coalgebra
  to an `R`-algebra has the filler `lift c a m = s ≫ E m ≫ p`, composed of the nontrivial
  components of the coaction `(𝟙, s)` and of the action `(p, 𝟙)` with the middle map of the
  factorization of `m`. Both triangles commute, and the fillers are functorial in morphisms of
  coalgebras and of algebras.
* `Comma/`: the main example. In a 2-category with comma objects, every 1-cell factors as
  `f = Lf ≫ Rf` through `f/B`, the comma object of `f` and `𝟙 B`; this is an AWFS whose 2-monad `R`
  is lax idempotent, and `R`-algebras are split reflections.
-/

universe w v u

open CategoryTheory TwoCategory

/-! ## Main results -/

/-- The comma factorization is an AWFS. -/
example {B : Type u} [TwoCategory.{w, v} B] [HasCommas B] : AWFS B :=
  commaAWFS B

section Lifting

variable {B : Type u} [TwoCategory.{w, v} B] {A : AWFS B} (c : A.L.Coalg) (a : A.R.Alg)
  (m : c.obj ⟶ a.obj)

/-- The chosen filler makes the upper triangle commute. -/
example : c.obj.hom ≫ AWFS.lift c a m = m.left :=
  AWFS.hom_comp_lift c a m

/-- The chosen filler makes the lower triangle commute. -/
example : AWFS.lift c a m ≫ a.obj.hom = m.right :=
  AWFS.lift_comp_hom c a m

/-- The chosen fillers are functorial in morphisms of coalgebras and of algebras. -/
example {c' : A.L.Coalg} {a' : A.R.Alg} (h : c' ⟶ c) (k : a ⟶ a') :
    AWFS.lift c' a' (h.hom ≫ m ≫ k.hom) = h.hom.right ≫ AWFS.lift c a m ≫ k.hom.left :=
  AWFS.lift_comp c a m h k

end Lifting
