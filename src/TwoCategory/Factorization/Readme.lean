import TwoCategory.Factorization.AWFS
import TwoCategory.Factorization.Comma.Readme

/-!
# AWFSs in a 2-category

* `AWFS`: AWFSs on a 2-category `B`, a 2-comonad `L` and a 2-monad `R` on `Arr B` forming a
  2-functorial factorization, whose counit and unit are the squares of the factorization, and with
  a distributive law of `L` over `R` formed by the comultiplication and the multiplication. The
  equations of objects and of 1-cells are rules, so those of 1-cells and of 2-cells are stated
  without transport.
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
