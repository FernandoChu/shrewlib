import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.TypeFormers.Sigma
import Tactic.KernelTactic

/-!
# Σ-types in the category model

For `A : Γ ⥤ Cat` and `B : Γ ⋉ A ⥤ Cat`, the Σ-type `Σ[A] B : Γ ⥤ Cat`
(`CatModel.Sigma.sigma B`) sends `γ` to the total category `A γ ⋉ B(γ, −)` of the
unstraightening of `B` restricted to the fibre over `γ`, and `f : γ ⟶ γ'` to the functor induced
by the strict transformation with components `B(f, 𝟙)`. Then `Γ ▹ A ▹ B = Γ ⋉ A ⋉ B` and
`Γ ▹ Σ[A] B = Γ ⋉ Σ[A] B` are isomorphic over `Γ`, by `((γ, x), b) ↦ (γ, (x, b))`, and the category
model has Σ-types (`CatModel.hasSigma`).

`B(f, 𝟙) ∘ B(𝟙, φ)` and `B(𝟙, F f φ) ∘ B(f, 𝟙)` agree on objects definitionally, since both
composites of morphisms of `Γ ⋉ A` are `(f, F f φ)`, but the functor rules unfold the two into
different terms, which the definitional-equality checker does not identify. So the 2-cells of the
reindexing of `Σ_A B`, and of the pairing, are identities `eqToHom` along such equations, proved by
`rfl`.

Comparing terms that the rules reduce in many steps is slow in the elaborator, which first tries
hard to unify the arguments of applications with the same head, so the expensive steps are checked
in the kernel instead (`kernel_exact`, `kernel_rfl'`), as `kernel_rfl` in `Bicategory/Basic`.
-/

universe v₁ u₁ v u

namespace ComprehensionCategory

open CategoryTheory Displayed Displayed.Opfibration.Straightening CatModel

namespace CatModel.Sigma

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{v, u}} (B : A ⋉ F ⥤ Cat.{v, u})

/-- The restriction `B(a, −) : F a ⥤ Cat` of `B` to the fibre over `a`. -/
abbrev fib (a : A) : F.obj a ⥤ Cat.{v, u} := incl F a ⋙ B

/-- The transformation `B(f, 𝟙) : B(a, −) ⇒ B(a', F f −)`, strictly natural. -/
def sigmaTrans {a a' : A} (f : a ⟶ a') :
    LaxTrans (fib B a) ((F.map f).toFunctor ⋙ fib B a') where
  app x := (B.map (transport F f x)).toFunctor
  naturality φ b := eqToHom (obj_transport_comm B f φ b)
  naturality_naturality φ _ _ β :=
    map_comp_eqToHom (congrArg (fun k => (B.map k).toFunctor) (transport_comm F f φ)) β
  naturality_id _ := eqToHom_refl _ _
  naturality_comp φ ψ b := by
    rw [eqToHom_map, eqToHom_trans]

theorem sigmaTrans_id (a : A) :
    sigmaTrans B (𝟙 a) = (LaxTrans.id (fib B a) :
      LaxTrans (fib B a) ((F.map (𝟙 a)).toFunctor ⋙ fib B a)) :=
  LaxTrans.ext' (fun _ _ => by kernel_rfl') (fun _ _ _ _ => by kernel_rfl') fun φ b => by
    kernel_exact eqToHom_refl _ (obj_transport_comm B (𝟙 a) φ b)

theorem sigmaTrans_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    sigmaTrans B (f ≫ g) = ((sigmaTrans B f).vcomp ((sigmaTrans B g).whiskerLeft
      (F.map f).toFunctor) :
        LaxTrans (fib B a) ((F.map (f ≫ g)).toFunctor ⋙ fib B a'')) :=
  LaxTrans.ext' (fun _ _ => by kernel_rfl') (fun _ _ _ _ => by kernel_rfl') fun {x x'} φ b => by
    kernel_exact eqToHom_eq_comp_map_eqToHom
      (B.map (transport F g ((F.map f).toFunctor.obj x'))).toFunctor
      (obj_transport_comm B (f ≫ g) φ b)
      (obj_transport_comm B g ((F.map f).toFunctor.map φ)
        ((B.map (transport F f x)).toFunctor.obj b))
      (obj_transport_comm B f φ b)

/-- The Σ-type `Σ_F B : A ⥤ Cat`, sending `a` to `F a ⋉ B(a, −)`. -/
def sigma : A ⥤ Cat.{v, u} where
  obj a := Cat.of (F.obj a ⋉ fib B a)
  map f := (unstraightenMap (u := (F.map f).toFunctor) (sigmaTrans B f)).total.toCatHom
  map_id a := Cat.Hom.ext ((congrArg (fun α => (unstraightenMap α).total)
    (sigmaTrans_id B a)).trans (total_unstraightenMap_id _))
  map_comp f g := Cat.Hom.ext ((congrArg (fun α => (unstraightenMap α).total)
    (sigmaTrans_comp B f g)).trans (total_unstraightenMap_vcomp _ _ _ _ _))

/-! ## The isomorphism `Γ.A.B ≅ Γ.Σ_A B` -/

/-- The transformation `B ⇒ π ⋙ Σ_F B` including `B(a, x)` into `F a ⋉ B(a, −)`, whose 2-cells
are the morphisms `(φ, 𝟙) : (F f x, B(f, 𝟙) b) ⟶ (x', B(f, φ) b)`. -/
def pairTrans : LaxTrans B (π F ⋙ Sigma.sigma B) where
  app X := incl (fib B X.1) X.2
  naturality k b := (unstraightenObj (fib B _)).totalMk k.fiber (eqToHom (obj_transport_incl B k b))
  naturality_naturality {X Y} k {b b'} β := Total.Hom.ext' (by kernel_rfl') (by
    kernel_exact map_eqToHom_comp_map_map (B.map (transport F k.base X.2)).toFunctor
      (B.map ((incl F Y.1).map k.fiber)).toFunctor
      (congrArg (fun k' => (B.map k').toFunctor) (transport_incl F k))
      (obj_transport_comm B k.base (𝟙 X.2) b) β)
  naturality_id {X} b := Total.Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_refl _ (obj_transport_incl B (𝟙 X) b))
  naturality_comp {X Y Z} k l b := Total.Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_eq_map_map_comp (B.map ((incl F Z.1).map l.fiber)).toFunctor
      (B.map (transport F l.base Y.2)).toFunctor (obj_transport_incl B (k ≫ l) b)
      (obj_transport_comm B l.base k.fiber ((B.map (transport F k.base X.2)).toFunctor.obj b))
      (obj_transport_incl B k b) (obj_transport_incl B l ((B.map k).toFunctor.obj b)))

/-- `((a, x), b) ↦ (a, (x, b))`. -/
def pair : A ⋉ F ⋉ B ⥤ A ⋉ Sigma.sigma B := (unstraightenMap (u := π F) (pairTrans B)).total

/-- The object `((a, x), b)` of `A ⋉ F ⋉ B` of an object `(a, (x, b))` of `A ⋉ Σ_F B`. -/
abbrev unpairObj (X : A ⋉ Sigma.sigma B) : A ⋉ F ⋉ B :=
  (unstraightenObj B).tot (a := (unstraightenObj F).tot X.2.1) X.2.2

/-- `(a, (x, b)) ↦ ((a, x), b)` on morphisms. -/
def unpairMap {X Y : A ⋉ Sigma.sigma B} (k : X ⟶ Y) : unpairObj B X ⟶ unpairObj B Y :=
  (unstraightenObj B).totalMk ((unstraightenObj F).totalMk k.base k.fiber.base)
    (eqToHom (obj_transport_incl B ((unstraightenObj F).totalMk k.base k.fiber.base)
      X.2.2).symm ≫ k.fiber.fiber)

theorem unpairMap_pair_map {X Y : A ⋉ F ⋉ B} (k : X ⟶ Y) :
    unpairMap B ((pair B).map k) = k :=
  Total.Hom.ext' (by kernel_rfl') (by
    kernel_exact eqToHom_comp_eqToHom_comp
      (obj_transport_incl B ((unstraightenObj F).totalMk k.base.base k.base.fiber) X.2).symm
      (obj_transport_incl B k.base X.2) k.fiber)

theorem pair_map_unpairMap {X Y : A ⋉ Sigma.sigma B} (k : X ⟶ Y) :
    (pair B).map (unpairMap B k) = k :=
  Total.Hom.ext' (by kernel_rfl') (Total.Hom.hext (by kernel_rfl') (by kernel_rfl')
    (by kernel_rfl') (by
    kernel_exact eqToHom_comp_eqToHom_comp
      (obj_transport_incl B ((unstraightenObj F).totalMk k.base k.fiber.base) X.2.2)
      (obj_transport_incl B ((unstraightenObj F).totalMk k.base k.fiber.base) X.2.2).symm
      k.fiber.fiber))

/-- `(a, (x, b)) ↦ ((a, x), b)`, inverse to `pair`. -/
def unpair : A ⋉ Sigma.sigma B ⥤ A ⋉ F ⋉ B where
  obj X := unpairObj B X
  map k := unpairMap B k
  map_id X := by
    kernel_exact (congrArg (unpairMap B) ((pair B).map_id (unpairObj B X))).symm.trans
      (unpairMap_pair_map B (𝟙 (unpairObj B X)))
  map_comp {X Y Z} k l := by
    have h : (pair B).map (unpairMap B k ≫ unpairMap B l) = k ≫ l := by
      rw [Functor.map_comp]
      kernel_exact congrArg₂ (· ≫ ·) (pair_map_unpairMap B k) (pair_map_unpairMap B l)
    kernel_exact (congrArg (unpairMap B) h).symm.trans
      (unpairMap_pair_map B (unpairMap B k ≫ unpairMap B l))

theorem pair_unpair : pair B ⋙ unpair B = 𝟭 _ :=
  Functor.hext (fun _ => by kernel_rfl') fun _ _ k => by kernel_exact unpairMap_pair_map B k

theorem unpair_pair : unpair B ⋙ pair B = 𝟭 _ :=
  Functor.hext (fun _ => by kernel_rfl') fun _ _ k => by kernel_exact pair_map_unpairMap B k

theorem pair_π : pair B ⋙ π (Sigma.sigma B) = π B ⋙ π F :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end CatModel.Sigma

/-! ## The category model has Σ-types -/

namespace CatModel

variable {Γ : Cat.{u, u}} (A : Γ ⥤ Cat.{u, u}) (B : Γ ⋉ A ⥤ Cat.{u, u})

/-- The Σ-type `Σ_A B` of the category model. -/
def sigma : Γ ⥤ Cat.{u, u} := Sigma.sigma B

/-- `Γ.A.B ⟶ Γ.Σ_A B`. -/
def pairHom : Cat.of (Γ ⋉ A ⋉ B) ⟶ Cat.of (Γ ⋉ CatModel.sigma A B) := (Sigma.pair B).toCatHom

/-- `Γ.Σ_A B ⟶ Γ.A.B`. -/
def unpairHom : Cat.of (Γ ⋉ CatModel.sigma A B) ⟶ Cat.of (Γ ⋉ A ⋉ B) :=
  (Sigma.unpair B).toCatHom

/-- The Σ-types of the category model, stable under substitution. -/
instance preSigma : PreSigma ICat.{u} where
  sigma A B := CatModel.sigma A B
  pull_sigma _ _ _ := Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl'

/-- **The category model has Σ-types.** -/
instance hasSigma : HasSigma ICat.{u} where
  pair A B := pairHom A B
  unpair A B := unpairHom A B
  pair_unpair _ B := Cat.Hom.ext (Sigma.pair_unpair B)
  unpair_pair _ B := Cat.Hom.ext (Sigma.unpair_pair B)
  pair_proj _ B := Cat.Hom.ext (Sigma.pair_π B)
  pair_q _ _ _ := Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl')

end CatModel

end ComprehensionCategory
