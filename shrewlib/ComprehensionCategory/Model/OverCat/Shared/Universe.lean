import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Universe
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Op
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The universes of discrete and of contravariant types

The category model at level `v + 1`, with contexts in `Cat.{v + 1, v + 1}`, has a Coquand-style
universe `UDisc Γ` of the discrete types of level `v`, the functors `Γ ⥤ Cat.{v, v}` into discrete
categories (`IDiscOb.{v, v} Γ`, the types of `SmallIDisc`, `Discrete/Small`): it is a type of the
category model, whose terms `Tm(Γ, UDisc Γ)` are exactly these functors, by inverse maps `ElDisc`
and `codeDisc`, all stable under substitution. This is a universe in the sense of
`ComprehensionCategory/TypeFormers/Universe`: `HasUniverse ICatLax SmallIDisc`.

As for the universe `U Γ` of all the types of level `v` (`Cat/TypeFormers/Universe`), `UDisc Γ` is
a constant type: at `smallDiscCat`, the full subcategory of `Cat.{v, v}` on the discrete categories,
made a category of `Cat.{v + 1, v + 1}` by `AsSmall`. It is not itself discrete: its morphisms are
the functors between discrete categories. Its terms are the functors `Γ ⥤ smallDiscCat`
(`Tm.constEquiv`), and `ElDisc` and `codeDisc` compose this with `AsSmall.down` followed by the
inclusion of the full subcategory, and with the lift into the full subcategory followed by
`AsSmall.up`. `ElDisc (codeDisc A) = A` holds componentwise by `rfl`, and
`codeDisc (ElDisc t) = t` since `t` is the term of its values. The universe is closed by `rfl`
(`pull_UDisc`), and `ElDisc` and `codeDisc` commute with substitution (`ElDisc_pull`,
`codeDisc_pull`).

A term `t` of the universe decodes to the type `lift (ElDisc t)` of the category model, along the
lift of the discrete types of level `v`, a strict map of comprehension categories
(`Displayed.decode liftDiscComprehensionMap`), and the discrete types of level `v` are types of the
discrete model too, by `liftDisc` (`Discrete/Small`).

## The universe of contravariant types

The category model also has a Coquand-style universe `Uop Γ` of the contravariant types of level
`v`, the functors `Γᵒᵖ ⥤ Cat.{v, v}` (`SmallICatOp`, `CatOp/Small`): `HasUniverse ICatLax
SmallICatOp`. It is the constant type at the opposite `opFunctor'.obj smallCat` of the category of
small categories, which is the opposite type of the universe `U Γ` by `rfl` (`Uop_eq_op`), the
paper's `U^op`. Its terms are the functors `Γ ⥤ opFunctor'.obj smallCat`, which are the functors
`Γᵒᵖ ⥤ smallCat` (`unopFunctor`, with inverse `opFunctor`), with the same components: `ElOp` and
`codeOp` compose these with `AsSmall.down` and `AsSmall.up`. Their laws hold as for `U`, and `ElOp`
commutes with substitution, `σ` acting on the contravariant types by `σ.op`.

A term of `Uop Γ` decodes to a type of the contravariant category model, not of the category model,
along the lift of the contravariant types of level `v` into it, a strict map of comprehension
categories (`Displayed.decode liftOpComprehensionMap`).
-/

universe v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening
  CatModel DiscreteModel

open scoped Displayed

/-- Being discrete, a property of small categories. -/
def isDiscreteCat : ObjectProperty Cat.{v, v} :=
  fun C => IsDiscrete C

/-- The category of small discrete categories, the full subcategory of `Cat.{v, v}` on the discrete
categories, made a category of `Cat.{v + 1, v + 1}` by `AsSmall`. -/
def smallDiscCat : Cat.{v + 1, v + 1} :=
  Cat.of (AsSmall.{v + 1} isDiscreteCat.{v}.FullSubcategory)

/-- **The universe of discrete types** in context `Γ`: the constant type at the category of small
discrete categories. -/
def UDisc (Γ : Cat.{v + 1, v + 1}) : ICatLax.{v + 1, v + 1}.Ty Γ :=
  constTy Γ smallDiscCat

variable {Γ Δ : Cat.{v + 1, v + 1}}

/-- The discrete type of level `v` decoded from a term `t` of the universe: its values. -/
def ElDisc (t : Tm(Γ, UDisc Γ)) : IDiscOb.{v, v} Γ where
  toFunctor := Tm.toConst t ⋙ AsSmall.down ⋙ isDiscreteCat.ι
  isDiscrete γ := (ULift.down ((Tm.toConst t).obj γ)).property

/-- The code of a discrete type `A` of level `v`, a term of the universe: the term of its values. -/
def codeDisc (A : IDiscOb.{v, v} Γ) : Tm(Γ, UDisc Γ) :=
  Tm.ofConst (isDiscreteCat.lift A.toFunctor A.isDiscrete ⋙ AsSmall.up)

/-- `ElDisc` undoes `codeDisc`. -/
theorem ElDisc_codeDisc (A : IDiscOb.{v, v} Γ) : ElDisc (codeDisc A) = A :=
  IDiscOb.ext (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl)

/-- `codeDisc` undoes `ElDisc`: a term is the term of its values. -/
theorem codeDisc_ElDisc (t : Tm(Γ, UDisc Γ)) : codeDisc (ElDisc t) = t :=
  (congrArg Tm.ofConst (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl :
    isDiscreteCat.lift (ElDisc t).toFunctor (ElDisc t).isDiscrete ⋙ AsSmall.up =
      Tm.toConst t)).trans (Tm.ofConst_toConst t)

/-- **The universe of discrete types is closed**: it is stable under substitution. -/
theorem pull_UDisc (σ : Δ ⟶ Γ) : (UDisc Γ)⦃σ⦄ = UDisc Δ :=
  rfl

/-- `ElDisc` commutes with substitution. -/
theorem ElDisc_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, UDisc Γ)) :
    ElDisc (Γ := Δ) t⦃σ⦄ = SmallIDisc.pull σ (ElDisc t) :=
  IDiscOb.ext ((congrArg (· ⋙ AsSmall.down ⋙ isDiscreteCat.ι) (Tm.toConst_pull σ t)).trans
    (Functor.assoc _ _ _))

/-- `codeDisc` commutes with substitution. -/
theorem codeDisc_pull (σ : Δ ⟶ Γ) (A : IDiscOb.{v, v} Γ) :
    (codeDisc A)⦃σ⦄ = codeDisc (SmallIDisc.pull σ A) :=
  (Tm.ofConst_pull σ _).trans (congrArg Tm.ofConst
    (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl))

/-- The universe of the discrete types of level `v` in the category model. -/
instance preUniverseDisc : PreUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1} SmallIDisc.{v} where
  univ Γ := UDisc Γ
  pull_univ σ := pull_UDisc σ

/-- **The category model has a Coquand-style universe of the discrete types of level `v`.** -/
instance hasUniverseDisc : HasUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1} SmallIDisc.{v} where
  El t := ElDisc t
  code A := codeDisc A
  El_code A := ElDisc_codeDisc A
  code_El t := codeDisc_ElDisc t
  El_pull σ t := ElDisc_pull σ t

/-! ## The universe of contravariant types -/

/-- A functor into the opposite of a category `K` as a functor from the opposite into `K`. -/
def unopFunctor {C : Type (v + 1)} [Category.{v + 1} C] {K : Cat.{v + 1, v + 1}}
    (F : C ⥤ opFunctor'.obj K) : Cᵒᵖ ⥤ K where
  obj x := F.obj x.unop
  map f := F.map f.unop
  map_id x := F.map_id x.unop
  map_comp f g := F.map_comp g.unop f.unop

/-- A functor from the opposite into a category `K` as a functor into the opposite of `K`. -/
def opFunctor {C : Type (v + 1)} [Category.{v + 1} C] {K : Cat.{v + 1, v + 1}} (G : Cᵒᵖ ⥤ K) :
    C ⥤ opFunctor'.obj K where
  obj x := G.obj (Opposite.op x)
  map f := G.map f.op
  map_id x := G.map_id (Opposite.op x)
  map_comp f g := G.map_comp g.op f.op

/-- **The universe of contravariant types** in context `Γ`: the constant type at the opposite of the
category of small categories. -/
def Uop (Γ : Cat.{v + 1, v + 1}) : ICatLax.{v + 1, v + 1}.Ty Γ :=
  constTy Γ (opFunctor'.obj smallCat)

/-- The universe of contravariant types is the opposite of the universe of types. -/
theorem Uop_eq_op (Γ : Cat.{v + 1, v + 1}) : Uop Γ = (U Γ)ᵒᵖ :=
  rfl

/-- The contravariant type of level `v` decoded from a term `t` of the universe: its values, seen
contravariantly. -/
def ElOp (t : Tm(Γ, Uop Γ)) : Γᵒᵖ ⥤ Cat.{v, v} :=
  unopFunctor (Tm.toConst t) ⋙ AsSmall.down

/-- The code of a contravariant type `A` of level `v`, a term of the universe: the term of its
values. -/
def codeOp (A : Γᵒᵖ ⥤ Cat.{v, v}) : Tm(Γ, Uop Γ) :=
  Tm.ofConst (opFunctor (A ⋙ AsSmall.up))

/-- `ElOp` undoes `codeOp`. -/
theorem ElOp_codeOp (A : Γᵒᵖ ⥤ Cat.{v, v}) : ElOp (codeOp A) = A :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- `codeOp` undoes `ElOp`: a term is the term of its values. -/
theorem codeOp_ElOp (t : Tm(Γ, Uop Γ)) : codeOp (ElOp t) = t :=
  (congrArg Tm.ofConst (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl :
    opFunctor (ElOp t ⋙ AsSmall.up) = Tm.toConst t)).trans (Tm.ofConst_toConst t)

/-- **The universe of contravariant types is closed**: it is stable under substitution. -/
theorem pull_Uop (σ : Δ ⟶ Γ) : (Uop Γ)⦃σ⦄ = Uop Δ :=
  rfl

/-- `ElOp` commutes with substitution. -/
theorem ElOp_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, Uop Γ)) :
    ElOp (Γ := Δ) t⦃σ⦄ = σ.toFunctor.op ⋙ ElOp t :=
  (congrArg (fun F => unopFunctor F ⋙ AsSmall.down) (Tm.toConst_pull σ t)).trans
    (Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl)

/-- The universe of the contravariant types of level `v` in the category model. -/
instance preUniverseOp : PreUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1}
    CatOpModel.SmallICatOp.{v} where
  univ Γ := Uop Γ
  pull_univ σ := pull_Uop σ

/-- **The category model has a Coquand-style universe of the contravariant types of level `v`.** A
term decodes to a type of the contravariant category model, along the lift
(`Displayed.decode liftOpComprehensionMap`). -/
instance hasUniverseOp : HasUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1}
    CatOpModel.SmallICatOp.{v} where
  El t := ElOp t
  code A := codeOp A
  El_code A := ElOp_codeOp A
  code_El t := codeOp_ElOp t
  El_pull σ t := ElOp_pull σ t

end ComprehensionCategory.OverCat
