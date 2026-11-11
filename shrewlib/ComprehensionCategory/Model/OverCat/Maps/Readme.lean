import ComprehensionCategory.Model.OverCat.Maps.CatOpToDisplayed
import ComprehensionCategory.Model.OverCat.Maps.CatToDisplayed
import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat
import ComprehensionCategory.Model.OverCat.Maps.SmallToCat
import ComprehensionCategory.Model.OverCat.Maps.Unstraighten

/-!
# Maps between the models over `Cat`

Maps of comprehension categories between the models over `Cat`, and their preservation of type
formers, one file per pair of models.

* `DiscreteToCat`: forgetting the discreteness is a strict map from the discrete model to the
  category model, which preserves the Σ-types, the unit types and the opposite types strictly,
  by `rfl`.
* `CatToDisplayed`: a type `C` of the category model is a type `catToDisp C` of the displayed
  model, the straightening of `∫ C`, and this is a strict map, since unstraightening undoes
  straightening on the nose. Its terms are those of `C` (Lift-Intro and Lift-Elim, `tmEquiv`), and
  it preserves unit types strictly, by `rfl`. It preserves Σ-types strictly, but propositionally:
  the counit of straightening–unstraightening at the composite of `∫ A` and `∫ B` casts along
  the functoriality of `B`, and so is the identity.
* `CatOpToDisplayed`: the same for the contravariant category model, `catOpToDisp C`.
* `SmallToCat`: the lifts of the types and of the discrete types of level `v` into the category
  model at level `v + 1`, and of the contravariant types into the contravariant category model,
  are strict maps, along which the terms of the universes of these types decode.
* `Unstraighten`: the unstraightenings, from the category, contravariant, discrete and displayed
  category models to the models of fibrations (`OverCat/Fibred`), preserve the chosen lifts on the
  nose, so that the straightening–unstraightening equivalences are fibred, and are strict maps of
  comprehension categories: each category model is a model of fibrations along its
  unstraightening.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory OverCat Opfibration.Straightening
  Displayed.Discrete.Straightening

/-! ## Main results -/

/-- **Forgetting the discreteness is a strict map of comprehension categories** from the discrete
model to the category model. -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u, u, u, u} ICatLax.{u, u, u, u}

/-- **It preserves Σ-types strictly.** -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap_preservesSigma :
    forgetComprehensionMap.{u}.PreservesSigma

/-- **It preserves unit types strictly.** -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap_preservesUnit :
    forgetComprehensionMap.{u}.PreservesUnit

/-- **It preserves opposite types strictly.** -/
recall ComprehensionCategory.OverCat.forgetComprehensionMap_obj_op {Γ : Cat.{u, u}}
    (A : IDisc.{u, u}.Ty Γ) :
    forgetComprehensionMap.toPre.obj (DiscreteModel.op A) =
      CatModel.op (forgetComprehensionMap.toPre.obj A)

/-- **The inclusion of the category model into the displayed model is a strict map of
comprehension categories.** -/
recall ComprehensionCategory.OverCat.catToDispComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ICatLax.{u, u, u, u}
      Straightening.IProf.{u, u, u}

/-- **Lift-Intro and Lift-Elim**: the terms of `C` are those of `catToDisp C`. -/
recall ComprehensionCategory.OverCat.tmEquivCatToDisp {Γ : Cat.{u, u}}
    (C : ICatLax.{u, u}.Ty Γ) : Tm(Γ, C) ≃ Tm(Γ, catToDisp C)

/-- **It preserves unit types strictly.** -/
recall ComprehensionCategory.OverCat.catToDispComprehensionMap_preservesUnit :
    catToDispComprehensionMap.{u}.PreservesUnit

/-- **It preserves Σ-types strictly**, propositionally. -/
recall ComprehensionCategory.OverCat.catToDispComprehensionMap_preservesSigma :
    catToDispComprehensionMap.{u}.PreservesSigma

/-- **The inclusion of the contravariant category model into the displayed model is a strict map of
comprehension categories**, preserving unit types and Σ-types strictly. -/
recall ComprehensionCategory.OverCat.catOpToDispComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Fibration.Straightening.ICatOpLax.{u, u, u, u}
      Straightening.IProf.{u, u, u}

recall ComprehensionCategory.OverCat.catOpToDispComprehensionMap_preservesUnit :
    catOpToDispComprehensionMap.{u}.PreservesUnit

recall ComprehensionCategory.OverCat.catOpToDispComprehensionMap_preservesSigma :
    catOpToDispComprehensionMap.{u}.PreservesSigma

/-- **The unstraightenings preserve the chosen lifts**: the straightening–unstraightening
equivalences are fibred. -/
recall ComprehensionCategory.OverCat.unstraightenCatCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) ICatLax.{u, u, u, u} SplitOpfibLax.{u, u, u, u}

recall ComprehensionCategory.OverCat.unstraightenCatOpCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) Fibration.Straightening.ICatOpLax.{u, u, u, u}
      SplitFibLax.{u, u, u, u}

recall ComprehensionCategory.OverCat.unstraightenDiscCartesian :
    CartesianFunctor (𝟭 Cat.{u, u}) IDisc.{u, u, u, u} DiscOpfibCat.{u, u, u, u}

/-- **The category models are the models of fibrations along the unstraightenings**, strict maps
of comprehension categories. -/
recall ComprehensionCategory.OverCat.unstraightenCatComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) ICatLax.{u, u, u, u} SplitOpfibLax.{u, u, u, u}

recall ComprehensionCategory.OverCat.unstraightenCatOpComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Fibration.Straightening.ICatOpLax.{u, u, u, u}
      SplitFibLax.{u, u, u, u}

recall ComprehensionCategory.OverCat.unstraightenDiscComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) IDisc.{u, u, u, u} DiscOpfibCat.{u, u, u, u}

recall ComprehensionCategory.OverCat.unstraightenDisplayedComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{u, u}) Straightening.IProf.{u, u, u}
      DisplayedCat.{u, u, u, u}

section Small

universe v

/-- **The lifts of the types of level `v`** are strict maps of comprehension categories. -/
recall ComprehensionCategory.OverCat.liftComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) CatModel.SmallICat.{v}
    ICatLax.{v + 1, v + 1, v + 1, v + 1}

recall ComprehensionCategory.OverCat.liftDiscComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) DiscreteModel.SmallIDisc.{v}
    ICatLax.{v + 1, v + 1, v + 1, v + 1}

recall ComprehensionCategory.OverCat.liftOpComprehensionMap :
    StrictComprehensionMap (𝟭 Cat.{v + 1, v + 1}) CatOpModel.SmallICatOp.{v}
    Fibration.Straightening.ICatOpLax.{v + 1, v + 1, v + 1, v + 1}

end Small
