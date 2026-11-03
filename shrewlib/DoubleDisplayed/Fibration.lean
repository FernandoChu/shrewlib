import DoubleDisplayed.Basic

/-!
# Fibrations of doubly displayed categories

The analogue one level up of the fibrations of `Displayed/Fibration/Basic.lean`: a category `C`
doubly displayed over `B` is a fibration over `B` when it has cartesian lifts of all the morphisms
of `B`, those over arbitrary morphisms of the base `A` included. This is the curried form of a
fibration over the total category of `B`. It is not the local fibration of a D2SFib
(`DoubleDisplayed/D2SFib/Basic.lean`), whose cartesian lifts are only along the vertical morphisms
of `B`, and whose cartesian morphisms (`DoubleDisplayed.IsCartesian`) are so only among the
morphisms over vertical morphisms.

* `IsDDCartesian θ`: `θ : c ⟶[[g]] c'` is cartesian, among the morphisms over arbitrary morphisms
  of `B`. The factorization is data.
* `DDFib`, `PreSplitDDFib` and `SplitDDFib`: cloven, pre-split and split fibrations, as for
  displayed categories. The axioms of the pre-split and split ones are rewrite rules.
* `DDCartesianFunctor C D`: vertical functors between fibrations preserving the chosen cartesian
  lifts on the nose, with the preservation on objects in a separate structure, as for the cartesian
  functors of `Displayed/Fibration/CartesianFunctor.lean`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

open scoped Displayed

namespace DoubleDisplayed

open scoped DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}

/-! ## Cartesian morphisms -/

section Cartesian

variable {C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B}

/-- `θ : c ⟶[[g]] c'` is *cartesian*: every morphism into `c'` over `g₀ ≫ᵈ g` factors uniquely
through `θ` by a morphism over `g₀`, for an arbitrary morphism `g₀` of `B`. The factorization is
data. -/
structure IsDDCartesian {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') where
  /-- The factorization of `χ` through `θ`. -/
  lift : ∀ {a₀ : A} {f₀ : a₀ ⟶ a} {b₀ : B.Ob a₀} (g₀ : b₀ ⟶[f₀] b) {c₀ : C.Ob b₀},
    (c₀ ⟶[[g₀ ≫ᵈ g]] c') → (c₀ ⟶[[g₀]] c)
  lift_fac : ∀ {a₀ : A} {f₀ : a₀ ⟶ a} {b₀ : B.Ob a₀} (g₀ : b₀ ⟶[f₀] b) {c₀ : C.Ob b₀}
    (χ : c₀ ⟶[[g₀ ≫ᵈ g]] c'), lift g₀ χ ≫ᵈᵈ θ = χ
  /-- Any factorization of `χ` through `θ` agrees with `lift`. -/
  lift_uniq : ∀ {a₀ : A} {f₀ : a₀ ⟶ a} {b₀ : B.Ob a₀} {g₀ : b₀ ⟶[f₀] b} {c₀ : C.Ob b₀}
    {χ : c₀ ⟶[[g₀ ≫ᵈ g]] c'} (ψ : c₀ ⟶[[g₀]] c), ψ ≫ᵈᵈ θ = χ → ψ = lift g₀ χ

namespace IsDDCartesian

variable {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'} {c : C.Ob b}
  {c' : C.Ob b'} {θ : c ⟶[[g]] c'}

instance : Subsingleton (IsDDCartesian θ) where
  allEq H H' := by
    obtain ⟨l, fac, _⟩ := H
    obtain ⟨l', _, uniq'⟩ := H'
    obtain rfl : @l = @l' := by
      funext a₀ f₀ b₀ g₀ c₀ χ
      exact uniq' _ (fac g₀ χ)
    rfl

/-- Two maps into `c` that agree after postcomposition with a cartesian `θ` are equal. -/
theorem hom_ext (H : IsDDCartesian θ) {a₀ : A} {f₀ : a₀ ⟶ a} {b₀ : B.Ob a₀} {g₀ : b₀ ⟶[f₀] b}
    {c₀ : C.Ob b₀} {ψ ψ' : c₀ ⟶[[g₀]] c} (h : ψ ≫ᵈᵈ θ = ψ' ≫ᵈᵈ θ) : ψ = ψ' :=
  (H.lift_uniq ψ rfl).trans (H.lift_uniq ψ' h.symm).symm

end IsDDCartesian

end Cartesian

/-! ## The classes -/

/-- A (cloven) fibration structure on a doubly displayed category: a chosen cartesian lift of
every morphism of `B` at every object over its codomain. -/
class DDFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  /-- The chosen pullback of `c'` along `g`. -/
  pull : {a a' : A} → {f : a ⟶ a'} → {b : B.Ob a} → {b' : B.Ob a'} → (g : b ⟶[f] b') →
    C.Ob b' → C.Ob b
  /-- The chosen cartesian lift of `g` at `c'`. -/
  clift : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[f] b') (c' : C.Ob b'),
    pull g c' ⟶[[g]] c'
  /-- The chosen lifts are cartesian. -/
  isCartesianClift : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[f] b')
    (c' : C.Ob b'), IsDDCartesian (clift g c')

/-- A pre-split fibration: the chosen pullbacks are strictly functorial on objects. These axioms
are rewrite rules. -/
class PreSplitDDFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) extends DDFib C where
  pull_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), pull (B.id b) c = c
  pull_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[f] b') (g' : b' ⟶[f'] b'') (c : C.Ob b''),
    pull (g ≫ᵈ g') c = pull g (pull g' c)

attribute [rewrite_rule] PreSplitDDFib.pull_id PreSplitDDFib.pull_comp

/-- A split fibration: a pre-split fibration whose chosen lifts are strictly functorial. As for
`SplitFib`, the pre-split structure is an instance field rather than a parent, so that its rules
apply to the axioms on lifts. -/
class SplitDDFib (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) where
  /-- The underlying pre-split fibration. -/
  [toPreSplitDDFib : PreSplitDDFib C]
  clift_id : ∀ {a : A} {b : B.Ob a} (c : C.Ob b), DDFib.clift (B.id b) c = C.id c
  clift_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {f' : a' ⟶ a''} {b : B.Ob a} {b' : B.Ob a'}
    {b'' : B.Ob a''} (g : b ⟶[f] b') (g' : b' ⟶[f'] b'') (c : C.Ob b''),
    DDFib.clift (g ≫ᵈ g') c = DDFib.clift g (DDFib.pull g' c) ≫ᵈᵈ DDFib.clift g' c

attribute [instance_reducible, instance] SplitDDFib.toPreSplitDDFib

attribute [rewrite_rule] SplitDDFib.clift_id SplitDDFib.clift_comp

/-! ## Cartesian functors -/

variable (C D : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)

/-- A vertical functor preserving the chosen pullbacks on objects. This axiom is a rewrite
rule. -/
structure PreDDCartesianFunctor [DDFib C] [DDFib D] extends VertFunctor C D where
  /-- Preserves the chosen pullbacks on objects. -/
  obj_pull : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[f] b') (c' : C.Ob b'),
    obj (DDFib.pull g c') = DDFib.pull g (obj c')

attribute [rewrite_rule] PreDDCartesianFunctor.obj_pull

/-- **A cartesian functor** of fibrations over `B`: a vertical functor preserving the chosen
cartesian lifts strictly. -/
structure DDCartesianFunctor [DDFib C] [DDFib D] where
  /-- The underlying vertical functor, preserving the chosen pullbacks. -/
  toPre : PreDDCartesianFunctor C D
  /-- Preserves the chosen cartesian lifts. -/
  map_clift : ∀ {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} (g : b ⟶[f] b')
    (c' : C.Ob b'), toPre.map (DDFib.clift g c') = DDFib.clift g (toPre.obj c')

attribute [rewrite_rule] DDCartesianFunctor.map_clift

end DoubleDisplayed
