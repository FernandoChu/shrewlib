import Nfib.Displayed.Double

/-!
# The sigma construction

Given `C : DoubleDisplayed B` (a category doubly displayed over `B → A`), its *sigma* collapses the
two-level chain `C → B → A` into a single displayed category `C.sigma : Displayed A`, whose objects
over `a` are dependent pairs `⟨b, c⟩` with `b : B.Ob a` and `c : C.Ob b`, and whose morphisms are
dependent pairs of a `B`-morphism and a `C`-morphism over it. Its total category is the "associated
category" of the chain.

This is part of milestone **M3/M4** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed

namespace DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A}

/-- A morphism of the sigma construction: a `B`-morphism together with a `C`-morphism over it. -/
structure Sigma.Hom (C : DoubleDisplayed B) {a a' : A} (f : a ⟶ a')
    (x : Σ b : B.Ob a, C.Ob b) (y : Σ b : B.Ob a', C.Ob b) where
  /-- The `B`-component. -/
  base : x.1 ⟶[f] y.1
  /-- The `C`-component, lying over `base`. -/
  fiber : x.2 ⟶[[base]] y.2

/-- Extensionality for sigma morphisms over a fixed base morphism. -/
theorem Sigma.Hom.ext {C : DoubleDisplayed B} {a a' : A} {f : a ⟶ a'}
    {x : Σ b : B.Ob a, C.Ob b} {y : Σ b : B.Ob a', C.Ob b} {F G : Sigma.Hom C f x y}
    (hb : F.base = G.base) (hf : C.castHom F.fiber rfl hb = G.fiber) : F = G := by
  obtain ⟨fb, ff⟩ := F
  obtain ⟨gb, gf⟩ := G
  have hf' : ff ≍ gf := (C.castHom_eq_iff_heq _ _).mp hf
  clear hf
  subst hb
  obtain rfl := eq_of_heq hf'
  rfl

/-- Heterogeneous extensionality: sigma morphisms over propositionally equal base morphisms whose
components agree after `castHom` are `≍`. The conclusion stays a `≍` because the two sigma
hom-*types* differ; `sigma_castHom_eq` below is the `castHom` restatement. -/
theorem Sigma.Hom.hext {C : DoubleDisplayed B} {a a' : A} {f f' : a ⟶ a'}
    {x : Σ b : B.Ob a, C.Ob b} {y : Σ b : B.Ob a', C.Ob b}
    {F : Sigma.Hom C f x y} {G : Sigma.Hom C f' x y}
    (hf : f = f') (hb : B.castHom F.base hf = G.base)
    (hfib : C.castHom F.fiber hf hb = G.fiber) : F ≍ G := by
  obtain ⟨fb, ff⟩ := F
  obtain ⟨gb, gf⟩ := G
  have hb' : fb ≍ gb := (B.castHom_eq_iff_heq _).mp hb
  have hfib' : ff ≍ gf := (C.castHom_eq_iff_heq _ _).mp hfib
  clear hb hfib
  subst hf
  obtain rfl := eq_of_heq hb'
  obtain rfl := eq_of_heq hfib'
  rfl

/-- The sigma construction: collapses the chain `C → B → A` to a single displayed category
`C.sigma : Displayed A`. -/
def sigma (C : DoubleDisplayed B) : Displayed A where
  Ob a := Σ b : B.Ob a, C.Ob b
  Hom f x y := Sigma.Hom C f x y
  id x := ⟨B.id x.1, C.id x.2⟩
  comp F G := ⟨F.base ≫ᵈ G.base, F.fiber ≫ᵈᵈ G.fiber⟩
  -- Each law is componentwise: the `B`-component is the corresponding law of `B` and the
  -- `C`-component the corresponding law of `C`, both already `castHom` equations.
  id_comp F := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr
    (Sigma.Hom.hext (Category.id_comp _) (B.id_comp F.base) (C.id_comp F.fiber))
  comp_id F := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr
    (Sigma.Hom.hext (Category.comp_id _) (B.comp_id F.base) (C.comp_id F.fiber))
  assoc F G H := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr
    (Sigma.Hom.hext (Category.assoc _ _ _) (B.assoc F.base G.base H.base)
      (C.assoc F.fiber G.fiber H.fiber))

@[simp] theorem sigma_Ob (C : DoubleDisplayed B) (a : A) :
    (C.sigma).Ob a = Σ b : B.Ob a, C.Ob b := rfl

/-- Transport in `C.sigma` is transport in each component. -/
@[simp] theorem sigma_castHom_base (C : DoubleDisplayed B) {a a' : A} {f f' : a ⟶ a'}
    {x : (C.sigma).Ob a} {y : (C.sigma).Ob a'} (F : x ⟶[f] y) (h : f = f') :
    ((C.sigma).castHom F h).base = B.castHom F.base h := by cases h; rfl

@[simp] theorem sigma_castHom_fiber (C : DoubleDisplayed B) {a a' : A} {f f' : a ⟶ a'}
    {x : (C.sigma).Ob a} {y : (C.sigma).Ob a'} (F : x ⟶[f] y) (h : f = f') :
    ((C.sigma).castHom F h).fiber = C.castHom F.fiber h (by simp) := by cases h; rfl

@[simp] theorem sigma_id_base (C : DoubleDisplayed B) {a : A} (x : (C.sigma).Ob a) :
    ((C.sigma).id x).base = B.id x.1 := rfl

@[simp] theorem sigma_id_fiber (C : DoubleDisplayed B) {a : A} (x : (C.sigma).Ob a) :
    ((C.sigma).id x).fiber = C.id x.2 := rfl

@[simp] theorem sigma_comp_base (C : DoubleDisplayed B) {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''}
    {x : (C.sigma).Ob a} {y : (C.sigma).Ob a'} {z : (C.sigma).Ob a''}
    (F : x ⟶[f] y) (G : y ⟶[g] z) :
    ((F ≫ᵈ G) : x ⟶[f ≫ g] z).base = F.base ≫ᵈ G.base := rfl

@[simp] theorem sigma_comp_fiber (C : DoubleDisplayed B) {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''}
    {x : (C.sigma).Ob a} {y : (C.sigma).Ob a'} {z : (C.sigma).Ob a''}
    (F : x ⟶[f] y) (G : y ⟶[g] z) :
    ((F ≫ᵈ G) : x ⟶[f ≫ g] z).fiber = F.fiber ≫ᵈᵈ G.fiber := rfl

end DoubleDisplayed

end Nfib
