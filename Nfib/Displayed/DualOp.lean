import Nfib.Displayed.SplitOpfib

/-!
# The dual opfibration

Given a split opfibration `B` over `A`, its *dual opfibration* `B.dualOp` is the fiberwise
opposite: it has the same displayed objects, but a morphism over `f : a ⟶ a'` from `x` to `y` is a
*vertical* morphism `y ⟶ B.transp f x` in the fiber over `a'`. This corresponds, in the paper, to
the Grothendieck construction of `a ↦ B(a)ᵒᵖ`.

We provide the displayed category `B.dualOp`, the chosen horizontal/vertical morphisms
`dualHoriz`/`dualVert` in its total category, the factorization lemma `dual_factor`, and the
interchange law `dualVert_comp_dualHoriz`.

This is part of milestone **M2** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂

namespace Nfib

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A] (B : Displayed A) [SplitOpfib B]

/-- The fiberwise opposite of a split opfibration `B`: same objects; a morphism over `f : a ⟶ a'`
from `x` to `y` is a vertical morphism `y ⟶ B.transp f x`. -/
noncomputable def dualOp : Displayed A where
  Ob := B.Ob
  Hom {a a'} f x y := (y ⟶[𝟙 a'] (B.transp f x))
  id {a} x := eqToHom (B.transp_id x).symm
  comp {a a' a''} {f g} {x y z} φ ψ := ψ ≫ B.transpMap g φ ≫ eqToHom (B.transp_comp f g x).symm
  -- Each law is an equation between morphisms of the fiber `B.Fiber a'`, once the `castHom` has
  -- been unfolded; `castHom_eq_iff_heq` performs that unfolding, and `conj_eqToHom_iff_heq`
  -- turns the result back into an equation corrected by `eqToHom`. Downstream, no `HEq` is
  -- needed: `dualOp_castHom` below states the unfolding directly.
  id_comp {a a'} {f} {x y} φ := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr (by
    refine (conj_eqToHom_iff_heq _ φ rfl
      (congrArg (fun m => B.transp m x) (Category.id_comp f))).mp ?_
    simp [transpMap_eqToHom])
  comp_id {a a'} {f} {x y} φ := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr (by
    refine (conj_eqToHom_iff_heq _ φ rfl
      (congrArg (fun m => B.transp m x) (Category.comp_id f))).mp ?_
    simp [transpMap_id])
  assoc {a a' a'' a'''} {f g h} {x y z w} φ ψ χ := (DisplayedStruct.castHom_eq_iff_heq _ _).mpr (by
    refine (conj_eqToHom_iff_heq _ _ rfl
      (congrArg (fun m => B.transp m x) (Category.assoc f g h))).mp ?_
    simp [transpMap_comp, transpMap_comp_vert, transpMap_eqToHom])

@[simp] theorem dualOp_Ob (a : A) : (B.dualOp).Ob a = B.Ob a := rfl

@[simp] theorem dualOp_Hom {a a' : A} (f : a ⟶ a') (x : B.Ob a) (y : B.Ob a') :
    (B.dualOp).Hom f x y = (y ⟶[𝟙 a'] B.transp f x) := rfl

@[simp] theorem dualOp_id {a : A} (x : B.Ob a) :
    (B.dualOp).id x = eqToHom (B.transp_id x).symm := rfl

@[simp] theorem dualOp_comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x y z}
    (φ : (B.dualOp).Hom f x y) (ψ : (B.dualOp).Hom g y z) :
    (φ ≫ᵈ ψ) = ψ ≫ B.transpMap g φ ≫ eqToHom (B.transp_comp f g x).symm := rfl

/-- Transporting a `dualOp`-morphism along `h : f = f'` is post-composition with the fiber
`eqToHom` that `h` induces on the pushforward. This is the `dualOp` instance of the
"push `castHom` outwards" normal form. -/
@[simp]
theorem dualOp_castHom {a a' : A} {f f' : a ⟶ a'} {x : B.Ob a} {y : B.Ob a'}
    (φ : (B.dualOp).Hom f x y) (h : f = f') :
    (B.dualOp).castHom φ h = φ ≫ eqToHom (congrArg (fun m : a ⟶ a' => B.transp m x) h) := by
  cases h; simp

section Total

variable {B}

/-- The chosen horizontal morphism of `∫(Bᵈᵒ)` over `α`: the total-category image of the identity
vertical morphism. -/
noncomputable def dualHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    B.dualOp.tot b ⟶ B.dualOp.tot (B.transp α b) :=
  B.dualOp.totalMk α (𝟙 (B.transp α b))

/-- The chosen vertical morphism of `∫(Bᵈᵒ)` associated to `β : b ⟶ b'`; note it is
*contravariant* (it reverses `β`). -/
noncomputable def dualVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    B.dualOp.tot b' ⟶ B.dualOp.tot b :=
  B.dualOp.totalMk (𝟙 a) (β ≫ eqToHom (B.transp_id b').symm)

@[simp] theorem dualHoriz_base {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    (dualHoriz α b).base = α := rfl

@[simp] theorem dualHoriz_fiber {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    (dualHoriz α b).fiber = 𝟙 (B.transp α b) := rfl

@[simp] theorem dualVert_base {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualVert β).base = 𝟙 a := rfl

@[simp] theorem dualVert_fiber {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualVert β).fiber = β ≫ eqToHom (B.transp_id b').symm := rfl

@[simp] theorem π_map_dualHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    (B.dualOp.π).map (dualHoriz α b) = α := rfl

@[simp] theorem π_map_dualVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (B.dualOp.π).map (dualVert β) = 𝟙 a := rfl

/-- `dualHoriz` is a congruence for `≍` in the base morphism. -/
theorem dualHoriz_heq {a a' : A} {α α₂ : a ⟶ a'} (h : α = α₂) (b : B.Ob a) :
    dualHoriz α b ≍ dualHoriz α₂ b := by subst h; rfl

/-- Extensionality for morphisms of `∫(Bᵈᵒ)` with common endpoints: it suffices to compare the base
morphisms and the fibers, the latter after the `eqToHom` correcting for the base discrepancy. -/
theorem dualOp_hom_ext {a a' : A} {b : B.Ob a} {b' : B.Ob a'}
    {F G : B.dualOp.tot b ⟶ B.dualOp.tot b'} (hbase : F.base = G.base)
    (h : F.fiber
      = G.fiber ≫ eqToHom (congrArg (fun m : a ⟶ a' => B.transp m b) hbase.symm)) : F = G :=
  Total.hom_ext _ hbase (by rw [h]; exact comp_eqToHom_heq _ _)

@[simp]
theorem dualVert_id {a : A} (b : B.Fiber a) : dualVert (𝟙 b) = 𝟙 (B.dualOp.tot b) :=
  dualOp_hom_ext (by simp) (by simp)

/-- `dualVert` is contravariant. -/
theorem dualVert_comp {a : A} {b₁ b₂ b₃ : B.Fiber a} (u : b₁ ⟶ b₂) (v : b₂ ⟶ b₃) :
    dualVert (u ≫ v) = dualVert v ≫ dualVert u :=
  dualOp_hom_ext (by simp) (by simp [transpMap_id, transpMap_comp_vert])

/-- `dualVert` of an `eqToHom` is an `eqToHom` of `∫(Bᵈᵒ)`. -/
theorem dualVert_eqToHom {a : A} {b b' : B.Fiber a} (h : b = b') :
    dualVert (eqToHom h) = eqToHom (congrArg (B.dualOp.tot (a := a)) h.symm) := by
  subst h; simp

/-- Every morphism of `∫(Bᵈᵒ)` factors as a chosen horizontal morphism followed by a vertical
one (the plan's `dual_factor`). -/
@[reassoc]
theorem dual_factor {a a' : A} {b : B.Ob a} {b' : B.Ob a'}
    (F : B.dualOp.tot b ⟶ B.dualOp.tot b') : F = dualHoriz F.base b ≫ dualVert F.fiber :=
  dualOp_hom_ext (by simp) (by simp [transpMap_id_vert])

/-- Interchange in `∫(Bᵈᵒ)`: pushing a vertical morphism past a chosen horizontal morphism
transports it along `B.transpMap`. -/
@[reassoc]
theorem dualVert_comp_dualHoriz {a a' : A} (α : a ⟶ a') {b b' : B.Fiber a} (β : b ⟶ b') :
    dualVert β ≫ dualHoriz α b = dualHoriz α b' ≫ dualVert (B.transpMap α β) :=
  dualOp_hom_ext (by simp) (by simp [transpMap_comp_vert, transpMap_id_vert])

/-- The chosen horizontal morphism over an identity is the `eqToHom` of `transp_id`. -/
theorem dualHoriz_id {a : A} (b : B.Ob a) :
    dualHoriz (𝟙 a) b = dualVert (eqToHom (B.transp_id b)) :=
  dualOp_hom_ext (by simp) (by simp)

/-- Splitness of `∫(Bᵈᵒ)`: the chosen horizontal morphism over a composite is the composite of the
chosen horizontal morphisms, corrected by the `eqToHom` of `transp_comp`. -/
@[reassoc]
theorem dualHoriz_comp {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    dualHoriz α b ≫ dualHoriz α' (B.transp α b)
        ≫ dualVert (eqToHom (B.transp_comp α α' b))
      = dualHoriz (α ≫ α') b :=
  dualOp_hom_ext (by simp) (by simp [transpMap_id_vert])

end Total

end Displayed

end Nfib
