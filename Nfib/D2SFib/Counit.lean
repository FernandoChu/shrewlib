import Nfib.D2SFib.Grothendieck
import Nfib.D2SFib.ToFunctor

/-!
# The counit `Ψ ⋙ Φ ≅ 𝟭` and the paper's proof of the equivalence

Milestone **M9** of `PLAN.md`, following the paper's argument: the D2S Grothendieck construction of
`Ψ C` is isomorphic to `C`. Objects agree definitionally; a morphism of `D2SGC (Ψ C)` over
`g : B.Hom α b b'` is by definition a vertical morphism `push α c ⟶ pull (B.factor g) c'` of `C`
(after the two `eqToHom`s supplied by `gpush`/`gpull`), so the counit's action on morphisms is
`d2sHomEquiv`. Its functoriality (`map_comp'`) is the paper's pasted square: `comp'` in
`D2SGC (Ψ C)` is exactly the composite appearing in `d2sHomEquiv_comp` (`comp'_heq_vert`).

The counit is built directly, not extracted from a prior proof that `Ψ` is an equivalence: this
file depends only on `Grothendieck.lean` (`Φ`) and `ToFunctor.lean` (`Ψ`).
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A} [SplitOpfib B]

namespace Counit

variable (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]

/-- `Ψ C` sends the chosen horizontal morphisms of `∫(Bᵈᵒ)` to the pushforward functors. -/
theorem fmap_dualHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    D2SGC.fmap (toFunctorObj C) (dualHoriz α b) = pushFunctor α b :=
  toFunctorObj_map_dualHoriz C α b

/-- `Ψ C` sends the chosen vertical morphisms of `∫(Bᵈᵒ)` to the pullback functors. -/
theorem fmap_dualVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    D2SGC.fmap (toFunctorObj C) (dualVert β) = pullFunctor β :=
  toFunctorObj_map_dualVert C β

variable {C}

/-- The pushforward of `D2SGC (Ψ C)` is that of `C`. -/
theorem gpush {a a' : A} (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) :
    D2SGC.push (toFunctorObj C) α c = push α c :=
  CategoryTheory.Functor.congr_obj (fmap_dualHoriz C α b) c

/-- The pullback of `D2SGC (Ψ C)` is that of `C`. -/
theorem gpull {a : A} {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    D2SGC.pull (toFunctorObj C) β c = pull β c :=
  CategoryTheory.Functor.congr_obj (fmap_dualVert C β) c

/-- A morphism of `D2SGC (Ψ C)` over `g`, read as the vertical morphism of `C` that classifies a
morphism of `C` over `g`. -/
noncomputable def vert {a a' : A} {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : (D2SGC (toFunctorObj C)).Hom g c c') :
    fiberHom C (B.transp α b) (push α c) (pull (B.factor g) c') :=
  eqToHom (gpush α c).symm ≫ θ ≫ eqToHom (gpull (B.factor g) c')

theorem vert_heq {a a' : A} {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : (D2SGC (toFunctorObj C)).Hom g c c') : vert θ ≍ θ :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

variable {a a' a'' : A} {α : a ⟶ a'} {α' : a' ⟶ a''}
variable {b : B.Ob a} {b' : B.Ob a'} {b'' : B.Ob a''}

/-- `Ψ C` of the horizontal comparison morphism is the pushforward functor, on objects. -/
theorem fmap_horizComp_obj (x : C.Fiber (B.transp α b)) :
    (D2SGC.fmap (toFunctorObj C) (D2SGC.horizComp α α' b)).obj x ≍ push α' x := by
  rw [D2SGC.horizComp, D2SGC.fmap_comp, fmap_dualHoriz, fmap_dualVert]
  exact pull_eqToHom (B.transp_comp α α' b) (push α' x)

/-- `Ψ C` of the horizontal comparison morphism is the pushforward functor, on morphisms. -/
theorem fmap_horizComp_map {x y : C.Fiber (B.transp α b)} (f : x ⟶ y) :
    (D2SGC.fmap (toFunctorObj C) (D2SGC.horizComp α α' b)).map f ≍ pushMap α' f := by
  rw [D2SGC.horizComp, D2SGC.fmap_comp, fmap_dualHoriz, fmap_dualVert]
  exact pullMap_eqToHom (B.transp_comp α α' b) (pushMap α' f)

/-- `Ψ C` of the vertical comparison morphism is the pullback functor, on objects. -/
theorem fmap_vertComp_obj (β : (B.transp α b : B.Fiber a') ⟶ b') (y : C.Fiber (B.transp α' b')) :
    (D2SGC.fmap (toFunctorObj C) (D2SGC.vertComp α α' β)).obj y
      ≍ pull (B.transpMap α' β) y := by
  rw [D2SGC.vertComp, fmap_dualVert]
  refine HEq.trans ?_ (pull_eqToHom (B.transp_comp α α' b) (pull (B.transpMap α' β) y))
  exact heq_of_eq (pull_comp (eqToHom (B.transp_comp α α' b)) (B.transpMap α' β) y)

/-- `Ψ C` of the vertical comparison morphism is the pullback functor, on morphisms. -/
theorem fmap_vertComp_map (β : (B.transp α b : B.Fiber a') ⟶ b')
    {y z : C.Fiber (B.transp α' b')} (f : y ⟶ z) :
    (D2SGC.fmap (toFunctorObj C) (D2SGC.vertComp α α' β)).map f
      ≍ pullMap (B.transpMap α' β) f := by
  rw [D2SGC.vertComp, fmap_dualVert]
  refine (pullMap_comp_base (eqToHom (B.transp_comp α α' b)) (B.transpMap α' β) f).trans ?_
  exact pullMap_eqToHom (B.transp_comp α α' b) (pullMap (B.transpMap α' β) f)


/-- **The composition law of `D2SGC (Ψ C)`**, read in `C`: `comp'` is the composite that appears in
`d2sHomEquiv_comp`. This is the paper's pasted square for the counit. -/
theorem comp'_heq_vert {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : (D2SGC (toFunctorObj C)).Hom g c c')
    (θ' : (D2SGC (toFunctorObj C)).Hom g' c' c'') :
    D2SGC.comp' (toFunctorObj C) θ θ'
      ≍ (pushFunctor α' (B.transp α b)).map (vert θ)
        ≫ eqToHom (push_pull α' (B.factor g) c')
        ≫ (pullFunctor (B.transpMap α' (B.factor g))).map (vert θ') := by
  have hx : (D2SGC.fmap (toFunctorObj C) (dualHoriz α b ≫ D2SGC.horizComp α α' b)).obj c
      ≍ push α' (push α c) :=
    (heq_of_eq (D2SGC.fmap_obj_comp _ _ _ _)).trans
      ((fmap_horizComp_obj _).trans (heq_of_eq (congrArg (push α') (gpush α c))))
  have hy : (D2SGC.fmap (toFunctorObj C) (dualVert (B.factor g) ≫ D2SGC.horizComp α α' b)).obj c'
      ≍ push α' (pull (B.factor g) c') :=
    (heq_of_eq (D2SGC.fmap_obj_comp _ _ _ _)).trans
      ((fmap_horizComp_obj _).trans (heq_of_eq (congrArg (push α') (gpull (B.factor g) c'))))
  have hy' : (D2SGC.fmap (toFunctorObj C)
        (dualHoriz α' b' ≫ D2SGC.vertComp α α' (B.factor g))).obj c'
      ≍ pull (B.transpMap α' (B.factor g)) (push α' c') :=
    (heq_of_eq (D2SGC.fmap_obj_comp _ _ _ _)).trans
      ((fmap_vertComp_obj _ _).trans
        (heq_of_eq (congrArg (pull (B.transpMap α' (B.factor g))) (gpush α' c'))))
  have hz : (D2SGC.fmap (toFunctorObj C)
        (dualVert (B.factor g') ≫ D2SGC.vertComp α α' (B.factor g))).obj c''
      ≍ pull (B.transpMap α' (B.factor g)) (pull (B.factor g') c'') :=
    (heq_of_eq (D2SGC.fmap_obj_comp _ _ _ _)).trans
      ((fmap_vertComp_obj _ _).trans
        (heq_of_eq (congrArg (pull (B.transpMap α' (B.factor g))) (gpull (B.factor g') c''))))
  refine (D2SGC.comp'_heq (toFunctorObj C) θ θ').trans ?_
  rw [D2SGC.GHom.trans]
  refine fiber_comp_heq (B.transp_comp α α' b) hx hy hz ?_ ?_
  · refine (D2SGC.GHom.push_heq_map θ _).trans ((fmap_horizComp_map θ).trans ?_)
    exact pushMap_congr α' rfl (heq_of_eq (gpush α c)) (heq_of_eq (gpull (B.factor g) c'))
      (vert_heq θ).symm
  · refine fiber_comp_heq (B.transp_comp α α' b) hy hy' hz
      (fiber_eqToHom_heq' (B.transp_comp α α' b) hy hy' _ _) ?_
    refine (D2SGC.GHom.push_heq_map θ' _).trans ((fmap_vertComp_map _ θ').trans ?_)
    exact pullMap_congr rfl HEq.rfl (heq_of_eq (gpush α' c')) (heq_of_eq (gpull (B.factor g') c''))
      (vert_heq θ').symm


/-- **The counit on morphisms**: a morphism of `D2SGC (Ψ C)` over `g`, read through `d2sHomEquiv`
as a morphism of `C` over `g`. -/
noncomputable def map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (D2SGC (toFunctorObj C)).Hom g c c') : c ⟶[[g]] c' :=
  (d2sHomEquiv α g c c').symm (vert θ)

@[simp] theorem d2sHomEquiv_map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (D2SGC (toFunctorObj C)).Hom g c c') :
    d2sHomEquiv α g c c' (map θ) = vert θ :=
  Equiv.apply_symm_apply _ _

/-- `vert` is injective (it is an `eqToHom`-conjugation). -/
theorem vert_injective {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    {θ θ₂ : (D2SGC (toFunctorObj C)).Hom g c c'} (h : vert θ = vert θ₂) : θ = θ₂ :=
  eq_of_heq ((vert_heq θ).symm.trans ((heq_of_eq h).trans (vert_heq θ₂)))

/-- The counit is injective on morphisms. -/
theorem map_injective {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    {θ θ₂ : (D2SGC (toFunctorObj C)).Hom g c c'} (h : map θ = map θ₂) : θ = θ₂ := by
  refine vert_injective ?_
  have h2 := congrArg (d2sHomEquiv α g c c') h
  rwa [d2sHomEquiv_map, d2sHomEquiv_map] at h2

theorem map_id' (c : C.Ob b) : map (D2SGC.id' (toFunctorObj C) c) = C.id c := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [d2sHomEquiv_id]
  refine eq_of_heq ((vert_heq _).trans ?_)
  rw [D2SGC.id', D2SGC.GHom.ofEq]
  exact fiber_eqToHom_heq' rfl (heq_of_eq (gpush (𝟙 a) c))
    (heq_of_eq (gpull (B.factor (B.id b)) c)) _ _

theorem map_comp' {g : b ⟶[α] b'} {g' : b' ⟶[α'] b''} {c : C.Ob b} {c' : C.Ob b'}
    {c'' : C.Ob b''} (θ : (D2SGC (toFunctorObj C)).Hom g c c')
    (θ' : (D2SGC (toFunctorObj C)).Hom g' c' c'') :
    map (D2SGC.comp' (toFunctorObj C) θ θ') = map θ ≫ᵈᵈ map θ' := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine d2sHomEquiv_comp α α' g g' (map θ) (map θ') _ ?_
  rw [d2sHomEquiv_map, d2sHomEquiv_map]
  exact (vert_heq _).trans (comp'_heq_vert θ θ')

theorem map_pullLift' {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    map (D2SGC.pullLift (toFunctorObj C) β c) ≍ pullLift β c := by
  refine heq_of_d2sHomEquiv_heq (𝟙 a) β (gpull β c) rfl ?_
  rw [d2sHomEquiv_map, d2sHomEquiv_pullLift]
  refine (vert_heq _).trans ?_
  rw [D2SGC.pullLift, D2SGC.GHom.ofEq]
  exact fiber_eqToHom_heq' rfl
    ((heq_of_eq (gpush (𝟙 a) (D2SGC.pull (toFunctorObj C) β c))).trans
      (heq_of_eq (congrArg (push (C := C) (𝟙 a)) (gpull β c))))
    (heq_of_eq (gpull (B.factor β) c)) _ _

theorem map_pushLift' (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) :
    map (D2SGC.pushLift (toFunctorObj C) α c) ≍ pushLift α c := by
  refine heq_of_d2sHomEquiv_heq α (B.olift α b) rfl (gpush α c) ?_
  rw [d2sHomEquiv_map, d2sHomEquiv_pushLift]
  refine (vert_heq _).trans ?_
  rw [D2SGC.pushLift, D2SGC.GHom.ofEq]
  exact fiber_eqToHom_heq' rfl (heq_of_eq (gpush α c))
    ((heq_of_eq (gpull (B.factor (B.olift α b)) (D2SGC.push (toFunctorObj C) α c))).trans
      (heq_of_eq (congrArg (pull (C := C) (B.factor (B.olift α b))) (gpush α c)))) _ _


/-- **The counit on morphisms**, backward direction. -/
noncomputable def invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    (D2SGC (toFunctorObj C)).Hom g c c' :=
  eqToHom (gpush α c) ≫ d2sHomEquiv α g c c' θ ≫ eqToHom (gpull (B.factor g) c').symm

theorem invMap_heq {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    invMap θ ≍ d2sHomEquiv α g c c' θ :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

@[simp] theorem map_invMap {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') :
    map (invMap θ) = θ := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  exact eq_of_heq ((vert_heq _).trans (invMap_heq θ))

@[simp] theorem invMap_map {g : b ⟶[α] b'} {c : C.Ob b} {c' : C.Ob b'}
    (θ : (D2SGC (toFunctorObj C)).Hom g c c') : invMap (map θ) = θ :=
  map_injective (map_invMap (map θ))

/-- **The counit component**, forward direction: the identity on objects, `d2sHomEquiv⁻¹` on
morphisms. -/
noncomputable def homD2S : D2SFibHom (D2SGC (toFunctorObj C)) C where
  obj := fun {_} {_} c => c
  map := fun θ => map (C := C) θ
  map_id := fun c => map_id' (C := C) c
  map_comp := fun θ θ' => map_comp' (C := C) θ θ'
  obj_pull := fun β c => gpull (C := C) β c
  map_pullLift := fun β c => map_pullLift' (C := C) β c
  obj_push := by intro _ _ α _ c; exact gpush (C := C) α c
  map_pushLift := by intro _ _ α _ c; exact map_pushLift' (C := C) α c

theorem gpullLift_eq {b b' : B.Ob a} (β : b ⟶[𝟙 a] b') (c : C.Ob b') :
    (pullLift (C := D2SGC (toFunctorObj C)) β c)
      = eqToHom (D2SGC.pullLift_obj (toFunctorObj C) β c) := rfl

theorem gpushLift_eq (α : a ⟶ a') {b : B.Ob a} (c : C.Ob b) :
    (pushLift (C := D2SGC (toFunctorObj C)) α c)
      = eqToHom (D2SGC.pushLift_obj (toFunctorObj C) α c) := rfl

/-- **The counit component**, backward direction. -/
noncomputable def invD2S : D2SFibHom C (D2SGC (toFunctorObj C)) where
  obj := fun {_} {_} c => c
  map := fun θ => invMap (C := C) θ
  map_id := fun c => map_injective (C := C) (by
    rw [map_invMap]; exact (map_id' (C := C) c).symm)
  map_comp := fun θ θ' => map_injective (C := C) (by
    rw [map_invMap]
    exact ((map_comp' (C := C) (invMap θ) (invMap θ')).trans
      (by rw [map_invMap, map_invMap])).symm)
  obj_pull := fun β c => (gpull (C := C) β c).symm
  map_pullLift := by
    intro a b b' β c
    refine (invMap_heq _).trans ?_
    rw [d2sHomEquiv_pullLift, gpullLift_eq]
    exact fiber_eqToHom_heq' rfl
      (((heq_of_eq (gpush (𝟙 a) (D2SGC.pull (toFunctorObj C) β c))).trans
        (heq_of_eq (congrArg (push (C := C) (𝟙 a)) (gpull β c)))).symm)
      (heq_of_eq (gpull (B.factor β) c)).symm _ _
  obj_push := by intro _ _ α _ c; exact (gpush (C := C) α c).symm
  map_pushLift := by
    intro a a' α b c
    refine (invMap_heq _).trans ?_
    rw [d2sHomEquiv_pushLift, gpushLift_eq]
    exact fiber_eqToHom_heq' rfl (heq_of_eq (gpush α c)).symm
      (((heq_of_eq (gpull (B.factor (B.olift α b)) (D2SGC.push (toFunctorObj C) α c))).trans
        (heq_of_eq (congrArg (pull (C := C) (B.factor (B.olift α b))) (gpush α c)))).symm) _ _


end Counit

/-- **The counit component of the equivalence** (the paper's `F`/`G` pair): the D2S Grothendieck
construction of `Ψ E` is isomorphic to `E`, by the identity on objects and `d2sHomEquiv` on
morphisms. -/
noncomputable def counitApp (E : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) :
    D2SGCFib (toFunctorObj E.C) ≅ E where
  hom := Counit.homD2S (C := E.C)
  inv := Counit.invD2S (C := E.C)
  hom_inv_id := D2SFibHom.ext (DoubleDisplayed.VertFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.invMap_map θ)))
  inv_hom_id := D2SFibHom.ext (DoubleDisplayed.VertFunctor.ext (fun _ => rfl)
    (fun θ => heq_of_eq (Counit.map_invMap θ)))

namespace Counit

/-- The counit intertwines `Φ Ψ Φ_*` with `Φ`: the naturality computation, on morphisms. -/
theorem map_gmap {E E' : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B} (Φ : E ⟶ E') {a a' : A}
    {α : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[α] b'} {c : E.C.Ob b} {c' : E.C.Ob b'}
    (θ : (D2SGC (toFunctorObj E.C)).Hom g c c') :
    map (C := E'.C) (D2SGC.gmap (toFunctorMap Φ) θ) = Φ.map (map (C := E.C) θ) := by
  refine eq_of_heq (heq_of_d2sHomEquiv_heq α g rfl rfl ?_)
  rw [d2sHomEquiv_map]
  refine HEq.trans ?_ (D2SFibHom.d2sHomEquiv_map_heq Φ (map (C := E.C) θ)).symm
  rw [d2sHomEquiv_map]
  refine (vert_heq _).trans ?_
  refine (D2SGC.gmap_heq_map (toFunctorMap Φ) θ).trans ?_
  exact Φ.toVertFunctor.map_heq rfl rfl rfl HEq.rfl (heq_of_eq (gpush α c))
    (heq_of_eq (gpull (B.factor g) c')) (vert_heq θ).symm

end Counit

/-- **The counit** `Ψ ⋙ Φ ≅ 𝟭` of the equivalence. -/
noncomputable def counitIso :
    toFunctor ⋙ D2SGCFunctor ≅ 𝟭 (D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B) :=
  NatIso.ofComponents (fun E => counitApp E) (fun {E E'} Φ => by
    refine D2SFibHom.ext (DoubleDisplayed.VertFunctor.ext (fun _ => rfl) (fun θ => ?_))
    exact heq_of_eq (Counit.map_gmap Φ θ))

end Nfib
