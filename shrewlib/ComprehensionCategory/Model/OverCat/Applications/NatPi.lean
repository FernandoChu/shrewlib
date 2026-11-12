import ComprehensionCategory.Model.OverCat.Applications.NatHom
import ComprehensionCategory.Model.OverCat.Applications.DirectedUnivalence
import ComprehensionCategory.Model.OverCat.Shared.FunTwist

/-!
# Natural transformations as terms of a dependent type

The paper's Proposition `internal-nat-pi`: for `F : Γ ⥤ Cat` and a copresheaf `G : Γ ⥤ Cat` into
discrete categories, of level `v`, the terms

```
  Γ ▹ x : F ⊢ θ : G
```

are the natural transformations `F ⟶ G` (`natPiEquiv`). The paper takes `Γ` to be a type `A` in
the empty context and `F` discrete too; here `Γ` is any context of level `v + 1`, which plays the
role of `a : A`, and `F` need not be discrete. As in the paper, the bijection is the chain

```
  Tm(Γ ▹ x : F, G) ≅ Tm_d(Γ, F̄ → G)            (funTwistEquiv, Shared/FunTwist)
                   ≅ Tm_d(Γ, Hom_U(F̄, G))       (twistedDunivEquiv, twisted directed univalence)
                   ≅ (code F ⟶ code G)          (natEquiv, Applications/NatHom)
                   ≅ (F ⟶ G)                    (codeNatEquiv)
```

## Twisted directed univalence

`F̄ → G` is the straightening of the displayed category `funDisp F G` (`Shared/FunTwist`), and
`Hom_U(F̄, G)` (`twistedHomU`), the twisted Hom-type of the universe `U Γ` at the codes of `F` and
`G`, that of `twistedHomUDisp F G` (`Applications/NatHom`). The two displayed categories over `Γ`
are isomorphic, by two vertical functors inverse to each other (`toTwistedHomU`,
`ofTwistedHomU`):

* over `γ`, the objects of `funDisp F G` are the sections of the constant family `G γ` over `F γ`,
  that is the functors `F γ ⥤ G γ` (`funFibToFun`, `funToFunFib`), and those of
  `twistedHomUDisp F G` are the `ULift`ed functors;
* over `k : γ ⟶ γ'`, a morphism of `funDisp F G` from `s` to `t` is a vertical natural
  transformation from `x ↦ G k (s x)` to `x ↦ t (F k x)`, and a morphism of `twistedHomUDisp F G` a
  proof of `s ⋙ G k = F k ⋙ t`. Since `G γ'` is discrete, there is at most one of each, and one
  exactly when the square commutes (`funFibToFun_sq`, and the `eqToHom`s of `ofTwistedHomUApp`).

So their sections, the terms of the two types, correspond (`twistedDunivSectionEquiv`,
`twistedDunivEquiv`). This is the twisted form of directed univalence
(`Applications/DirectedUnivalence`), built directly on the displayed categories, fibrewise, rather
than by twisting the untwisted isomorphism: the function type `Y → X` of `Shared/FunTwist` lives
over the universe `U` of all types, over which it is not discrete, so `dunivIso` does not apply to
it before substituting the codes.

## The natural transformations

The last step is that the vertical natural transformations between the sections of the codes
`code F` and `code G`, terms of the universe `U Γ`, are the natural transformations `F ⟶ G`,
through `AsSmall` (`codeNatEquiv`). The composite sends `θ` to the natural transformation whose
component at `γ` sends `x` to the value of `θ` at `(γ, x)` (`natPiEquiv_app_obj`), and it is
natural in `Γ` (`natPiEquiv_pull`).

As in `Shared/FunTwist`, the type `F̄ → G` is only propositionally the straightening of
`funDisp F G` (`funTwist_eq`), and checking the transport along this equality in the kernel
unfolds the twist. So the composite is computed by rewriting with `Equiv.trans_apply` and with
`funLam_heq` (`twistedDunivEquiv_funLam`, `natPiEquiv_eq`), never by `rfl`.
-/

universe v

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{v + 1, v + 1}} {F : Γ ⥤ Cat.{v, v}} {G : IDiscOb.{v, v} Γ}

/-! ## Twisted directed univalence -/

variable (F G) in
/-- The objects of `F̄ → G` over `γ`: the sections of the constant family `G γ` over `F γ`. -/
abbrev FunFib (γ : Γ) :=
  PiFib (funDom Γ) ((funCod Γ)⦃𝐩 (funDom Γ)⦄) (funPt F G.toFunctor γ)

variable (F G) in
/-- **`Hom_U(F̄, G)`**: the twisted Hom-type of the universe at the codes of `F` and `G`, a type of
the displayed model. -/
abbrev twistedHomU : Straightening.IProf.{v + 1, v + 1, v + 1}.Ty Γ :=
  twistedHomAt (B := U Γ) (code F) (code G.toFunctor)

variable (F G) in
/-- The displayed category of `Hom_U(F̄, G)`. Its objects over `γ` are the `ULift`ed functors
`F γ ⥤ G γ`, and its morphisms over `k` from `e` to `e'` the proofs of `e ⋙ G k = F k ⋙ e'`. -/
abbrev twistedHomUDisp : Displayed.{v + 1, v + 1} Γ :=
  twistedHomAtDisp (B := U Γ) (Tm.toSection (code F)) (Tm.toSection (code G.toFunctor))

/-- The functor `F γ ⥤ G γ` of a section of the constant family `G γ` over `F γ`. -/
def funFibToFun {γ : Γ} (s : FunFib F G γ) : F.obj γ ⥤ G.toFunctor.obj γ where
  obj x := ULift.down (s.obj (ULift.up.{v + 1} x))
  map f := ULift.down (s.map (ULift.up.{v + 1} f))
  map_id x := congrArg ULift.down (s.map_id (ULift.up.{v + 1} x))
  map_comp f g := congrArg ULift.down (s.map_comp (ULift.up.{v + 1} f) (ULift.up.{v + 1} g))

/-- The section of the constant family `G γ` over `F γ` of a functor `F γ ⥤ G γ`. -/
def funToFunFib {γ : Γ} (H : F.obj γ ⥤ G.toFunctor.obj γ) : FunFib F G γ where
  obj x := ULift.up.{v + 1} (H.obj (ULift.down x))
  map f := ULift.up.{v + 1} (H.map (ULift.down f))

/-- A section is the section of its functor. -/
theorem funToFunFib_funFibToFun {γ : Γ} (s : FunFib F G γ) : funToFunFib (funFibToFun s) = s :=
  Section.ext (fun _ => rfl) fun _ => HEq.rfl

/-- A functor is the functor of its section, by `rfl`. -/
theorem funFibToFun_funToFunFib {γ : Γ} (H : F.obj γ ⥤ G.toFunctor.obj γ) :
    funFibToFun (F := F) (G := G) (funToFunFib H) = H :=
  rfl

/-- The morphisms of `F̄ → G` are unique: their components are in the discrete categories `G γ'`. -/
theorem funDisp_hom_ext {γ γ' : Γ} {k : γ ⟶ γ'} {s : FunFib F G γ} {t : FunFib F G γ'}
    (h h' : (funDisp F G.toFunctor).Hom k s t) : h = h' :=
  funHom_ext k fun _ => @Subsingleton.elim _ (((liftDisc G).isDiscrete γ').subsingleton _ _) _ _

/-- **A morphism of `F̄ → G` over `k` from `s` to `t` makes the square `s ⋙ G k = F k ⋙ t`
commute**: its components are morphisms of the discrete category `G γ'`. -/
theorem funFibToFun_sq {γ γ' : Γ} {k : γ ⟶ γ'} {s : FunFib F G γ} {t : FunFib F G γ'}
    (h : (funDisp F G.toFunctor).Hom k s t) :
    (funFibToFun s).toCatHom ≫ G.toFunctor.map k = F.map k ≫ (funFibToFun t).toCatHom := by
  have hobj : ∀ x, (G.toFunctor.map k).toFunctor.obj ((funFibToFun s).obj x) =
      (funFibToFun t).obj ((F.map k).toFunctor.obj x) := fun x =>
    congrArg ULift.down (((liftDisc G).isDiscrete γ').eq_of_hom (funAppOf k h (ULift.up x)))
  exact Cat.Hom.ext (Functor.hext hobj fun x y _ =>
    @hom_heq_of_isDiscrete _ _ (G.isDiscrete γ') _ _ _ _ (hobj x) (hobj y) _ _)

/-- The morphism of `Hom_U(F̄, G)` of a morphism of `F̄ → G`: its square. It is stated for a
variable `k`, so that the kernel checks its type once. -/
def toTwistedHomUMap {γ γ' : Γ} {k : γ ⟶ γ'} {s : FunFib F G γ} {t : FunFib F G γ'}
    (h : (funDisp F G.toFunctor).Hom k s t) :
    (twistedHomUDisp F G).Hom k (ULift.up.{v + 1} (funFibToFun s).toCatHom)
      (ULift.up.{v + 1} (funFibToFun t).toCatHom) :=
  ⟨⟨congrArg ULift.up.{v + 1} (funFibToFun_sq h)⟩⟩

variable (F G) in
/-- **The vertical functor from `F̄ → G` to `Hom_U(F̄, G)`**: a section of the constant family goes
to its functor, and a morphism to its square. -/
def toTwistedHomU : VertFunctor (funDisp F G.toFunctor) (twistedHomUDisp F G) where
  obj s := ULift.up.{v + 1} (funFibToFun s).toCatHom
  map h := toTwistedHomUMap h
  map_id _ := twistedHomAtDisp_hom_ext _ _
  map_comp _ _ := twistedHomAtDisp_hom_ext _ _

/-- The square `e ⋙ G k = F k ⋙ e'` of a morphism of `Hom_U(F̄, G)`, on objects. -/
theorem twistedHomU_obj_eq {γ γ' : Γ} {k : γ ⟶ γ'} {e : (twistedHomUDisp F G).Ob γ}
    {e' : (twistedHomUDisp F G).Ob γ'} (p : (twistedHomUDisp F G).Hom k e e') (x : F.obj γ) :
    (G.toFunctor.map k).toFunctor.obj ((ULift.down e).toFunctor.obj x) =
      (ULift.down e').toFunctor.obj ((F.map k).toFunctor.obj x) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (congrArg ULift.down p.down.down)) x

/-- The component at `x` of the morphism of `F̄ → G` of a morphism of `Hom_U(F̄, G)`: the `eqToHom`
of its square at `x`, a morphism of `∫ G⦃𝐩 F⦄` over the chosen lift `(k, 𝟙)`. -/
def ofTwistedHomUApp {γ γ' : Γ} {k : γ ⟶ γ'} {e : (twistedHomUDisp F G).Ob γ}
    {e' : (twistedHomUDisp F G).Ob γ'} (p : (twistedHomUDisp F G).Hom k e e')
    (x : (CatModel.lift F).obj γ) :
    (funE F G.toFunctor).Hom ((∫ (CatModel.lift F)).totalOlift k x)
      ((funToFunFib (F := F) (G := G) (ULift.down e).toFunctor).obj x)
      ((funToFunFib (F := F) (G := G) (ULift.down e').toFunctor).obj
        (((CatModel.lift F).map k).toFunctor.obj x)) :=
  ULift.up.{v + 1} (eqToHom (twistedHomU_obj_eq p (ULift.down x)))

/-- The morphism of `F̄ → G` of a morphism of `Hom_U(F̄, G)`, natural since `G γ'` is discrete. -/
def ofTwistedHomUMap {γ γ' : Γ} {k : γ ⟶ γ'} {e : (twistedHomUDisp F G).Ob γ}
    {e' : (twistedHomUDisp F G).Ob γ'} (p : (twistedHomUDisp F G).Hom k e e') :
    (funDisp F G.toFunctor).Hom k (funToFunFib (ULift.down e).toFunctor)
      (funToFunFib (ULift.down e').toFunctor) :=
  ⟨fun x => ofTwistedHomUApp p x, fun _ =>
    @Subsingleton.elim _ (((liftDisc G).isDiscrete γ').subsingleton _ _) _ _⟩

variable (F G) in
/-- **The vertical functor from `Hom_U(F̄, G)` to `F̄ → G`**: a functor goes to its section, and a
square to the natural transformation of its `eqToHom`s. -/
def ofTwistedHomU : VertFunctor (twistedHomUDisp F G) (funDisp F G.toFunctor) where
  obj e := funToFunFib (ULift.down e).toFunctor
  map p := ofTwistedHomUMap p
  map_id _ := funDisp_hom_ext _ _
  map_comp _ _ := funDisp_hom_ext _ _

/-- `ofTwistedHomU` is a left inverse of `toTwistedHomU`. -/
theorem toTwistedHomU_ofTwistedHomU :
    toTwistedHomU F G ⋙ᵥ ofTwistedHomU F G = VertFunctor.id (funDisp F G.toFunctor) :=
  DispFunctor.ext funToFunFib_funFibToFun fun {_ γ'} {k} {s t} _ =>
    funHom_hext k (funToFunFib_funFibToFun s) (funToFunFib_funFibToFun t) fun x =>
      @hom_heq_of_isDiscrete _ _ ((liftDisc G).isDiscrete γ') _ _ _ _
        (congrArg (fun s : FunFib F G _ =>
          ((CatModel.lift G.toFunctor).map k).toFunctor.obj (s.obj x))
          (funToFunFib_funFibToFun s))
        (congrArg (fun t : FunFib F G γ' => t.obj (((CatModel.lift F).map k).toFunctor.obj x))
          (funToFunFib_funFibToFun t)) _ _

/-- `ofTwistedHomU` is a right inverse of `toTwistedHomU`. -/
theorem ofTwistedHomU_toTwistedHomU :
    ofTwistedHomU F G ⋙ᵥ toTwistedHomU F G = VertFunctor.id (twistedHomUDisp F G) :=
  DispFunctor.ext (fun _ => rfl) fun _ => heq_of_eq (twistedHomAtDisp_hom_ext _ _)

variable (F G) in
/-- The sections of `F̄ → G` and of `Hom_U(F̄, G)` correspond along the vertical isomorphism. -/
def twistedDunivSectionEquiv :
    (funDisp F G.toFunctor).Section ≃ (twistedHomUDisp F G).Section where
  toFun := (toTwistedHomU F G).mapSection
  invFun := (ofTwistedHomU F G).mapSection
  left_inv S := (VertFunctor.mapSection_comp _ _ S).trans
    ((congrArg (VertFunctor.mapSection · S) toTwistedHomU_ofTwistedHomU).trans
      (VertFunctor.mapSection_id S))
  right_inv S := (VertFunctor.mapSection_comp _ _ S).trans
    ((congrArg (VertFunctor.mapSection · S) ofTwistedHomU_toTwistedHomU).trans
      (VertFunctor.mapSection_id S))

variable (F G) in
/-- **Twisted directed univalence**: the terms of `F̄ → G` are those of `Hom_U(F̄, G)`. -/
def twistedDunivEquiv : Tm(Γ, funTwist F G.toFunctor) ≃ Tm(Γ, twistedHomU F G) :=
  (Equiv.cast (congrArg (fun X => Tm(Γ, X)) (funTwist_eq F G.toFunctor))).trans
    (DisplayedModel.Tm.sectionEquiv.trans ((twistedDunivSectionEquiv F G).trans
      DisplayedModel.Tm.sectionEquiv.symm))

/-! ## The natural transformations -/

variable (F G) in
/-- The vertical natural transformations between the sections of the codes of `F` and `G` are the
natural transformations `F ⟶ G`: their components are the `ULift`ed functors. -/
def codeNatEquiv :
    (Tm.toSection (code F) ⟶ Tm.toSection (code G.toFunctor)) ≃ (F ⟶ G.toFunctor) where
  toFun α :=
    { app γ := ULift.down (α.app γ)
      naturality _ _ k := congrArg ULift.down (α.naturality k) }
  invFun θ :=
    { app γ := ULift.up.{v + 1} (θ.app γ)
      naturality k := congrArg ULift.up.{v + 1} (θ.naturality k) }
  left_inv _ := rfl
  right_inv _ := rfl

variable (F G) in
/-- **The paper's Proposition `internal-nat-pi`**: the terms of `G` in context `Γ ▹ x : F` are the
natural transformations `F ⟶ G`, through `F̄ → G`, `Hom_U(F̄, G)` and the natural transformations
between the codes. -/
def natPiEquiv :
    Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄) ≃
      (F ⟶ G.toFunctor) :=
  (funTwistEquiv F G.toFunctor).symm.trans ((twistedDunivEquiv F G).trans
    ((natEquiv (code F) (code G.toFunctor)).trans (codeNatEquiv F G)))

/-- Twisted directed univalence sends the abstraction of `θ` to the term of the image of its
section. -/
theorem twistedDunivEquiv_funLam
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) :
    twistedDunivEquiv F G ((funTwistEquiv F G.toFunctor).symm θ) = DisplayedModel.Tm.ofSection
      ((toTwistedHomU F G).mapSection (funSection (CatModel.Tm.toSection θ))) := by
  have h : (Equiv.cast (congrArg (fun X => Tm(Γ, X)) (funTwist_eq F G.toFunctor)))
      ((funTwistEquiv F G.toFunctor).symm θ) =
        DisplayedModel.Tm.ofSection (funSection (CatModel.Tm.toSection θ)) := by
    kernel_exact eq_of_heq ((cast_heq (congrArg (fun X => Tm(Γ, X)) (funTwist_eq F G.toFunctor))
      ((funTwistEquiv F G.toFunctor).symm θ)).trans (funLam_heq θ))
  rw [twistedDunivEquiv, Equiv.trans_apply, h, Equiv.trans_apply]
  exact congrArg (fun T => DisplayedModel.Tm.sectionEquiv.symm ((twistedDunivSectionEquiv F G) T))
    (DisplayedModel.Tm.toSection_ofSection _)

/-- The bijection `natPiEquiv`, computed up to the last steps. -/
theorem natPiEquiv_eq
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) :
    natPiEquiv F G θ = codeNatEquiv F G (natEquiv (code F) (code G.toFunctor)
      (DisplayedModel.Tm.ofSection
        ((toTwistedHomU F G).mapSection (funSection (CatModel.Tm.toSection θ))))) := by
  rw [natPiEquiv, Equiv.trans_apply, Equiv.trans_apply, twistedDunivEquiv_funLam]
  exact Equiv.trans_apply _ _ _

/-- The component at `γ` of the natural transformation of `θ` is the functor of the restriction of
the section of `θ` to the fibre `F γ`. -/
theorem natPiEquiv_app
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) (γ : Γ) :
    (natPiEquiv F G θ).app γ =
      ULift.down ((toTwistedHomU F G).obj ((funSection (CatModel.Tm.toSection θ)).obj γ)) := by
  rw [natPiEquiv_eq]
  exact congrArg (fun X => (codeNatEquiv F G (natSectionEquiv X)).app γ)
    (DisplayedModel.Tm.toSection_ofSection _)

/-- **The bijection is the expected one**: the component at `γ` of the natural transformation of
`θ` sends `x` to the value of `θ` at `(γ, x)`. -/
theorem natPiEquiv_app_obj
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) (γ : Γ)
    (x : F.obj γ) :
    ((natPiEquiv F G θ).app γ).toFunctor.obj x = ULift.down ((CatModel.Tm.toSection θ).obj
      ((∫ (CatModel.lift F)).tot (a := γ) (ULift.up.{v + 1} x))) := by
  rw [natPiEquiv_app]
  rfl

/-- **The bijection is natural in `Γ`**: the natural transformation of `θ⦃𝐪(σ, F)⦄` is the
restriction along `σ` of that of `θ`. -/
theorem natPiEquiv_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) :
    natPiEquiv (σ.toFunctor ⋙ F) (SmallIDisc.pull σ G) θ⦃𝐪(σ, CatModel.lift F)⦄ =
      Functor.whiskerLeft σ.toFunctor (natPiEquiv F G θ) := by
  refine NatTrans.ext (funext fun δ => ?_)
  have hobj : ∀ x, ((natPiEquiv (σ.toFunctor ⋙ F) (SmallIDisc.pull σ G)
      θ⦃𝐪(σ, CatModel.lift F)⦄).app δ).toFunctor.obj x =
        ((natPiEquiv F G θ).app (σ.toFunctor.obj δ)).toFunctor.obj x := fun x => by
    refine (natPiEquiv_app_obj _ δ x).trans (Eq.trans ?_ (natPiEquiv_app_obj θ _ x).symm)
    exact congrArg ULift.down (eq_of_heq (CatModel.Tm.toSection_pull_obj 𝐪(σ, CatModel.lift F) θ
      ((∫ (CatModel.lift (σ.toFunctor ⋙ F))).tot (a := δ) (ULift.up.{v + 1} x))))
  exact Cat.Hom.ext (Functor.hext hobj fun x y _ =>
    @hom_heq_of_isDiscrete _ _ (G.isDiscrete (σ.toFunctor.obj δ)) _ _ _ _ (hobj x) (hobj y) _ _)

end ComprehensionCategory.OverCat
