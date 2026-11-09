import Displayed.Fibration.Straightening.Unstraighten
import Displayed.Displayed.Section
import Tactic.KernelTactic

/-!
# The dependent product along the unstraightening of a contravariant functor

For `A : Γᵒᵖ ⥤ Cat` and a displayed category `E` over the total category of `∫⁻ A`, the *dependent
product* `piDisp A E` is displayed over `Γ`:

* an object over `γ` is a section of `E` over the fibre `A γ`, that is, a section of the reindexing
  `fibreDisp A E γ` of `E` along the inclusion `fibreIncl A γ : A γ ⥤ (∫⁻ A).Total`: objects
  `s x` of `E` over `(γ, x)`, and morphisms `s φ : s x ⟶[(𝟙, φ)] s x'`;
* a morphism over `g : γ ⟶ γ'` from `s` to `t` (`PiHom`) is a morphism `s (A g x') ⟶ t x'` of `E`
  over the chosen lift `(g, 𝟙) : (γ, A g x') ⟶ (γ', x')` (`(∫⁻ A).totalClift g x'`), natural in
  `x'`.

This is where `A` must be contravariant: a section over `A γ` is related to one over `A γ'` along
`A g : A γ' ⥤ A γ`. The laws of `piDisp A E` hold by `rfl`, through the rules of `E` and the rule
`totalClift_comp`, which splits the chosen lift of a composite.

**The sections of `piDisp A E` are those of `E`** (`piSectionEquiv`). A section `S` of `E`
restricts to the fibres (`piSection`). Conversely, a section `T` of `piDisp A E` gives the section
of `E` whose morphism over `(f, φ) = (𝟙, φ) ≫ (f, 𝟙)` is the transport `(T γ).map φ` in the fibre
followed by the component `(T.map f).app` (`ofPiSection`). This is abstraction and application for
the Π-types of the category model over the contravariant one (`OverCat/Shared/Pi`).

All the morphisms are of `E`, over morphisms of the total category of `∫⁻ A`, never composites of
the transports of a functor: the base morphisms are compared before `E` is unfolded, so that
`(𝟙, A g φ') ≫ (g, 𝟙)` and `(g, 𝟙) ≫ (𝟙, φ')`, both `(g, A g φ')`, are identified. Some of these
comparisons are checked in the kernel.
-/

universe u

namespace Displayed.Fibration.Straightening

open CategoryTheory Opposite Displayed

open scoped Displayed

variable {Γ : Cat.{u, u}} (A : Γᵒᵖ ⥤ Cat.{u, u}) (E : Displayed.{u, u} (∫⁻ A).Total)

/-- The inclusion of the fibre `A γ` into the total category of `∫⁻ A`. -/
def fibreIncl (γ : Γ) : A.obj (op γ) ⟶ Cat.of (∫⁻ A).Total :=
  Functor.toCatHom
    { obj x := (∫⁻ A).tot x
      map φ := (∫⁻ A).totalMk (𝟙 γ) φ
      map_id _ := rfl
      map_comp _ _ := rfl }

/-- The restriction of `E` to the fibre `A γ`. -/
abbrev fibreDisp (γ : Γ) : Displayed.{u, u} (A.obj (op γ)) :=
  DisplayedCat.pull (fibreIncl A γ) E

variable {A E}

/-- A morphism over `g : γ ⟶ γ'` from a section `s` over `A γ` to a section `t` over `A γ'`: a
morphism of `E` from `s (A g x')` to `t x'` over the chosen lift `(g, 𝟙)`, natural in `x'`. -/
structure PiHom {γ γ' : Γ} (g : γ ⟶ γ') (s : (fibreDisp A E γ).Section)
    (t : (fibreDisp A E γ').Section) where
  /-- The component at `x'`. -/
  app : ∀ x' : A.obj (op γ'), s.obj ((A.map g.op).toFunctor.obj x') ⟶[(∫⁻ A).totalClift g x']
    t.obj x'
  naturality : ∀ {x' y' : A.obj (op γ')} (φ' : x' ⟶ y'),
    E.comp (s.map ((A.map g.op).toFunctor.map φ')) (app y') = E.comp (app x') (t.map φ')

theorem PiHom.ext {γ γ' : Γ} {g : γ ⟶ γ'} {s : (fibreDisp A E γ).Section}
    {t : (fibreDisp A E γ').Section} {h k : PiHom g s t} (happ : ∀ x', h.app x' = k.app x') :
    h = k := by
  obtain ⟨app, _⟩ := h
  obtain ⟨app', _⟩ := k
  obtain rfl : app = app' := funext happ
  rfl

theorem PiHom.hext {γ γ' : Γ} {g : γ ⟶ γ'} {s s' : (fibreDisp A E γ).Section}
    {t t' : (fibreDisp A E γ').Section} (hs : s = s') (ht : t = t') {h : PiHom g s t}
    {k : PiHom g s' t'} (happ : ∀ x', h.app x' ≍ k.app x') : h ≍ k := by
  subst hs ht
  exact heq_of_eq (PiHom.ext fun x' => eq_of_heq (happ x'))

variable (A E)

/-- **The dependent product of `E` along `∫⁻ A`**, displayed over `Γ`: the objects over `γ` are the
sections of `E` over the fibre `A γ`, and the morphisms over `g` are the natural families
`PiHom`. Its laws hold by `rfl`. -/
def piDisp : Displayed.{u, u} Γ where
  Ob γ := (fibreDisp A E γ).Section
  Hom g s t := PiHom g s t
  id s := ⟨fun x => E.id (s.obj x), fun _ => rfl⟩
  comp {_ _ _ g g' s t r} h k :=
    ⟨fun x'' => E.comp (h.app ((A.map g'.op).toFunctor.obj x'')) (k.app x''), fun {_ _} φ =>
      (congrArg (E.comp · (k.app _)) (h.naturality ((A.map g'.op).toFunctor.map φ))).trans
        (congrArg (E.comp (h.app _) ·) (k.naturality φ))⟩

variable {A E}

/-! ## Sections -/

/-- The section of `piDisp A E` of a section of `E`: its restrictions to the fibres. -/
def piSection (S : E.Section) : (piDisp A E).Section where
  obj γ :=
    { obj x := S.obj ((∫⁻ A).tot x)
      map φ := S.map ((∫⁻ A).totalMk (𝟙 γ) φ)
      map_id x := S.map_id _
      map_comp φ ψ := by
        kernel_exact S.map_comp ((∫⁻ A).totalMk (𝟙 γ) φ) ((∫⁻ A).totalMk (𝟙 γ) ψ) }
  map {γ γ'} g := ⟨fun x' => S.map ((∫⁻ A).totalClift g x'), fun {x' y'} φ' => by
    kernel_exact (S.map_comp ((∫⁻ A).totalMk (𝟙 γ) ((A.map g.op).toFunctor.map φ'))
      ((∫⁻ A).totalClift g y')).symm.trans
      (S.map_comp ((∫⁻ A).totalClift g x') ((∫⁻ A).totalMk (𝟙 γ') φ'))⟩
  map_id γ := PiHom.ext fun x => S.map_id _
  map_comp {_ _ _} g g' := PiHom.ext fun x => by
    kernel_exact S.map_comp ((∫⁻ A).totalClift g ((A.map g'.op).toFunctor.obj x))
      ((∫⁻ A).totalClift g' x)

/-- The section of `E` of a section of `piDisp A E`: over `(f, φ)`, the transport in the fibre along
`φ`, followed by the component of the transport along `f`. -/
def ofPiSection (T : (piDisp A E).Section) : E.Section where
  obj p := (T.obj p.1).obj p.2
  map {p _} F := E.comp ((T.obj p.1).map F.fiber) ((T.map F.base).app _)
  map_id p := congrArg₂ E.comp ((T.obj p.1).map_id p.2)
    (congrArg (fun h => PiHom.app h p.2) (T.map_id p.1))
  map_comp {p _ r} F G :=
    (congrArg₂ E.comp ((T.obj p.1).map_comp _ _)
      (congrArg (fun h => PiHom.app h r.2) (T.map_comp F.base G.base))).trans
    (congrArg (E.comp ((T.obj p.1).map F.fiber) ·)
      (congrArg (E.comp · ((T.map G.base).app r.2)) ((T.map F.base).naturality G.fiber)))

theorem ofPiSection_piSection (S : E.Section) : ofPiSection (piSection S) = S :=
  Section.ext (fun _ => rfl) fun F => by
    kernel_exact heq_of_eq
      (S.map_comp ((∫⁻ A).totalMk (𝟙 _) F.fiber) ((∫⁻ A).totalClift F.base _)).symm

theorem piSection_ofPiSection (T : (piDisp A E).Section) : piSection (ofPiSection T) = T := by
  have hobj : ∀ γ, (piSection (ofPiSection T)).obj γ = T.obj γ := fun γ =>
    Section.ext (fun x => (rfl : (T.obj γ).obj x = _)) fun {_ x'} φ => by
      kernel_exact heq_of_eq
        (congrArg (E.comp ((T.obj γ).map φ) ·) (congrArg (fun h => PiHom.app h x') (T.map_id γ)))
  exact Section.ext hobj fun {γ γ'} g => PiHom.hext (hobj γ) (hobj γ') fun x' => by
    kernel_exact heq_of_eq (congrArg (E.comp · ((T.map g).app x')) ((T.obj γ).map_id _))

/-- **The sections of the dependent product are those of `E`.** -/
def piSectionEquiv : (piDisp A E).Section ≃ E.Section where
  toFun := ofPiSection
  invFun := piSection
  left_inv := piSection_ofPiSection
  right_inv := ofPiSection_piSection

end Displayed.Fibration.Straightening
