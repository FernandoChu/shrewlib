import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Maps.DiscreteToCat
import CategoryTheory.Opposite.Discrete

/-!
# Twists along discrete variables

The twist along a variable of a discrete type does nothing:

```
    Γ ⊢ B type_s        Γ ▹ˢ b : Bᵒᵖ ⊢ C type
  ------------------------------------------- Twist-Disc
        Γ ▹ˢ b : B ⊢ Tw_b(C) ≡ C type_d
```

On the right, `C` is read in context `Γ ▹ˢ b : B` through op-Disc, `Bᵒᵖ ≡ B`. In the model this
needs uniqueness of empty types (`op_eq_self`), and the contexts `Γ ▹ B` and `Γ ▹ Bᵒᵖ` are then only
propositionally equal. So the rule is the heterogeneous equality `twist C ≍ catToDisp C`
(`twist_disc`), between types in these two contexts, much as Hom-Disc transports a term of a
discrete type `A` to `Aᵒᵖ` (`Tm.toOp`, in `HomDisc`).

It comes from an equality with no hypothesis (`twist_discSwap`): the twist of `C` is `C`
substituted along `discSwap B : Γ ▹ B ⟶ Γ ▹ Bᵒᵖ`, the identity on objects, which sends a morphism
`(f, β)`, with `β : B f b ⟶ b'` in the discrete category `B γ'`, to `(f, β⁻¹)`, with
`β⁻¹ : b' ⟶ B f b` the `eqToHom` of the equality that `β` gives. If empty types are unique,
`discSwap B` is the identity (`discSwap_heq_id`): the types `b' ⟶ B f b` and `B f b ⟶ b'` are then
equal, and `β⁻¹` and `β` are equal elements of this subsingleton.

Over `(f, β)`, the morphisms `c ⟶ c'` of the twist are the morphisms `C(f, 𝟙) c ⟶ C(𝟙, β) c'` of
`C (γ', B f b)`, and those of `∫ C⦃discSwap B⦄` the morphisms `C(f, β⁻¹) c ⟶ c'` of `C (γ', b')`.
These types are equal (`twistDisp_hom_eq_disc`), but not definitionally, since `b'` is only
propositionally `B f b`: substituting `B f b` for `b'` and then `𝟙` for `β`, which the
discreteness of `B γ'` allows, makes both sides `C(f, 𝟙) c ⟶ c'`, by `rfl`. Identities and
composites agree up to the casts along these equalities in the same way, so the casts form a
vertical functor (`twistDispDiscFunctor`), and the two displayed categories are equal
(`twistDisp_disc`, by `VertFunctor.eq_of_map_cast`).

The paper's proof of the Yoneda lemma needs this rule: its premise `Refl_{θ*} : Hom_{Fa₀}(θ*, θ*)`
is Hom-Intro for the discrete type `Fa₀`, a term of the twisted Hom-type `Hom_{Fa₀}(θ̄*, θ*)`,
which Twist-Disc identifies with the Hom-type. `Applications/Yoneda` uses instead the reflexivity
`homDiscRefl` of the Hom-types of discrete types (`HomDisc`), defined directly in the model.

None of these equations is a rewrite rule.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}} (B : IDisc.{u, u}.Ty Γ)

/-! ## The swap of `Γ ▹ B` and `Γ ▹ Bᵒᵖ` -/

/-- The swap of the total categories of `∫ B` and `∫ Bᵒᵖ`, for a discrete type `B`: the identity on
objects, which sends `(f, β)`, with `β : B f b ⟶ b'`, to `(f, β⁻¹)`, with `β⁻¹ : b' ⟶ B f b` the
`eqToHom` of the equality that `β` gives. Its laws hold since the morphisms of the fibres are
unique. -/
def discSwapFunctor : (∫ B.toFunctor).Total ⥤ (∫ (B.toFunctor ⋙ opFunctor')).Total where
  obj x := x
  map {x y} g := ⟨g.base,
    (eqToHom ((B.isDiscrete y.1).eq_of_hom g.fiber).symm :
      @Quiver.Hom (B.toFunctor.obj y.1) _ y.2 ((B.toFunctor.map g.base).toFunctor.obj x.2))⟩
  map_id x := Total.Hom.ext' rfl
    (heq_of_eq (@Subsingleton.elim _ ((B.isDiscrete x.1).subsingleton _ _) _ _))
  map_comp {_ _ z} _ _ := Total.Hom.ext' rfl
    (heq_of_eq (@Subsingleton.elim _ ((B.isDiscrete z.1).subsingleton _ _) _ _))

/-- **The swap `Γ ▹ˢ b : B ⟶ Γ ▹ˢ b : Bᵒᵖ`** of the context extensions by a discrete type and by
its opposite, through which a type in context `Γ ▹ˢ b : Bᵒᵖ` is read in context `Γ ▹ˢ b : B`. -/
def discSwap : (Γ ▹ B : Cat.{u, u}) ⟶ Γ ▹ Bᵒᵖ :=
  (discSwapFunctor B).toCatHom

/-! ## The twist along a discrete variable is the substitution along the swap -/

variable (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ))

/-- The morphisms of the twist of `C` over `(f, β)` are those of `∫ C⦃discSwap B⦄`, for explicit
components of the base morphism. They are both those of `C (γ', B f b)` from `C(f, 𝟙) c` to `c'`
once `b'` is `B f b` and `β` is `𝟙`. -/
theorem twistDisp_hom_eq_disc_mk {γ γ' : Γ} {b : B.toFunctor.obj γ} {b' : B.toFunctor.obj γ'}
    (f : γ ⟶ γ') (β : (∫ B.toFunctor).Hom f b b')
    (x : (twistDisp (B := B.toFunctor) C).Ob ((∫ B.toFunctor).tot b))
    (y : (twistDisp (B := B.toFunctor) C).Ob ((∫ B.toFunctor).tot b')) :
    (twistDisp (B := B.toFunctor) C).Hom ((∫ B.toFunctor).totalMk f β) x y =
      (∫ (C⦃discSwap B⦄)).Hom ((∫ B.toFunctor).totalMk f β) x y := by
  obtain rfl := (B.isDiscrete γ').eq_of_hom β
  obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ').subsingleton _ _) β (𝟙 _)
  rfl

/-- **The twist of `C` and `∫ C⦃discSwap B⦄` have the same morphisms.** -/
theorem twistDisp_hom_eq_disc {a a' : (Γ ▹ B : Cat.{u, u})} (F : a ⟶ a')
    (x : (twistDisp (B := B.toFunctor) C).Ob a) (y : (twistDisp (B := B.toFunctor) C).Ob a') :
    (twistDisp (B := B.toFunctor) C).Hom F x y = (∫ (C⦃discSwap B⦄)).Hom F x y := by
  obtain ⟨γ, b⟩ := a
  obtain ⟨γ', b'⟩ := a'
  obtain ⟨f, β⟩ := F
  exact twistDisp_hom_eq_disc_mk B C f β x y

/-- The casts along `twistDisp_hom_eq_disc` preserve composites, for explicit components of the
base morphisms: once the second components of the objects are substituted, the casts are along
`rfl`, and the two composites are `C(g, 𝟙) φ ≫ ψ`. -/
theorem twistDisp_disc_map_comp_mk {γ γ' γ'' : Γ} {b : B.toFunctor.obj γ}
    {b' : B.toFunctor.obj γ'} {b'' : B.toFunctor.obj γ''} (f : γ ⟶ γ') (g : γ' ⟶ γ'')
    (β : (∫ B.toFunctor).Hom f b b') (β' : (∫ B.toFunctor).Hom g b' b'')
    {x : (twistDisp (B := B.toFunctor) C).Ob ((∫ B.toFunctor).tot b)}
    {y : (twistDisp (B := B.toFunctor) C).Ob ((∫ B.toFunctor).tot b')}
    {z : (twistDisp (B := B.toFunctor) C).Ob ((∫ B.toFunctor).tot b'')}
    (φ : (twistDisp (B := B.toFunctor) C).Hom ((∫ B.toFunctor).totalMk f β) x y)
    (ψ : (twistDisp (B := B.toFunctor) C).Hom ((∫ B.toFunctor).totalMk g β') y z) :
    cast (twistDisp_hom_eq_disc B C _ x z) (φ ≫ᵈ ψ) =
      cast (twistDisp_hom_eq_disc B C _ x y) φ ≫ᵈ cast (twistDisp_hom_eq_disc B C _ y z) ψ := by
  obtain rfl := (B.isDiscrete γ').eq_of_hom β
  obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ').subsingleton _ _) β (𝟙 _)
  obtain rfl := (B.isDiscrete γ'').eq_of_hom β'
  obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ'').subsingleton _ _) β' (𝟙 _)
  rfl

/-- The casts along `twistDisp_hom_eq_disc`, a vertical functor from the twist of `C` to
`∫ C⦃discSwap B⦄`. -/
def twistDispDiscFunctor :
    VertFunctor (twistDisp (B := B.toFunctor) C) (∫ (C⦃discSwap B⦄)) where
  obj x := x
  map {_ _ F x y} φ := cast (twistDisp_hom_eq_disc B C F x y) φ
  map_id {a} x := by
    obtain ⟨γ, b⟩ := a
    rfl
  map_comp {a a' a''} F G x y z φ ψ := by
    obtain ⟨γ, b⟩ := a
    obtain ⟨γ', b'⟩ := a'
    obtain ⟨γ'', b''⟩ := a''
    obtain ⟨f, β⟩ := F
    obtain ⟨g, β'⟩ := G
    exact twistDisp_disc_map_comp_mk B C f g β β' φ ψ

/-- **The displayed category of the twist of `C` is `∫ C⦃discSwap B⦄`**, since a vertical functor
between them is the identity on objects and a cast on morphisms. -/
theorem twistDisp_disc : twistDisp (B := B.toFunctor) C = ∫ (C⦃discSwap B⦄) :=
  (VertFunctor.eq_of_map_cast (twistDispDiscFunctor B C) rfl (fun _ => rfl)
    (twistDisp_hom_eq_disc B C) (fun _ => rfl)).1

/-- **Twist-Disc, along the swap**: the twist of a type `C` in context `Γ ▹ˢ b : Bᵒᵖ`, for a
discrete type `B`, is `C` read in context `Γ ▹ˢ b : B` through `discSwap B`, seen in the displayed
model. -/
theorem twist_discSwap : twist (B := B.toFunctor) C = catToDisp (C⦃discSwap B⦄) :=
  congrArg Straightening.straightenObj (twistDisp_disc B C)

/-! ## Twist-Disc

If empty types are unique, `Bᵒᵖ = B` (op-Disc), and the swap is the identity. -/

/-- Morphisms `y ⟶ x` and `x ⟶ y` of a discrete category are equal, as elements of types that are
equal once `y` is `x`. -/
theorem hom_heq_symm_of_isDiscrete {D : Cat.{u, u}} [IsDiscrete D] {x y : D} (f : y ⟶ x)
    (g : x ⟶ y) : f ≍ g := by
  obtain rfl := IsDiscrete.eq_of_hom g
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Functors into the total categories of equal displayed categories are equal if they agree on
objects and morphisms, compared heterogeneously. -/
theorem toCatHom_heq_of_displayed_eq {A : Type u} [Category.{u} A] {D D' : Displayed.{u, u} A}
    (hD : D = D') {E : Type u} [Category.{u} E] (F : E ⥤ D.Total) (G : E ⥤ D'.Total)
    (hobj : ∀ x, F.obj x ≍ G.obj x) (hmap : ∀ {x y : E} (f : x ⟶ y), F.map f ≍ G.map f) :
    F.toCatHom ≍ G.toCatHom := by
  subst hD
  exact heq_of_eq (congrArg Functor.toCatHom
    (Functor.hext (fun x => eq_of_heq (hobj x)) fun _ _ f => hmap f))

/-- Morphisms of the total categories of equal displayed categories are equal if their components
are, compared heterogeneously. -/
theorem totalHom_heq_of_displayed_eq {A : Type u} [Category.{u} A] {D D' : Displayed.{u, u} A}
    (hD : D = D') {x y : D.Total} {x' y' : D'.Total} (hx : x ≍ x') (hy : y ≍ y') (F : x ⟶ y)
    (G : x' ⟶ y') (hb : F.base ≍ G.base) (hf : F.fiber ≍ G.fiber) : F ≍ G := by
  subst hD
  exact Total.Hom.hext (eq_of_heq hx) (eq_of_heq hy) hb hf

/-- Substituting along a morphism that is the identity up to an equality of contexts gives the same
type, in the displayed model. -/
theorem catToDisp_pull_heq {X Y : Cat.{u, u}} (h : Y = X) (σ : Y ⟶ X) (hσ : σ ≍ 𝟙 Y)
    (C : ICatLax.{u, u}.Ty X) : catToDisp (C⦃σ⦄) ≍ catToDisp C := by
  subst h
  obtain rfl := eq_of_heq hσ
  rfl

variable (hE : EmptyUnique.{u})

include hE in
/-- If empty types are unique, the context extensions by a discrete type and by its opposite are
equal, by op-Disc. -/
theorem ext_op_disc : (Γ ▹ B : Cat.{u, u}) = Γ ▹ Bᵒᵖ :=
  congrArg (fun A : IDisc.{u, u}.Ty Γ => (Γ ▹ A : Cat.{u, u})) (op_eq_self hE B).symm

include hE in
/-- If empty types are unique, the unstraightenings of a discrete type and of its opposite are
equal, by op-Disc. -/
theorem unstraighten_op_disc : ∫ (B.toFunctor ⋙ opFunctor') = ∫ B.toFunctor :=
  congrArg (fun A : IDisc.{u, u}.Ty Γ => ∫ A.toFunctor) (op_eq_self hE B)

include hE in
/-- **If empty types are unique, the swap is the identity**: `β⁻¹ : b' ⟶ B f b` and
`β : B f b ⟶ b'` are then equal. -/
theorem discSwap_heq_id : discSwap B ≍ 𝟙 (Γ ▹ B : Cat.{u, u}) :=
  toCatHom_heq_of_displayed_eq (unstraighten_op_disc B hE) (discSwapFunctor B) (𝟭 _)
    (fun _ => HEq.rfl) fun {_ y} g =>
      totalHom_heq_of_displayed_eq (unstraighten_op_disc B hE) HEq.rfl HEq.rfl _ _ HEq.rfl
        (@hom_heq_symm_of_isDiscrete _ (B.isDiscrete y.1) _ _ _ g.fiber)

include hE in
/-- **Twist-Disc**: if empty types are unique, the twist of a type `C` in context
`Γ ▹ˢ b : Bᵒᵖ`, for a discrete type `B`, is `C`, seen in the displayed model, in context
`Γ ▹ˢ b : B`, which op-Disc makes `Γ ▹ˢ b : Bᵒᵖ`. -/
theorem twist_disc : twist (B := B.toFunctor) C ≍ catToDisp C :=
  (heq_of_eq (twist_discSwap B C)).trans
    (catToDisp_pull_heq (ext_op_disc B hE) (discSwap B) (discSwap_heq_id B hE) C)

end ComprehensionCategory.OverCat
