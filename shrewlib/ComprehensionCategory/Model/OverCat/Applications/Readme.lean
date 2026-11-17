import ComprehensionCategory.Model.OverCat.Applications.NatHom
import ComprehensionCategory.Model.OverCat.Applications.DirectedUnivalence
import ComprehensionCategory.Model.OverCat.Applications.NatPi
import ComprehensionCategory.Model.OverCat.Applications.Yoneda

/-!
# Applications

The paper's Section `applications`, synthetic category theory in Twisted Type Theory, in the
models over `Cat`. The Yoneda corollary itself and Remark `lax-ends` are not formalized.

* `DirectedUnivalence`: Proposition `dunivalence`. For a contravariant type `A` and a discrete type
  `B`, the function type `A → B`, the Π-type of `B` weakened, is discrete (`funDisc`). For `A` and
  `B` of level `v`, it is isomorphic to the Hom-type `Hom_U(A, B)` of the universe at their codes
  (`homU`), by a strict natural isomorphism of functors `Γ ⥤ Cat` (`dunivIso`), not an equality:
  the values of `A → B` are the sections of the constant family `B γ` over `A γ`, those of
  `Hom_U(A, B)` the `ULift`ed functors. Both types and the isomorphism are stable under
  substitution, and the isomorphism gives a bijection of terms, natural in `Γ` (`dunivTmEquiv`),
  through a bijection of the terms of isomorphic discrete types (`tmEquivOfIso`).
* `NatHom`: Proposition `internal-nat-hom`. The twisted Hom-type `Hom_B(f̄, g)` of two terms
  (`twistedHomAt`), the twist of the Hom-type substituted along their pairing, is the straightening
  of a displayed category whose objects over `γ` are the morphisms `f γ ⟶ g γ` and whose morphisms
  are the naturality squares, so its terms are the vertical natural transformations between the
  sections of `f` and `g` (`natEquiv`), naturally in `Γ`; for functors `F G : A ⥤ B`, the natural
  transformations `F ⟶ G` (`natHomEquiv`). The twisted Hom-type of Hom-Intro is the instance at
  the variable, twice, by `rfl`.
* `NatPi`: Proposition `internal-nat-pi`. For `F : Γ ⥤ Cat` and `G` into discrete categories, of
  level `v`, the terms of `G` in context `Γ ▹ x : F` are the natural transformations `F ⟶ G`
  (`natPiEquiv`), by the paper's chain: application of the twisted function type `F̄ → G`
  (`Shared/FunTwist`), twisted directed univalence, a vertical isomorphism between the displayed
  categories of `F̄ → G` and of `Hom_U(F̄, G)` built fibrewise (`twistedDunivEquiv`), and
  `natEquiv` at the universe. The bijection sends `θ` to the transformation whose component at `γ`
  sends `x` to the value of `θ` at `(γ, x)`, and it is natural in `Γ`.
* `Yoneda`: the lemma before the Yoneda corollary. For a type `A` in the empty context and terms
  `F : A → U_s` and `a₀ : A` in context `Γ`, the bijection between the terms of `F b` in context
  `Γ ▹ b : A ▹ f : Homₐ(ā₀, b)` and those of `F a₀` in context `Γ`, substitution along the
  reflexivity, with inverse `k ↦ j(f, k)`, Hom-Elim with the premise `k` (`yonedaEquiv`), if empty
  types are unique. One round trip is Hom-Comp, and the other is, as in the paper, Hom-Elim into
  the Hom-type `Hom_{F b}(θ, j(f, θ*))` of the discrete model, with the premise `Refl_{θ*}`,
  followed by Hom-Disc.
-/

universe u v

open CategoryTheory Displayed ComprehensionCategory OverCat CatModel DiscreteModel
  Opfibration.Straightening Displayed.Discrete.Straightening

open scoped Displayed

/-! ## Directed univalence -/

section DirectedUnivalence

/-- The function type into a discrete type is discrete, a type of the discrete model whose functor
is the Π-type. -/
example {Γ : Cat.{u, u}} (A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ)
    (B : IDisc.{u, u}.Ty Γ) : (funDisc A B).toFunctor = Π[A] (funCodDisc A B) :=
  rfl

/-- **Directed univalence**: `A → B` and `Hom_U(A, B)` are isomorphic. -/
recall ComprehensionCategory.OverCat.dunivIso {Γ : Cat.{v + 1, v + 1}} (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v})
    (B : IDiscOb.{v, v} Γ) : (funU A B).toFunctor ≅ (homU A B).toFunctor

/-- Both types are stable under substitution, by `rfl` in the kernel, and so is the
isomorphism. -/
recall ComprehensionCategory.OverCat.funU_pull {Γ : Cat.{v + 1, v + 1}}
    (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}) (B : IDiscOb.{v, v} Γ) {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (funU A B)⦃σ⦄ = funU (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B)

recall ComprehensionCategory.OverCat.homU_pull {Γ : Cat.{v + 1, v + 1}}
    (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}) (B : IDiscOb.{v, v} Γ) {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (homU A B)⦃σ⦄ = homU (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B)

recall ComprehensionCategory.OverCat.dunivIso_pull {Γ : Cat.{v + 1, v + 1}}
    {A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}} {B : IDiscOb.{v, v} Γ} {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft σ.toFunctor (dunivIso A B) ≍
      dunivIso (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B)

/-- **Directed univalence for terms**, natural in `Γ`. -/
recall ComprehensionCategory.OverCat.dunivTmEquiv {Γ : Cat.{v + 1, v + 1}}
    (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}) (B : IDiscOb.{v, v} Γ) : Tm(Γ, funU A B) ≃ Tm(Γ, homU A B)

recall ComprehensionCategory.OverCat.dunivTmEquiv_pull {Γ : Cat.{v + 1, v + 1}}
    {A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}} {B : IDiscOb.{v, v} Γ} {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    (t : Tm(Γ, funU A B)) :
    (dunivTmEquiv A B t)⦃σ⦄.castTy (homU_pull A B σ) =
      dunivTmEquiv (σ.toFunctor.op ⋙ A) (SmallIDisc.pull σ B) (t⦃σ⦄.castTy (funU_pull A B σ))

end DirectedUnivalence

/-! ## Natural transformations as terms of twisted Hom-types -/

section NatHom

variable {Γ : Cat.{u, u}} {B : ICatLax.{u, u}.Ty Γ}

/-- The twisted Hom-type of two terms is the twist of the Hom-type, substituted along their
pairing. -/
recall ComprehensionCategory.OverCat.twistedHomAt_eq (f g : Tm(Γ, B)) :
    twistedHomAt f g =
      (twist (homFunctor B))⦃consSec g.sec (f.castTy (pull_sec_weak g).symm)⦄

/-- **The terms of `Hom_B(f̄, g)` are the natural transformations from `f` to `g`.** -/
recall ComprehensionCategory.OverCat.natEquiv (f g : Tm(Γ, B)) :
    Tm(Γ, twistedHomAt f g) ≃ (Tm.toSection f ⟶ Tm.toSection g)

/-- The bijection is natural in `Γ`. -/
recall ComprehensionCategory.OverCat.natEquiv_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    (f g : Tm(Γ, B)) (t : Tm(Γ, twistedHomAt f g)) :
    natEquiv f⦃σ⦄ g⦃σ⦄ (t⦃σ⦄.castTy (twistedHomAt_pull σ f g)) ≍
      Section.Hom.pull σ (natEquiv f g t)

/-- **The paper's statement**: for `F G : A ⥤ K`, the terms of `a : A ⊢ Hom_K(F̄a, Ga)` are the
natural transformations `F ⟶ G`. -/
recall ComprehensionCategory.OverCat.natHomEquiv {A K : Cat.{u, u}} (F G : A ⥤ K) :
    Tm(A, twistedHomAt (B := constTy A K) (Tm.ofConst F) (Tm.ofConst G)) ≃ (F ⟶ G)

/-- The twisted Hom-type of Hom-Intro is the twisted Hom-type of the variable with itself. -/
example (A : ICatLax.{u, u}.Ty Γ) : twistedHom A = twistedHomAt (var A) (var A) :=
  twistedHom_eq_twistedHomAt A

end NatHom

/-! ## Natural transformations as terms of a discrete type -/

section NatPi

variable {Γ : Cat.{v + 1, v + 1}} {F : Γ ⥤ Cat.{v, v}} {G : IDiscOb.{v, v} Γ}

/-- **Twisted directed univalence**: the terms of `F̄ → G` are those of `Hom_U(F̄, G)`. -/
recall ComprehensionCategory.OverCat.twistedDunivEquiv (F : Γ ⥤ Cat.{v, v})
    (G : IDiscOb.{v, v} Γ) : Tm(Γ, funTwist F G.toFunctor) ≃ Tm(Γ, twistedHomU F G)

/-- **The terms of `G` in context `Γ ▹ x : F` are the natural transformations `F ⟶ G`.** -/
recall ComprehensionCategory.OverCat.natPiEquiv (F : Γ ⥤ Cat.{v, v}) (G : IDiscOb.{v, v} Γ) :
    Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄) ≃
      (F ⟶ G.toFunctor)

/-- The component at `γ` sends `x` to the value of `θ` at `(γ, x)`. -/
recall ComprehensionCategory.OverCat.natPiEquiv_app_obj
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) (γ : Γ)
    (x : F.obj γ) :
    ((natPiEquiv F G θ).app γ).toFunctor.obj x = ULift.down ((CatModel.Tm.toSection θ).obj
      ((∫ (CatModel.lift F)).tot (a := γ) (ULift.up.{v + 1} x)))

/-- The bijection is natural in `Γ`. -/
recall ComprehensionCategory.OverCat.natPiEquiv_pull {Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    (θ : Tm(Γ ▹ CatModel.lift F, (CatModel.lift G.toFunctor)⦃𝐩 (CatModel.lift F)⦄)) :
    natPiEquiv (σ.toFunctor ⋙ F) (SmallIDisc.pull σ G) θ⦃𝐪(σ, CatModel.lift F)⦄ =
      Functor.whiskerLeft σ.toFunctor (natPiEquiv F G θ)

end NatPi

/-! ## The Yoneda lemma -/

section Yoneda

variable {Γ : Cat.{v + 1, v + 1}} {A : Cat.{v + 1, v + 1}} {F : Tm(Γ, copresheafTy Γ A)}
  {a₀ : Tm(Γ, CatModel.constTy Γ A)}

/-- `A → U_s`, for a category `A`, a type in the empty context: the Π-type of the universe of
discrete types over the constant type at `A`. -/
example : copresheafTy Γ A = piTy (CatOpModel.constTy Γ A) (UDisc (Γ ▹ CatOpModel.constTy Γ A)) :=
  rfl

/-- `F a₀` is the substitution of `F b` along the section of `a₀`. -/
example : appAt F a₀ = (app F)⦃a₀.sec⦄ :=
  rfl

/-- `j(refl_a₀, k) ≡ k`, by Hom-Comp. -/
recall ComprehensionCategory.OverCat.yonedaFun_yonedaInv (k : Tm(Γ, appAt F a₀)) :
    yonedaFun (yonedaInv k) = k

/-- `j(f, θ*) ≡ θ`, by Hom-Elim into `Hom_{F b}(θ, j(f, θ*))` with the premise `Refl_{θ*}`, and
Hom-Disc. -/
recall ComprehensionCategory.OverCat.yonedaInv_yonedaFun (hE : EmptyUnique.{v + 1})
    (θ : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄)) : yonedaInv (yonedaFun θ) = θ

/-- **The lemma before the Yoneda corollary**: for `A` a type in the empty context, `F : A → U_s`
and `a₀ : A`, the terms of `F b` over the context of Hom-Elim are those of `F a₀`, if empty types
are unique. -/
recall ComprehensionCategory.OverCat.yonedaEquiv (F : Tm(Γ, copresheafTy Γ A))
    (a₀ : Tm(Γ, CatModel.constTy Γ A)) (hE : EmptyUnique.{v + 1}) :
    Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄) ≃ Tm(Γ, appAt F a₀)

/-- The bijection is the substitution along the reflexivity. -/
example (hE : EmptyUnique.{v + 1}) (θ : Tm(homElimCtx a₀, (app F)⦃homElimCod a₀⦄)) :
    yonedaEquiv F a₀ hE θ = θ⦃homElimR a₀⦄ :=
  rfl

end Yoneda
