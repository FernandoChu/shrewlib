import ComprehensionCategory.Model.OverCat.Applications.NatHom
import ComprehensionCategory.Model.OverCat.Applications.DirectedUnivalence
import ComprehensionCategory.Model.OverCat.Applications.NatPi
import ComprehensionCategory.Model.OverCat.Applications.Transport

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
* `Transport`: the lemma before the Yoneda corollary. Transport `j(f, r, r)` by Hom-Elim, and,
  for a discrete type `P` in context `Γ ▹ a : A`, the bijection between the terms of `P b` in
  context `Γ ▹ b : A ▹ a : A ▹ f : Hom_A(ā, b)` and those of `P a` in context `Γ ▹ a : A`,
  substitution along the reflexivity, with inverse the substitution of `r := k` in transport
  (`yonedaEquiv`), if empty types are unique. One round trip is Hom-Comp, and the other is, as in
  the paper, Hom-Elim into the Hom-type of the discrete model followed by Hom-Disc: two terms of a
  discrete type over the context of Hom-Elim that agree along the reflexivity are equal
  (`eq_of_pull_reflSec`). The bijection is natural in `Γ`, and so is transport.
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

/-! ## Transport and the Yoneda lemma -/

section Transport

variable {Γ : Cat.{u, u}} {A : ICatLax.{u, u}.Ty Γ}

/-- **Transport**, `j(f, r, r) : P b`, and `j(refl_a, r, r) ≡ r`. -/
recall ComprehensionCategory.OverCat.transport (P : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    Tm(elimCtx A P, transportMotive P)

recall ComprehensionCategory.OverCat.transport_refl (P : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    (transport P)⦃homR A P⦄ = var P

/-- Two terms of a discrete type over the context of Hom-Elim that agree along the reflexivity are
equal, by Hom-Elim and Hom-Disc. -/
recall ComprehensionCategory.OverCat.eq_of_pull_reflSec (hE : EmptyUnique.{u})
    {B : IDisc.{u, u}.Ty (homCtx A)} (a b : Tm(homCtx A, B)) (h : b⦃reflSec A⦄ = a⦃reflSec A⦄) :
    a = b

/-- **The lemma before the Yoneda corollary**: the terms of `P b` over the context of Hom-Elim are
those of `P a`, for a discrete type `P`, if empty types are unique. -/
recall ComprehensionCategory.OverCat.yonedaEquiv (hE : EmptyUnique.{u})
    {Pd : IDisc.{u, u}.Ty (Γ ▹ A)} :
    Tm(homCtx A, (forgetComprehensionMap.toPre.obj Pd)⦃homCod A⦄) ≃
      Tm(Γ ▹ A, forgetComprehensionMap.toPre.obj Pd)

/-- The bijection is substitution along the reflexivity, with inverse the substitution of `r := k`
in transport. -/
example (hE : EmptyUnique.{u}) {Pd : IDisc.{u, u}.Ty (Γ ▹ A)}
    (θ : Tm(homCtx A, (forgetComprehensionMap.toPre.obj Pd)⦃homCod A⦄)) :
    yonedaEquiv hE θ = θ⦃reflSec A⦄ :=
  rfl

/-- The bijection is natural in `Γ`. -/
example {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {P : ICatLax.{u, u}.Ty (Γ ▹ A)}
    (θ : Tm(homCtx A, P⦃homCod A⦄)) :
    yonedaFun (A := A⦃σ⦄) (P := P⦃𝐪(σ, A)⦄) θ⦃homCtxMap σ A⦄ = (yonedaFun θ)⦃𝐪(σ, A)⦄ :=
  yonedaFun_pull σ θ

end Transport
