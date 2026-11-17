import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Shared.OpDisc

/-!
# Twists along discrete variables

The twist along a variable of a discrete type does nothing:

```
    Γ ⊢ B type_s        Γ ▹ˢ b : Bᵒᵖ ⊢ C type
  ------------------------------------------- Twist-Disc
        Γ ▹ˢ b : B ⊢ Tw_b(C) ≡ C type_d
```

On the right, `C` is read in context `Γ ▹ˢ b : B`, which is `Γ ▹ˢ b : Bᵒᵖ` by op-Disc. This is
judgmental, by the rules of `Shared/OpDisc`, from the axiom of uniqueness of empty types: the
contexts `Γ ▹ B` and `Γ ▹ Bᵒᵖ` are the same, as are their morphisms. So Twist-Disc is the equation
`twist C = catToDisp C` (`twist_disc`), between types in this context.

Over `(f, β) : (γ, b) ⟶ (γ', b')`, with `β : B f b ⟶ b'`, the morphisms `c ⟶ c'` of the twist are
the morphisms `C(f, 𝟙) c ⟶ C(𝟙, β) c'` of `C (γ', B f b)`, and those of `∫ C` the morphisms
`C(f, β) c ⟶ c'` of `C (γ', b')`. These types are equal, but not definitionally, since `b'` is
only propositionally `B f b`: substituting `B f b` for `b'` and then `𝟙` for `β`, which the
discreteness of `B γ'` allows, makes both sides `C(f, 𝟙) c ⟶ c'`, by `rfl`. Identities and
composites agree up to the casts along these equalities in the same way, so the casts form a
vertical functor, and the two displayed categories are equal (`twistDisp_disc`, by
`VertFunctor.eq_of_map_cast`).

Substituting first is also what keeps the proofs within the rules: the twist sees `β` as the
morphism `b' ⟶ B f b` of `Bᵒᵖ` from `B f b` to `b'`, whose type the rules make that of a morphism
of `B` from `B f b` to `b'`, while `β` goes the other way (`Shared/OpDisc`). For `β = 𝟙`, the two
agree.

The paper's proof of the Yoneda lemma needs this rule: its premise `Refl_{θ*} : Hom_{Fa₀}(θ*, θ*)`
is Hom-Intro for the discrete type `Fa₀`, a term of the twisted Hom-type `Hom_{Fa₀}(θ̄*, θ*)`,
which Twist-Disc identifies with the Hom-type. `Applications/Yoneda` builds it so (`yonedaRefl`).
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening
  Displayed.Discrete.Straightening CatModel DiscreteModel

open scoped Displayed

variable {Γ : Cat.{u, u}} (B : IDisc.{u, u}.Ty Γ) (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ))

/-- **The displayed category of the twist of `C` is `∫ C`**: a vertical functor between them is the
identity on objects and a cast on morphisms, along the equality of their morphisms over `(f, β)`,
which holds by `rfl` once `b'` is `B f b` and `β` is `𝟙`. -/
theorem twistDisp_disc : twistDisp (B := B.toFunctor) C = ∫ C := by
  have hHom : ∀ {a a' : (Γ ▹ B : Cat.{u, u})} (F : a ⟶ a') x y,
      (twistDisp (B := B.toFunctor) C).Hom F x y = (∫ C).Hom F x y := by
    rintro ⟨γ, b⟩ ⟨γ', b'⟩ ⟨f, β⟩ x y
    dsimp only at f β
    obtain rfl := (B.isDiscrete γ').eq_of_hom β
    obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ').subsingleton _ _) β (𝟙 _)
    rfl
  exact (VertFunctor.eq_of_map_cast (D := twistDisp (B := B.toFunctor) C) (E := ∫ C)
    { obj x := x
      map {_ _ F x y} φ := cast (hHom F x y) φ
      map_id := by
        rintro ⟨γ, b⟩ x
        rfl
      map_comp := by
        rintro ⟨γ, b⟩ ⟨γ', b'⟩ ⟨γ'', b''⟩ ⟨f, β⟩ ⟨g, β'⟩ x y z φ ψ
        dsimp only at f g β β'
        obtain rfl := (B.isDiscrete γ').eq_of_hom β
        obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ').subsingleton _ _) β (𝟙 _)
        obtain rfl := (B.isDiscrete γ'').eq_of_hom β'
        obtain rfl := @Subsingleton.elim _ ((B.isDiscrete γ'').subsingleton _ _) β' (𝟙 _)
        rfl }
    rfl (fun _ => rfl) hHom fun _ => rfl).1

/-- **Twist-Disc**: the twist of a type `C` in context `Γ ▹ˢ b : Bᵒᵖ`, for a discrete type `B`, is
`C`, seen in the displayed model, in the context `Γ ▹ˢ b : B`, which is `Γ ▹ˢ b : Bᵒᵖ` by
op-Disc. -/
theorem twist_disc : twist (B := B.toFunctor) C = catToDisp C :=
  congrArg Straightening.straightenObj (twistDisp_disc B C)

end ComprehensionCategory.OverCat
