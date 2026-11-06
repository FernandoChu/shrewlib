import DoubleDisplayed.Basic

/-!
# (Op)cartesian morphisms in a doubly displayed category

The analogue one level up of the (op)cartesian morphisms of `Displayed/Opfibration/Basic.lean` and
`Displayed/Fibration/Basic.lean`: the double-level `IsOpcartesian` (over any `B`-morphism) and
`IsCartesian` (over vertical `B`-morphisms) structures, whose factorizations are data, and their
universal-property API.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

namespace DoubleDisplayed

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₂, u₂} A}
  (C : DoubleDisplayed.{v₃, u₃} B)

section Opcartesian

variable {C}

/-- `θ : c ⟶[[g]] c'` is *opcartesian* at the double level: every doubly displayed map out of `c`
over `g ≫ᵈ g'` factors uniquely through `θ` over `g'`. The factorization is data. -/
structure IsOpcartesian {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') where
  /-- The factorization of `χ` through `θ`. -/
  desc : ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} (g' : b' ⟶[f'] b'') {c'' : C.Ob b''},
    (c ⟶[[g ≫ᵈ g']] c'') → (c' ⟶[[g']] c'')
  desc_fac : ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} (g' : b' ⟶[f'] b'') {c'' : C.Ob b''}
    (χ : c ⟶[[g ≫ᵈ g']] c''), θ ≫ᵈᵈ desc g' χ = χ
  /-- Any factorization of `χ` through `θ` agrees with `desc`. -/
  desc_uniq : ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} {g' : b' ⟶[f'] b''} {c'' : C.Ob b''}
    {χ : c ⟶[[g ≫ᵈ g']] c''} (ψ : c' ⟶[[g']] c''), θ ≫ᵈᵈ ψ = χ → ψ = desc g' χ

namespace IsOpcartesian

variable {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
  {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'}

instance : Subsingleton (IsOpcartesian θ) where
  allEq H H' := by
    obtain ⟨d, fac, _⟩ := H
    obtain ⟨d', _, uniq'⟩ := H'
    obtain rfl : @d = @d' := by
      funext a'' f' b'' g' c'' χ
      exact uniq' _ (fac g' χ)
    rfl

/-- Two maps out of `c'` that agree after precomposition with an opcartesian `θ` are equal. -/
theorem hom_ext (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    {g' : b' ⟶[f'] b''} {c'' : C.Ob b''} {ψ ψ' : c' ⟶[[g']] c''}
    (h : θ ≫ᵈᵈ ψ = θ ≫ᵈᵈ ψ') : ψ = ψ' :=
  (H.desc_uniq ψ rfl).trans (H.desc_uniq ψ' h.symm).symm

end IsOpcartesian

/-- `θ : s ⟶[[g]] t` is *cartesian* at the double level, among vertical morphisms (over `𝟙 a`):
every doubly displayed map into `t` over `g₀ ≫ᵈ g` factors uniquely through `θ` over `g₀`. The
factorization is data. -/
structure IsCartesian {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'} {s : C.Ob b} {t : C.Ob b'}
    (θ : s ⟶[[g]] t) where
  /-- The factorization of `χ` through `θ`. -/
  lift : ∀ {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀},
    (s₀ ⟶[[g₀ ≫ᵈ g]] t) → (s₀ ⟶[[g₀]] s)
  lift_fac : ∀ {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀} (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t),
    lift g₀ χ ≫ᵈᵈ θ = χ
  /-- Any factorization of `χ` through `θ` agrees with `lift`. -/
  lift_uniq : ∀ {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀} {χ : s₀ ⟶[[g₀ ≫ᵈ g]] t}
    (ξ : s₀ ⟶[[g₀]] s), ξ ≫ᵈᵈ θ = χ → ξ = lift g₀ χ

namespace IsCartesian

variable {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'} {s : C.Ob b} {t : C.Ob b'}
  {θ : s ⟶[[g]] t}

instance : Subsingleton (IsCartesian θ) where
  allEq H H' := by
    obtain ⟨l, fac, _⟩ := H
    obtain ⟨l', _, uniq'⟩ := H'
    obtain rfl : @l = @l' := by
      funext b₀ g₀ s₀ χ
      exact uniq' _ (fac g₀ χ)
    rfl

/-- Two maps into `s` that agree after postcomposition with a cartesian `θ` are equal. -/
theorem hom_ext (H : IsCartesian θ) {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀}
    {ξ ξ' : s₀ ⟶[[g₀]] s} (h : ξ ≫ᵈᵈ θ = ξ' ≫ᵈᵈ θ) : ξ = ξ' :=
  (H.lift_uniq ξ rfl).trans (H.lift_uniq ξ' h.symm).symm

end IsCartesian

end Opcartesian

end DoubleDisplayed
