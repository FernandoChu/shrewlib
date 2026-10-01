import DoubleDisplayed.Basic

/-!
# (Op)cartesian morphisms in a doubly displayed category

The analogue of `Displayed/Cartesian.lean` one level up: the double-level `IsOpcartesian` (over
any `B`-morphism) and `IsCartesian` (over vertical `B`-morphisms) predicates and their
universal-property API.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

namespace DoubleDisplayed

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}
  (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)

section Opcartesian

variable {C}

/-- `θ : c ⟶[[g]] c'` is *opcartesian* at the double level: every doubly displayed map out of `c`
over `g ≫ᵈ g'` factors uniquely through `θ` over `g'`. -/
def IsOpcartesian {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
    {c : C.Ob b} {c' : C.Ob b'} (θ : c ⟶[[g]] c') : Prop :=
  ∀ {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''} (g' : b' ⟶[f'] b'')
    (c'' : C.Ob b'') (χ : c ⟶[[g ≫ᵈ g']] c''),
    ∃! ψ : c' ⟶[[g']] c'', θ ≫ᵈᵈ ψ = χ

namespace IsOpcartesian

variable {a a' : A} {f : a ⟶ a'} {b : B.Ob a} {b' : B.Ob a'} {g : b ⟶[f] b'}
  {c : C.Ob b} {c' : C.Ob b'} {θ : c ⟶[[g]] c'}

/-- The unique factorization of `χ` through an opcartesian `θ`. -/
noncomputable def desc (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    (g' : b' ⟶[f'] b'') {c'' : C.Ob b''} (χ : c ⟶[[g ≫ᵈ g']] c'') : c' ⟶[[g']] c'' :=
  (H g' c'' χ).choose

theorem desc_fac (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    (g' : b' ⟶[f'] b'') {c'' : C.Ob b''} (χ : c ⟶[[g ≫ᵈ g']] c'') :
    θ ≫ᵈᵈ desc H g' χ = χ :=
  (H g' c'' χ).choose_spec.1

/-- Any factorization of `χ` through `θ` agrees with `desc`. -/
theorem desc_uniq (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    {g' : b' ⟶[f'] b''} {c'' : C.Ob b''} {χ : c ⟶[[g ≫ᵈ g']] c''}
    (ψ : c' ⟶[[g']] c'') (hψ : θ ≫ᵈᵈ ψ = χ) : ψ = desc H g' χ :=
  (H g' c'' χ).choose_spec.2 ψ hψ

/-- Two maps out of `c'` that agree after precomposition with an opcartesian `θ` are equal. -/
theorem hom_ext (H : IsOpcartesian θ) {a'' : A} {f' : a' ⟶ a''} {b'' : B.Ob a''}
    {g' : b' ⟶[f'] b''} {c'' : C.Ob b''} {ψ ψ' : c' ⟶[[g']] c''}
    (h : θ ≫ᵈᵈ ψ = θ ≫ᵈᵈ ψ') : ψ = ψ' :=
  (desc_uniq H ψ rfl).trans (desc_uniq H ψ' h.symm).symm

end IsOpcartesian

/-- `θ : s ⟶[[g]] t` is *cartesian* at the double level, among vertical morphisms (over `𝟙 a`):
every doubly displayed map into `t` over `g₀ ≫ᵈ g` factors uniquely through `θ` over `g₀`. -/
def IsCartesian {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'} {s : C.Ob b} {t : C.Ob b'}
    (θ : s ⟶[[g]] t) : Prop :=
  ∀ {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) (s₀ : C.Ob b₀) (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t),
    ∃! ξ : s₀ ⟶[[g₀]] s, ξ ≫ᵈᵈ θ = χ

namespace IsCartesian

variable {a : A} {b b' : B.Ob a} {g : b ⟶[𝟙 a] b'} {s : C.Ob b} {t : C.Ob b'}
  {θ : s ⟶[[g]] t}

/-- The unique factorization of `χ` through a cartesian `θ`. -/
noncomputable def lift (H : IsCartesian θ) {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀}
    (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t) : s₀ ⟶[[g₀]] s :=
  (H g₀ s₀ χ).choose

theorem lift_fac (H : IsCartesian θ) {b₀ : B.Ob a} (g₀ : b₀ ⟶[𝟙 a] b) {s₀ : C.Ob b₀}
    (χ : s₀ ⟶[[g₀ ≫ᵈ g]] t) : lift H g₀ χ ≫ᵈᵈ θ = χ :=
  (H g₀ s₀ χ).choose_spec.1

/-- Any factorization of `χ` through `θ` agrees with `lift`. -/
theorem lift_uniq (H : IsCartesian θ) {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀}
    {χ : s₀ ⟶[[g₀ ≫ᵈ g]] t} (ξ : s₀ ⟶[[g₀]] s) (hξ : ξ ≫ᵈᵈ θ = χ) : ξ = lift H g₀ χ :=
  (H g₀ s₀ χ).choose_spec.2 ξ hξ

/-- Two maps into `s` that agree after postcomposition with a cartesian `θ` are equal. -/
theorem hom_ext (H : IsCartesian θ) {b₀ : B.Ob a} {g₀ : b₀ ⟶[𝟙 a] b} {s₀ : C.Ob b₀}
    {ξ ξ' : s₀ ⟶[[g₀]] s} (h : ξ ≫ᵈᵈ θ = ξ' ≫ᵈᵈ θ) : ξ = ξ' :=
  (lift_uniq H ξ rfl).trans (lift_uniq H ξ' h.symm).symm

end IsCartesian

end Opcartesian

end DoubleDisplayed
