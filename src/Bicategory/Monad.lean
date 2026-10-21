import Bicategory.Basic
import Rules.StrictPseudofunctor

/-!
# 2-monads and 2-comonads, and their 2-categories of algebras and coalgebras

A (strict) *2-monad* on a 2-category `C` is a strict 2-functor `T : C ⥤ C` (Mathlib's
`StrictPseudofunctor`) with a unit `η x : x ⟶ T x` and a multiplication `μ x : T (T x) ⟶ T x`
that are 2-natural and satisfy the monad laws on the nose. 2-naturality has two parts: the
1-dimensional `η x ≫ T m = m ≫ η y`, and the 2-dimensional `η x ◁ T α = α ▷ η y` for 2-cells
`α : m ⟶ n`. The former is a rule, so the latter is stated without transport: its two sides have
the definitionally equal types `η x ≫ T m ⟶ η x ≫ T n` and `m ≫ η y ⟶ n ≫ η y`. For the rule to
apply, the 1-dimensional data (`PreTwoMonad`) is a field of `TwoMonad`, rather than a parent: the
fields of a parent are local variables while a structure is elaborated. Dually for 2-comonads.

The *strict algebras* of a 2-monad `M` form a 2-category `Alg M`: an algebra is an object `x` with
an action `T x ⟶ x` satisfying the unit and associativity laws, a 1-cell is a 1-cell `m` commuting
with the actions, and a 2-cell is a 2-cell `α` with `a ◁ α = T α ▷ a'`. The equations of 1- and
2-cells are rules, and the laws of the 2-category hold by `rfl`. Dually, `Coalg M` for 2-comonads.

The laws of strict 2-functors are rules (`Rules.StrictPseudofunctor`); here they get their
whiskered forms `F.map₂ (f ◁ η) ↦ F.map f ◁ F.map₂ η` and `F.map₂ (η ▷ f) ↦ F.map₂ η ▷ F.map f`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory

namespace StrictPseudofunctor

variable {C : Type u} [TwoCategory.{w, v} C] (F : StrictPseudofunctor C C)

@[rewrite_rule]
theorem map₂_whiskerLeft' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    F.map₂ (f ◁ η) = F.map f ◁ F.map₂ η :=
  (F.map₂_whisker_left f η).trans (by kernel_rfl)

@[rewrite_rule]
theorem map₂_whiskerRight' {a b c : C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    F.map₂ (η ▷ h) = F.map₂ η ▷ F.map h :=
  (F.map₂_whisker_right η h).trans (by kernel_rfl)

end StrictPseudofunctor

namespace TwoCategory

variable (C : Type u) [TwoCategory.{w, v} C]

/-! ## 2-monads -/

/-- The 1-dimensional data of a 2-monad: a strict 2-functor with a 1-natural unit and
multiplication satisfying the monad laws. -/
structure PreTwoMonad where
  /-- The underlying strict 2-functor. -/
  T : StrictPseudofunctor C C
  /-- The unit. -/
  η (x : C) : x ⟶ T.obj x
  /-- The multiplication. -/
  μ (x : C) : T.obj (T.obj x) ⟶ T.obj x
  η_naturality {x y : C} (m : x ⟶ y) : η x ≫ T.map m = m ≫ η y
  μ_naturality {x y : C} (m : x ⟶ y) : μ x ≫ T.map m = T.map (T.map m) ≫ μ y
  unit_left (x : C) : η (T.obj x) ≫ μ x = 𝟙 (T.obj x)
  unit_right (x : C) : T.map (η x) ≫ μ x = 𝟙 (T.obj x)
  assoc (x : C) : μ (T.obj x) ≫ μ x = T.map (μ x) ≫ μ x

attribute [rewrite_rule] PreTwoMonad.η_naturality PreTwoMonad.μ_naturality

namespace PreTwoMonad

variable {C} (M : PreTwoMonad C)

@[rewrite_rule]
theorem η_naturality_assoc {x y z : C} (m : x ⟶ y) (k : M.T.obj y ⟶ z) :
    M.η x ≫ M.T.map m ≫ k = m ≫ M.η y ≫ k :=
  congrArg (· ≫ k) (M.η_naturality m)

@[rewrite_rule]
theorem μ_naturality_assoc {x y z : C} (m : x ⟶ y) (k : M.T.obj y ⟶ z) :
    M.μ x ≫ M.T.map m ≫ k = M.T.map (M.T.map m) ≫ M.μ y ≫ k :=
  congrArg (· ≫ k) (M.μ_naturality m)

end PreTwoMonad

/-- A (strict) 2-monad: a `PreTwoMonad` whose unit and multiplication are also 2-natural. -/
structure TwoMonad where
  /-- The 1-dimensional data. -/
  toPreTwoMonad : PreTwoMonad C
  η_naturality₂ {x y : C} {m n : x ⟶ y} (α : m ⟶ n) :
    toPreTwoMonad.η x ◁ toPreTwoMonad.T.map₂ α = α ▷ toPreTwoMonad.η y
  μ_naturality₂ {x y : C} {m n : x ⟶ y} (α : m ⟶ n) :
    toPreTwoMonad.μ x ◁ toPreTwoMonad.T.map₂ α =
      toPreTwoMonad.T.map₂ (toPreTwoMonad.T.map₂ α) ▷ toPreTwoMonad.μ y

/-! ## 2-comonads -/

/-- The 1-dimensional data of a 2-comonad: a strict 2-functor with a 1-natural counit and
comultiplication satisfying the comonad laws. -/
structure PreTwoComonad where
  /-- The underlying strict 2-functor. -/
  T : StrictPseudofunctor C C
  /-- The counit. -/
  ε (x : C) : T.obj x ⟶ x
  /-- The comultiplication. -/
  δ (x : C) : T.obj x ⟶ T.obj (T.obj x)
  ε_naturality {x y : C} (m : x ⟶ y) : T.map m ≫ ε y = ε x ≫ m
  δ_naturality {x y : C} (m : x ⟶ y) : T.map m ≫ δ y = δ x ≫ T.map (T.map m)
  counit_left (x : C) : δ x ≫ ε (T.obj x) = 𝟙 (T.obj x)
  counit_right (x : C) : δ x ≫ T.map (ε x) = 𝟙 (T.obj x)
  coassoc (x : C) : δ x ≫ δ (T.obj x) = δ x ≫ T.map (δ x)

attribute [rewrite_rule] PreTwoComonad.ε_naturality PreTwoComonad.δ_naturality

namespace PreTwoComonad

variable {C} (M : PreTwoComonad C)

@[rewrite_rule]
theorem ε_naturality_assoc {x y z : C} (m : x ⟶ y) (k : y ⟶ z) :
    M.T.map m ≫ M.ε y ≫ k = M.ε x ≫ m ≫ k :=
  congrArg (· ≫ k) (M.ε_naturality m)

@[rewrite_rule]
theorem δ_naturality_assoc {x y z : C} (m : x ⟶ y) (k : M.T.obj (M.T.obj y) ⟶ z) :
    M.T.map m ≫ M.δ y ≫ k = M.δ x ≫ M.T.map (M.T.map m) ≫ k :=
  congrArg (· ≫ k) (M.δ_naturality m)

end PreTwoComonad

/-- A (strict) 2-comonad: a `PreTwoComonad` whose counit and comultiplication are also
2-natural. -/
structure TwoComonad where
  /-- The 1-dimensional data. -/
  toPreTwoComonad : PreTwoComonad C
  ε_naturality₂ {x y : C} {m n : x ⟶ y} (α : m ⟶ n) :
    toPreTwoComonad.T.map₂ α ▷ toPreTwoComonad.ε y = toPreTwoComonad.ε x ◁ α
  δ_naturality₂ {x y : C} {m n : x ⟶ y} (α : m ⟶ n) :
    toPreTwoComonad.T.map₂ α ▷ toPreTwoComonad.δ y =
      toPreTwoComonad.δ x ◁ toPreTwoComonad.T.map₂ (toPreTwoComonad.T.map₂ α)

variable {C}

/-! ## The 2-category of algebras of a 2-monad -/

namespace TwoMonad

variable (M : TwoMonad C)

/-- The underlying 2-functor. -/
abbrev T : StrictPseudofunctor C C :=
  M.toPreTwoMonad.T

/-- The unit. -/
abbrev η (x : C) : x ⟶ M.T.obj x :=
  M.toPreTwoMonad.η x

/-- The multiplication. -/
abbrev μ (x : C) : M.T.obj (M.T.obj x) ⟶ M.T.obj x :=
  M.toPreTwoMonad.μ x

/-- A strict algebra of a 2-monad: an object with an action satisfying the unit and associativity
laws. -/
structure Alg where
  /-- The underlying object. -/
  obj : C
  /-- The action. -/
  act : M.T.obj obj ⟶ obj
  unit : M.η obj ≫ act = 𝟙 obj
  assoc : M.μ obj ≫ act = M.T.map act ≫ act

namespace Alg

variable {M}

/-- A strict morphism of algebras: a 1-cell commuting with the actions. -/
@[ext]
structure Hom (A A' : Alg M) where
  /-- The underlying 1-cell. -/
  hom : A.obj ⟶ A'.obj
  w : A.act ≫ hom = M.T.map hom ≫ A'.act

attribute [rewrite_rule] Hom.w

namespace Hom

variable {A A' : Alg M} (m : Hom A A')

@[rewrite_rule]
theorem w_assoc {z : C} (k : A'.obj ⟶ z) : A.act ≫ m.hom ≫ k = M.T.map m.hom ≫ A'.act ≫ k :=
  congrArg (· ≫ k) m.w

@[rewrite_rule]
theorem whiskerLeft_w {z : C} {k k' : A'.obj ⟶ z} (η : k ⟶ k') :
    A.act ◁ m.hom ◁ η = M.T.map m.hom ◁ A'.act ◁ η :=
  eq_of_heq (whiskerLeft_congr m.w η)

@[rewrite_rule]
theorem whiskerRight_w {z : C} {u u' : z ⟶ M.T.obj A.obj} (θ : u ⟶ u') :
    θ ▷ A.act ▷ m.hom = θ ▷ M.T.map m.hom ▷ A'.act :=
  eq_of_heq (whiskerRight_congr θ m.w)

end Hom

/-- A 2-cell of algebras: a 2-cell between the underlying 1-cells compatible with the actions. -/
@[ext]
structure Hom₂ {A A' : Alg M} (m n : Hom A A') where
  /-- The underlying 2-cell. -/
  hom : m.hom ⟶ n.hom
  w : A.act ◁ hom = M.T.map₂ hom ▷ A'.act

attribute [rewrite_rule] Hom₂.w

/-- The equation of a 2-cell of algebras, whiskered on the right. -/
@[rewrite_rule]
theorem Hom₂.w_whiskerRight {A A' : Alg M} {m n : Hom A A'} (α : Hom₂ m n) {z : C}
    (k : A'.obj ⟶ z) : A.act ◁ (α.hom ▷ k) = M.T.map₂ α.hom ▷ A'.act ▷ k := by
  rw [← α.w]

instance : CategoryStruct.{v} (Alg M) where
  Hom := Hom
  id A := ⟨𝟙 A.obj, by kernel_rfl⟩
  comp m n := ⟨m.hom ≫ n.hom, by kernel_rfl⟩

instance homCategory (A A' : Alg M) : Category.{w} (A ⟶ A') where
  Hom := Hom₂
  id m := ⟨𝟙 m.hom, by kernel_rfl⟩
  comp α β := ⟨α.hom ≫ β.hom, by kernel_rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom₂_ext {A A' : Alg M} {m n : A ⟶ A'} {α β : m ⟶ n} (h : α.hom = β.hom) : α = β :=
  Hom₂.ext h

instance bicategory : Bicategory.{w, v} (Alg M) where
  homCategory := homCategory
  whiskerLeft m _ _ α := ⟨m.hom ◁ α.hom, by kernel_rfl⟩
  whiskerRight α n := ⟨α.hom ▷ n.hom, by kernel_rfl⟩
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _
  whiskerLeft_id := by intros; rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; rfl
  comp_whiskerLeft := by intros; rfl
  id_whiskerRight := by intros; rfl
  comp_whiskerRight := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerRight_comp := by intros; rfl
  whisker_assoc := by intros; rfl
  whisker_exchange := by intros; ext; exact whisker_exchange _ _
  pentagon := by intros; rfl
  triangle := by intros; rfl

/-- The strict algebras of a 2-monad form a 2-category. -/
instance twoCategory : TwoCategory.{w, v} (Alg M) where
  toBicategory := bicategory
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  leftUnitor_eqToIso := by intros; rfl
  rightUnitor_eqToIso := by intros; rfl
  associator_eqToIso := by intros; rfl

end Alg

end TwoMonad

/-! ## The 2-category of coalgebras of a 2-comonad -/

namespace TwoComonad

variable (M : TwoComonad C)

/-- The underlying 2-functor. -/
abbrev T : StrictPseudofunctor C C :=
  M.toPreTwoComonad.T

/-- The counit. -/
abbrev ε (x : C) : M.T.obj x ⟶ x :=
  M.toPreTwoComonad.ε x

/-- The comultiplication. -/
abbrev δ (x : C) : M.T.obj x ⟶ M.T.obj (M.T.obj x) :=
  M.toPreTwoComonad.δ x

/-- A strict coalgebra of a 2-comonad: an object with a coaction satisfying the counit and
coassociativity laws. -/
structure Coalg where
  /-- The underlying object. -/
  obj : C
  /-- The coaction. -/
  coact : obj ⟶ M.T.obj obj
  counit : coact ≫ M.ε obj = 𝟙 obj
  coassoc : coact ≫ M.δ obj = coact ≫ M.T.map coact

namespace Coalg

variable {M}

/-- A strict morphism of coalgebras: a 1-cell commuting with the coactions. -/
@[ext]
structure Hom (A A' : Coalg M) where
  /-- The underlying 1-cell. -/
  hom : A.obj ⟶ A'.obj
  w : hom ≫ A'.coact = A.coact ≫ M.T.map hom

attribute [rewrite_rule] Hom.w

namespace Hom

variable {A A' : Coalg M} (m : Hom A A')

@[rewrite_rule]
theorem w_assoc {z : C} (k : M.T.obj A'.obj ⟶ z) :
    m.hom ≫ A'.coact ≫ k = A.coact ≫ M.T.map m.hom ≫ k :=
  congrArg (· ≫ k) m.w

@[rewrite_rule]
theorem whiskerLeft_w {z : C} {k k' : M.T.obj A'.obj ⟶ z} (η : k ⟶ k') :
    m.hom ◁ A'.coact ◁ η = A.coact ◁ M.T.map m.hom ◁ η :=
  eq_of_heq (whiskerLeft_congr m.w η)

@[rewrite_rule]
theorem whiskerRight_w {z : C} {u u' : z ⟶ A.obj} (θ : u ⟶ u') :
    θ ▷ m.hom ▷ A'.coact = θ ▷ A.coact ▷ M.T.map m.hom :=
  eq_of_heq (whiskerRight_congr θ m.w)

end Hom

/-- A 2-cell of coalgebras: a 2-cell between the underlying 1-cells compatible with the
coactions. -/
@[ext]
structure Hom₂ {A A' : Coalg M} (m n : Hom A A') where
  /-- The underlying 2-cell. -/
  hom : m.hom ⟶ n.hom
  w : hom ▷ A'.coact = A.coact ◁ M.T.map₂ hom

attribute [rewrite_rule] Hom₂.w

instance : CategoryStruct.{v} (Coalg M) where
  Hom := Hom
  id A := ⟨𝟙 A.obj, by kernel_rfl⟩
  comp m n := ⟨m.hom ≫ n.hom, by kernel_rfl⟩

instance homCategory (A A' : Coalg M) : Category.{w} (A ⟶ A') where
  Hom := Hom₂
  id m := ⟨𝟙 m.hom, by kernel_rfl⟩
  comp α β := ⟨α.hom ≫ β.hom, by kernel_rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom₂_ext {A A' : Coalg M} {m n : A ⟶ A'} {α β : m ⟶ n} (h : α.hom = β.hom) : α = β :=
  Hom₂.ext h

instance bicategory : Bicategory.{w, v} (Coalg M) where
  homCategory := homCategory
  whiskerLeft m _ _ α := ⟨m.hom ◁ α.hom, by kernel_rfl⟩
  whiskerRight α n := ⟨α.hom ▷ n.hom, by kernel_rfl⟩
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _
  whiskerLeft_id := by intros; rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; rfl
  comp_whiskerLeft := by intros; rfl
  id_whiskerRight := by intros; rfl
  comp_whiskerRight := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerRight_comp := by intros; rfl
  whisker_assoc := by intros; rfl
  whisker_exchange := by intros; ext; exact whisker_exchange _ _
  pentagon := by intros; rfl
  triangle := by intros; rfl

/-- The strict coalgebras of a 2-comonad form a 2-category. -/
instance twoCategory : TwoCategory.{w, v} (Coalg M) where
  toBicategory := bicategory
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  leftUnitor_eqToIso := by intros; rfl
  rightUnitor_eqToIso := by intros; rfl
  associator_eqToIso := by intros; rfl

end Coalg

end TwoComonad

end TwoCategory

end CategoryTheory
