import Rules.Category
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The bicategory of profunctors

A profunctor `P : A ⇸ B` between small categories consists of sets `P.obj a b` with a
contravariant action `P.lmap` of `A` and a covariant action `P.rmap` of `B` that commute; this is
the same data as a functor `Aᵒᵖ × B ⥤ Type u`. Profunctors compose by the coend:
`(comp P Q).obj a c` is the coend over `b` of `P.obj a b × Q.obj b c`, realised as a quotient, and
form the bicategory `ProfCat`.

The category laws, the action laws of profunctors, and the naturality of their morphisms are
declared as rewrite rules. They are oriented so that composites are right-associated, `lmap` is
outermost, and components of morphisms are innermost. As a result, most coherence laws of
`ProfCat` hold by `rfl` once the quotients are reduced to generators. Requires the `rewrite-rules`
fork of Lean.
-/

open CategoryTheory

universe u

/-- A profunctor from `A` to `B`: a family of types `obj a b`, contravariant in `a` and covariant in
`b`. -/
structure Profunctor (A : Type u) [SmallCategory A] (B : Type u) [SmallCategory B] where
  /-- The type of elements of `P` over `(a, b)`. -/
  obj : A → B → Type u
  /-- The contravariant action of `A`. -/
  lmap {a a' : A} {b : B} : (a' ⟶ a) → obj a b → obj a' b
  /-- The covariant action of `B`. -/
  rmap {a : A} {b b' : B} : (b ⟶ b') → obj a b → obj a b'
  lmap_id (a : A) {b : B} (x : obj a b) : lmap (𝟙 a) x = x
  lmap_comp {a a' a'' : A} {b : B} (g : a'' ⟶ a') (f : a' ⟶ a) (x : obj a b) :
    lmap (g ≫ f) x = lmap g (lmap f x)
  rmap_id {a : A} (b : B) (x : obj a b) : rmap (𝟙 b) x = x
  rmap_comp {a : A} {b b' b'' : B} (g : b ⟶ b') (g' : b' ⟶ b'') (x : obj a b) :
    rmap (g ≫ g') x = rmap g' (rmap g x)
  rmap_lmap {a a' : A} {b b' : B} (f : a' ⟶ a) (g : b ⟶ b') (x : obj a b) :
    rmap g (lmap f x) = lmap f (rmap g x)

attribute [rewrite_rule] Profunctor.lmap_id Profunctor.lmap_comp Profunctor.rmap_id
  Profunctor.rmap_comp Profunctor.rmap_lmap

namespace Profunctor

/-- `A ⇸ B` is the type of profunctors from `A` to `B`. -/
scoped infixr:10 " ⇸ " => Profunctor

variable {A B C D : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
  [SmallCategory D]

/-! ## Morphisms of profunctors -/

/-- A morphism of profunctors: a family of maps commuting with both actions. -/
structure Hom (P Q : A ⇸ B) where
  /-- The component at `(a, b)`. -/
  app (a : A) (b : B) : P.obj a b → Q.obj a b
  app_lmap {a a' : A} {b : B} (f : a' ⟶ a) (x : P.obj a b) :
    app a' b (P.lmap f x) = Q.lmap f (app a b x)
  app_rmap {a : A} {b b' : B} (g : b ⟶ b') (x : P.obj a b) :
    app a b' (P.rmap g x) = Q.rmap g (app a b x)

attribute [rewrite_rule] Hom.app_lmap Hom.app_rmap

theorem Hom.ext' {P Q : A ⇸ B} {η θ : Hom P Q} (h : ∀ a b x, η.app a b x = θ.app a b x) :
    η = θ := by
  cases η; cases θ; congr; funext a b x; exact h a b x

instance category : Category (A ⇸ B) where
  Hom := Hom
  id P := { app _ _ x := x, app_lmap := by intros; rfl, app_rmap := by intros; rfl }
  comp η θ :=
    { app a b x := θ.app a b (η.app a b x), app_lmap := by intros; rfl,
      app_rmap := by intros; rfl }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem hom_ext {P Q : A ⇸ B} {η θ : P ⟶ Q}
    (h : ∀ a b x, Hom.app η a b x = Hom.app θ a b x) : η = θ :=
  Hom.ext' h

/-- Reduces an equation of morphisms of profunctors to their components. -/
macro "hom_ext" x:ident : tactic =>
  `(tactic| (refine Profunctor.hom_ext fun _ _ $x => ?_))

/-! ## The identity profunctor -/

/-- The identity profunctor `(a, a') ↦ (a ⟶ a')`. Its laws hold by the category rewrite rules. -/
def hom (A : Type u) [SmallCategory A] : A ⇸ A where
  obj a a' := a ⟶ a'
  lmap f h := f ≫ h
  rmap g h := h ≫ g
  lmap_id := by intros; rfl
  lmap_comp := by intros; rfl
  rmap_id := by intros; rfl
  rmap_comp := by intros; rfl
  rmap_lmap := by intros; rfl

/-! ## Composition -/

/-- The relation generating the coend over `b` of `P.obj a b × Q.obj b c`. -/
inductive CompRel (P : A ⇸ B) (Q : B ⇸ C) (a : A) (c : C) :
    (Σ b : B, P.obj a b × Q.obj b c) → (Σ b : B, P.obj a b × Q.obj b c) → Prop
  | intro {b b' : B} (g : b ⟶ b') (p : P.obj a b) (q : Q.obj b' c) :
      CompRel P Q a c ⟨b', P.rmap g p, q⟩ ⟨b, p, Q.lmap g q⟩

/-- The coend over `b` of `P.obj a b × Q.obj b c`. -/
def CompObj (P : A ⇸ B) (Q : B ⇸ C) (a : A) (c : C) : Type u :=
  Quot (CompRel P Q a c)

namespace CompObj

variable {P : A ⇸ B} {Q : B ⇸ C} {a : A} {c : C}

/-- The class of `(p, q)` in the coend. -/
def mk (b : B) (p : P.obj a b) (q : Q.obj b c) : CompObj P Q a c :=
  Quot.mk _ ⟨b, p, q⟩

theorem sound {b b' : B} (g : b ⟶ b') (p : P.obj a b) (q : Q.obj b' c) :
    mk b' (P.rmap g p) q = mk b p (Q.lmap g q) :=
  Quot.sound (.intro g p q)

@[elab_as_elim]
theorem ind {motive : CompObj P Q a c → Prop} (h : ∀ b p q, motive (mk b p q))
    (x : CompObj P Q a c) : motive x :=
  Quot.ind (fun ⟨b, p, q⟩ => h b p q) x

/-- Defines a function out of the coend from one that respects the coend relation. -/
def lift {X : Sort*} (F : ∀ b, P.obj a b → Q.obj b c → X)
    (h : ∀ {b b' : B} (g : b ⟶ b') (p : P.obj a b) (q : Q.obj b' c),
      F b' (P.rmap g p) q = F b p (Q.lmap g q)) (x : CompObj P Q a c) : X :=
  Quot.lift (fun t => F t.1 t.2.1 t.2.2) (by rintro _ _ ⟨g, p, q⟩; exact h g p q) x

/-- The contravariant action on the coend. -/
def lmap {a' : A} (f : a' ⟶ a) : CompObj P Q a c → CompObj P Q a' c :=
  lift (fun b p q => mk b (P.lmap f p) q) (fun g p q => sound g (P.lmap f p) q)

/-- The covariant action on the coend. -/
def rmap {c' : C} (h : c ⟶ c') : CompObj P Q a c → CompObj P Q a c' :=
  lift (fun b p q => mk b p (Q.rmap h q)) (fun g p q => sound g p (Q.rmap h q))

end CompObj

/-- The composite `comp P Q : A ⇸ C` of `P : A ⇸ B` and
`Q : B ⇸ C`. -/
def comp (P : A ⇸ B) (Q : B ⇸ C) : A ⇸ C where
  obj := CompObj P Q
  lmap := CompObj.lmap
  rmap := CompObj.rmap
  lmap_id := by intros; rename_i x; induction x using CompObj.ind; rfl
  lmap_comp := by intros; rename_i x; induction x using CompObj.ind; rfl
  rmap_id := by intros; rename_i x; induction x using CompObj.ind; rfl
  rmap_comp := by intros; rename_i x; induction x using CompObj.ind; rfl
  rmap_lmap := by intros; rename_i x; induction x using CompObj.ind; rfl

/-! ## Whiskering -/

/-- Left whiskering `whiskerLeft P η : comp P Q ⟶ comp P Q'`. -/
def whiskerLeft (P : A ⇸ B) {Q Q' : B ⇸ C} (η : Q ⟶ Q') :
    Hom (comp P Q) (comp P Q') where
  app _ _ := CompObj.lift (fun b p q => CompObj.mk b p (Hom.app η b _ q))
    (fun g p q => CompObj.sound g p (Hom.app η _ _ q))
  app_lmap := by intros; rename_i x; induction x using CompObj.ind; rfl
  app_rmap := by intros; rename_i x; induction x using CompObj.ind; rfl

/-- Right whiskering `whiskerRight η Q : comp P Q ⟶ comp P' Q`. -/
def whiskerRight {P P' : A ⇸ B} (η : P ⟶ P') (Q : B ⇸ C) :
    Hom (comp P Q) (comp P' Q) where
  app _ _ := CompObj.lift (fun b p q => CompObj.mk b (Hom.app η _ b p) q)
    (fun g p q => CompObj.sound g (Hom.app η _ _ p) q)
  app_lmap := by intros; rename_i x; induction x using CompObj.ind; rfl
  app_rmap := by intros; rename_i x; induction x using CompObj.ind; rfl

/-! ## Unitors and associator -/

/-- The left unitor `comp (hom A) P ≅ P`, sending `CompObj.mk _ h p` to `P.lmap h p`. -/
def leftUnitor (P : A ⇸ B) : comp (hom A) P ≅ P where
  hom := ({
    app _ _ := CompObj.lift (fun _ h p => P.lmap h p) (fun _ _ _ => rfl)
    app_lmap := by intros; rename_i x; induction x using CompObj.ind; rfl
    app_rmap := by intros; rename_i x; induction x using CompObj.ind; rfl } : Hom _ _)
  inv := ({
    app a _ p := CompObj.mk a (𝟙 a) p
    app_lmap := fun f _ => (CompObj.sound (P := hom A) (Q := P) f (𝟙 _) _).symm
    app_rmap := by intros; rfl } : Hom _ _)
  hom_inv_id := by
    hom_ext x
    induction x using CompObj.ind
    rfl
  inv_hom_id := by hom_ext x; rfl

/-- The right unitor `comp P (hom B) ≅ P`, sending `CompObj.mk _ p h` to `P.rmap h p`. -/
def rightUnitor (P : A ⇸ B) : comp P (hom B) ≅ P where
  hom := ({
    app _ _ := CompObj.lift (fun _ p h => P.rmap h p) (fun _ _ _ => rfl)
    app_lmap := by intros; rename_i x; induction x using CompObj.ind; rfl
    app_rmap := by intros; rename_i x; induction x using CompObj.ind; rfl } : Hom _ _)
  inv := ({
    app _ b p := CompObj.mk b p (𝟙 b)
    app_lmap := by intros; rfl
    app_rmap := fun g _ => CompObj.sound (P := P) (Q := hom B) g _ (𝟙 _) } : Hom _ _)
  hom_inv_id := by
    hom_ext x
    induction x using CompObj.ind
    rfl
  inv_hom_id := by hom_ext x; rfl

/-- The components of the associator, sending the class of `((p, q), r)` to that of
`(p, (q, r))`. -/
def assocHom (P : A ⇸ B) (Q : B ⇸ C) (R : C ⇸ D) (a : A) (d : D) :
    CompObj (comp P Q) R a d → CompObj P (comp Q R) a d :=
  CompObj.lift
    (fun c x r => CompObj.lift (fun b p q => CompObj.mk b p (CompObj.mk c q r))
      (fun g p q => CompObj.sound (P := P) (Q := comp Q R) g p (CompObj.mk c q r)) x)
    (fun g x r => by
      induction x using CompObj.ind with
      | h b p q => exact congrArg (CompObj.mk b p) (CompObj.sound g q r))

/-- The components of the inverse associator, sending the class of `(p, (q, r))` to that of
`((p, q), r)`. -/
def assocInv (P : A ⇸ B) (Q : B ⇸ C) (R : C ⇸ D) (a : A) (d : D) :
    CompObj P (comp Q R) a d → CompObj (comp P Q) R a d :=
  CompObj.lift
    (fun b p y => CompObj.lift (fun c q r => CompObj.mk c (CompObj.mk b p q) r)
      (fun g q r => CompObj.sound (P := comp P Q) (Q := R) g (CompObj.mk b p q) r) y)
    (fun g p y => by
      induction y using CompObj.ind with
      | h c q r => exact congrArg (CompObj.mk c · r) (CompObj.sound g p q))

/-- The associator `comp (comp P Q) R ≅ comp P (comp Q R)`. -/
def associator (P : A ⇸ B) (Q : B ⇸ C) (R : C ⇸ D) :
    comp (comp P Q) R ≅ comp P (comp Q R) where
  hom := ({
    app := assocHom P Q R
    app_lmap := by
      intros; rename_i x
      induction x using CompObj.ind with | h _ x _ => induction x using CompObj.ind; rfl
    app_rmap := by
      intros; rename_i x
      induction x using CompObj.ind with
      | h _ x _ => induction x using CompObj.ind; rfl } : Hom _ _)
  inv := ({
    app := assocInv P Q R
    app_lmap := by
      intros; rename_i x
      induction x using CompObj.ind with | h _ _ y => induction y using CompObj.ind; rfl
    app_rmap := by
      intros; rename_i x
      induction x using CompObj.ind with
      | h _ _ y => induction y using CompObj.ind; rfl } : Hom _ _)
  hom_inv_id := by
    hom_ext x
    induction x using CompObj.ind with | h _ x _ => induction x using CompObj.ind; rfl
  inv_hom_id := by
    hom_ext x
    induction x using CompObj.ind with | h _ _ y => induction y using CompObj.ind; rfl

end Profunctor

/-! ## The bicategory -/

/-- The bicategory of small categories, profunctors, and morphisms of profunctors. -/
structure ProfCat : Type (u + 1) where
  /-- Construct an object of `ProfCat` from a small category. -/
  of ::
  /-- The underlying type of objects. -/
  carrier : Type u
  [str : SmallCategory carrier]

namespace ProfCat

attribute [instance] ProfCat.str

instance : CoeSort ProfCat (Type u) := ⟨ProfCat.carrier⟩

open Profunctor

instance bicategory : Bicategory ProfCat where
  Hom A B := A ⇸ B
  id A := hom A
  comp P Q := comp P Q
  homCategory _ _ := Profunctor.category
  whiskerLeft P _ _ η := whiskerLeft P η
  whiskerRight η Q := whiskerRight η Q
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  whiskerLeft_comp := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  id_whiskerLeft := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  comp_whiskerLeft := by
    intros; hom_ext x
    induction x using CompObj.ind with | h _ x _ => induction x using CompObj.ind; rfl
  id_whiskerRight := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  comp_whiskerRight := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  whiskerRight_id := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  whiskerRight_comp := by
    intros; hom_ext x
    induction x using CompObj.ind with | h _ _ y => induction y using CompObj.ind; rfl
  whisker_assoc := by
    intros; hom_ext x
    induction x using CompObj.ind with | h _ x _ => induction x using CompObj.ind; rfl
  whisker_exchange := by
    intros; hom_ext x; induction x using CompObj.ind; rfl
  pentagon := by
    intros; hom_ext x
    induction x using CompObj.ind with
    | h _ x _ => induction x using CompObj.ind with
      | h _ x _ => induction x using CompObj.ind; rfl
  triangle := by
    intros _ _ _ f g; hom_ext x
    induction x using CompObj.ind with
    | h _ x q =>
      induction x using CompObj.ind with
      | h _ p h => exact (CompObj.sound (P := f) (Q := g) h p q).symm

end ProfCat
