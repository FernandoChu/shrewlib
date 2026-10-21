import Bicategory.Pullback
import Bicategory.Span

/-!
# The bicategory of spans in a 2-category

If a 2-category `B` has pullbacks (Mathlib's `Limits.HasPullbacks` for its underlying category),
its spans are the 1-cells of the bicategory of spans `Spans B`, whose 2-cells are the morphisms of
spans: the 1-cells of the 2-categories of spans (`Bicategory.Span`). The composite of
`s : Span a b` and `t : Span b c` is the chosen pullback `pullback s.right t.left`.

The whiskerings, unitors and associator are induced by `pullback.lift`. Its equations and that of
the pullback square are rules (`Rules.Pullback`, `Bicategory.Pullback`), so the laws of the
bicategory reduce by extensionality into the chosen pullbacks (`pullback_ext`) to equations that
hold by `rfl` (`span_ext`). These are checked in the kernel (`kernel_rfl`): the elaborator's unifier
is much slower on them, as it first tries to unify the arguments of the composites.

Mathlib's bicategory of spans `SpanBicat B ⊤ ⊤` is not used: its projections, lifts and associator
are not exposed, only lemmas about their composites, which as rules are slow to try and do not fire
once the legs of a span are unfolded.
-/

open CategoryTheory Bicategory Limits

universe w v u

namespace CategoryTheory.TwoCategory

variable (B : Type u) [TwoCategory.{w, v} B]

/-- The objects of the bicategory of spans in `B`. -/
structure Spans where
  /-- The underlying object of `B`. -/
  of : B

namespace Spans

variable {B} [Limits.HasPullbacks B]

noncomputable instance : CategoryStruct (Spans B) where
  Hom a b := Span a.of b.of
  id a := ⟨a.of, 𝟙 a.of, 𝟙 a.of⟩
  comp s t := ⟨pullback s.right t.left, pullback.fst _ _ ≫ s.left, pullback.snd _ _ ≫ t.right⟩

instance homCategory (a b : Spans B) : Category.{v} (a ⟶ b) :=
  StrictBicategory.category (Span a.of b.of)

variable {a b c d : Spans B}

/-- Whiskering a morphism of spans on the left with a span, by the universal property of the chosen
pullback. -/
noncomputable def whiskerLeft (s : a ⟶ b) {t t' : b ⟶ c} (m : t ⟶ t') : s ≫ t ⟶ s ≫ t' :=
  Span.Hom.mk (pullback.lift (pullback.fst s.right t.left) (pullback.snd s.right t.left ≫ m.hom)
    (by kernel_rfl)) (by kernel_rfl) (by kernel_rfl)

/-- Whiskering a morphism of spans on the right with a span. -/
noncomputable def whiskerRight {s s' : a ⟶ b} (m : s ⟶ s') (t : b ⟶ c) : s ≫ t ⟶ s' ≫ t :=
  Span.Hom.mk (pullback.lift (pullback.fst s.right t.left ≫ m.hom) (pullback.snd s.right t.left)
    (by kernel_rfl)) (by kernel_rfl) (by kernel_rfl)

/-- Proves an equation of morphisms of spans in the bicategory of spans: by extensionality into the
chosen pullbacks, it reduces to equations that hold by `rfl`, checked in the kernel. -/
macro "span_ext" : tactic =>
  `(tactic| (intros; apply Span.Hom.ext; (repeat' pullback_ext); all_goals kernel_rfl))

/-- The associator of spans, by the universal property of the chosen pullbacks. -/
noncomputable def associator (s : a ⟶ b) (t : b ⟶ c) (u : c ⟶ d) : (s ≫ t) ≫ u ≅ s ≫ t ≫ u :=
  Iso.mk
    (Span.Hom.mk
      (pullback.lift (f := s.right) (g := (t ≫ u).left)
        (pullback.fst (s ≫ t).right u.left ≫ pullback.fst s.right t.left)
        (pullback.lift (f := t.right) (g := u.left)
          (pullback.fst (s ≫ t).right u.left ≫ pullback.snd s.right t.left)
          (pullback.snd (s ≫ t).right u.left) (by kernel_rfl))
        (by kernel_rfl)) (by kernel_rfl) (by kernel_rfl))
    (Span.Hom.mk
      (pullback.lift (f := (s ≫ t).right) (g := u.left)
        (pullback.lift (f := s.right) (g := t.left) (pullback.fst s.right (t ≫ u).left)
          (pullback.snd s.right (t ≫ u).left ≫ pullback.fst t.right u.left) (by kernel_rfl))
        (pullback.snd s.right (t ≫ u).left ≫ pullback.snd t.right u.left) (by kernel_rfl))
      (by kernel_rfl) (by kernel_rfl))
    (by span_ext) (by span_ext)

/-- The left unitor of spans: the pullback along an identity is the projection. -/
noncomputable def leftUnitor (s : a ⟶ b) : 𝟙 a ≫ s ≅ s :=
  Iso.mk (Span.Hom.mk (pullback.snd (𝟙 a.of) s.left) (by kernel_rfl) (by kernel_rfl))
    (Span.Hom.mk (pullback.lift (f := 𝟙 a.of) (g := s.left) s.left (𝟙 _) (by kernel_rfl))
      (by kernel_rfl) (by kernel_rfl))
    (by span_ext) (by span_ext)

/-- The right unitor of spans: the pullback along an identity is the projection. -/
noncomputable def rightUnitor (s : a ⟶ b) : s ≫ 𝟙 b ≅ s :=
  Iso.mk (Span.Hom.mk (pullback.fst s.right (𝟙 b.of)) (by kernel_rfl) (by kernel_rfl))
    (Span.Hom.mk (pullback.lift (f := s.right) (g := 𝟙 b.of) (𝟙 _) s.right (by kernel_rfl))
      (by kernel_rfl) (by kernel_rfl))
    (by span_ext) (by span_ext)

/-- The bicategory of spans in a 2-category with pullbacks. Its 1-cells are spans, composed by
pullback, and its 2-cells are morphisms of spans. -/
noncomputable instance bicategory : Bicategory.{v, max u v} (Spans B) where
  whiskerLeft := Spans.whiskerLeft
  whiskerRight := Spans.whiskerRight
  associator := Spans.associator
  leftUnitor := Spans.leftUnitor
  rightUnitor := Spans.rightUnitor
  whiskerLeft_id := by span_ext
  whiskerLeft_comp := by span_ext
  id_whiskerLeft := by span_ext
  comp_whiskerLeft := by span_ext
  id_whiskerRight := by span_ext
  comp_whiskerRight := by span_ext
  whiskerRight_id := by span_ext
  whiskerRight_comp := by span_ext
  whisker_assoc := by span_ext
  whisker_exchange := by span_ext
  pentagon := by span_ext
  triangle := by span_ext

end Spans

end CategoryTheory.TwoCategory
