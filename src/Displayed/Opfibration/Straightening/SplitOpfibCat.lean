import Displayed.Opfibration.Straightening.Unstraighten
import Tactic.KernelTactic
import Displayed.Displayed.Straightening.Straighten
import Displayed.Opfibration.Basic

/-!
# The category of split opfibrations

A *split opfibration* over `A` is a functor `p : E ⥤ A` together with a split opcleavage, that
is, a `SplitOpfib` structure on its displayed category of fibres `fibres p`
(`Displayed/Displayed/Straightening/Straighten.lean`). `SplitOpfibCat`, displayed over `Cat`, has
the split opfibrations over `A` as objects, and as morphisms over `u` all morphisms of `cod Cat`
between the underlying functors: a functor `w` with `w ⋙ p' = p ⋙ u`, which need not preserve the
chosen lifts.

The forgetful functor `SplitOpfibCat.incl : SplitOpfibCat ⟶ cod Cat` is fully faithful, but it is
not injective on objects, as a functor can carry several split opcleavages, so `SplitOpfibCat` is
not a subcategory of `cod Cat`.

The projection `π : A ⋉ F ⥤ A` is a split opfibration: the chosen pushforward of `(a, x)` along
`f` is `(a', F f x)`, with lift `(f, 𝟙)`. Its laws hold by `rfl` once the equation `X.base = a` of
an object of the fibre is substituted. So the unstraightening lifts along `SplitOpfibCat.incl` to
`SplitOpfibCat` (`unstraightenSplit`), equipping `π` with this split opcleavage, and it is still
fully faithful there (`unstraightenSplitFullyFaithful`), since the morphisms are the same.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open Displayed.Straightening (Fibre FibreHom fibres)

open Grothendieck (Hom)

open scoped Displayed

/-! ## The split opcleavage of `A ⋉ F` -/

namespace Groth

variable {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u})

/-- The chosen pushforward of `(a, x)` along `f : a ⟶ a'` in `A ⋉ F`: `(a', F f x)`. -/
def push : ∀ {a a' : A} (_ : a ⟶ a'), Fibre (unstraightenObj F) a → Fibre (unstraightenObj F) a'
  | _, a', f, ⟨⟨_, x⟩, rfl⟩ => ⟨⟨a', (F.map f).toFunctor.obj x⟩, rfl⟩

/-- The chosen lift `(f, 𝟙) : (a, x) ⟶ (a', F f x)`. -/
def olift : ∀ {a a' : A} (f : a ⟶ a') (x : Fibre (unstraightenObj F) a),
    FibreHom (unstraightenObj F) f x (push F f x)
  | _, _, f, ⟨⟨_, _⟩, rfl⟩ => ⟨Hom.mk f (𝟙 _), rfl⟩

/-- The factorization of `(f ≫ g, φ)` through `(f, 𝟙)`: `(g, φ)`. -/
def oliftDesc : ∀ {a a' a'' : A} (f : a ⟶ a') (x : Fibre (unstraightenObj F) a) (g : a' ⟶ a'')
    {z : Fibre (unstraightenObj F) a''}, FibreHom (unstraightenObj F) (f ≫ g) x z →
      FibreHom (unstraightenObj F) g (push F f x) z
  | _, _, _, f, ⟨⟨_, y⟩, rfl⟩, g, ⟨⟨_, _⟩, rfl⟩, ⟨⟨kb, kf⟩, hk⟩ =>
    ⟨Hom.mk g (eqToHom (congrArg (fun t => (F.map t).toFunctor.obj y)
      (show kb = f ≫ g from hk).symm) ≫ kf), rfl⟩

/-- The chosen lifts are opcartesian: a morphism `(f ≫ g, φ)` factors as `(f, 𝟙) ≫ (g, φ)`. -/
def isOpcartesianOlift {a a' : A} (f : a ⟶ a') (x : Fibre (unstraightenObj F) a) :
    IsOpcartesian (D := fibres (unstraightenObj F)) (olift F f x) where
  desc g _ χ := oliftDesc F f x g χ
  desc_fac g z χ := by
    obtain ⟨⟨_, y⟩, rfl⟩ := x
    obtain ⟨⟨_, w⟩, rfl⟩ := z
    obtain ⟨⟨kb, kf⟩, hk⟩ := χ
    obtain rfl : kb = f ≫ g := hk
    rfl
  desc_uniq {_ g z χ} ψ h := by
    obtain ⟨⟨_, y⟩, rfl⟩ := x
    obtain ⟨⟨_, w⟩, rfl⟩ := z
    obtain ⟨⟨kb, kf⟩, hk⟩ := χ
    obtain rfl : kb = f ≫ g := hk
    obtain ⟨⟨gb, gf⟩, hg⟩ := ψ
    obtain rfl : gb = g := hg
    obtain rfl : gf = kf := by
      kernel_exact Groth.fiber_eq_of_eq (F := F) (X := ⟨_, y⟩) (Y := ⟨_, w⟩) (f := f ≫ gb)
        (φ := gf) (ψ := kf) (congrArg Subtype.val h)
    rfl

instance preSplitOpfib : PreSplitOpfib (fibres (unstraightenObj F)) where
  push f x := push F f x
  olift f x := olift F f x
  isOpcartesianOlift f x := isOpcartesianOlift F f x
  push_id := by rintro _ ⟨⟨_, _⟩, rfl⟩; rfl
  push_comp := by rintro _ _ _ _ _ ⟨⟨_, _⟩, rfl⟩; rfl

/-- **`π : A ⋉ F ⥤ A` is a split opfibration.** -/
instance splitOpfib : SplitOpfib (fibres (unstraightenObj F)) where
  olift_id := by rintro _ ⟨⟨_, _⟩, rfl⟩; rfl
  olift_comp := by rintro _ _ _ _ _ ⟨⟨_, _⟩, rfl⟩; rfl

end Groth

/-! ## The category of split opfibrations -/

/-- A split opfibration over `A`: an object of `cod Cat` over `A` with a split opcleavage of its
fibres. -/
structure SplitOpfibOb (A : Cat.{u, u}) where
  /-- The functor `p : E ⥤ A`. -/
  ob : (cod Cat.{u, u}).Ob A
  /-- The split opcleavage of `p`. -/
  [splitOpfib : SplitOpfib (fibres ob)]

attribute [instance] SplitOpfibOb.splitOpfib

/-- The split opfibrations, displayed over `Cat`: the morphisms are all morphisms of `cod Cat`
between the underlying functors, with no condition on the opcleavages. -/
def SplitOpfibCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := SplitOpfibOb A
  Hom u X Y := (cod Cat.{u, u}).Hom u X.ob Y.ob
  id X := (cod Cat.{u, u}).id X.ob
  comp φ ψ := (cod Cat.{u, u}).comp φ ψ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The functor forgetting the split opcleavage, into `cod Cat`. It is fully faithful, but not
injective on objects. -/
def SplitOpfibCat.incl : VertFunctor SplitOpfibCat.{u} (cod Cat.{u, u}) where
  obj X := X.ob
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The unstraightening into the split opfibrations -/

/-- The unstraightening, into the split opfibrations: `F` goes to `π : A ⋉ F ⥤ A`. -/
def unstraightenSplit : VertFunctor ICat.{u} SplitOpfibCat.{u} where
  obj F := { ob := unstraightenObj F, splitOpfib := Groth.splitOpfib F }
  map α := unstraighten.map α
  map_id F := unstraighten.map_id F
  map_comp α β := unstraighten.map_comp α β

/-- Followed by the inclusion, `unstraightenSplit` is the unstraightening. -/
theorem incl_obj_unstraightenSplit_obj {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) :
    SplitOpfibCat.incl.obj (unstraightenSplit.obj F) = unstraighten.obj F :=
  rfl

theorem incl_map_unstraightenSplit_map {A B : Cat.{u, u}} {u : A ⟶ B} {F : A ⥤ Cat.{u, u}}
    {G : B ⥤ Cat.{u, u}} (α : ICat.Hom u F G) :
    SplitOpfibCat.incl.map (unstraightenSplit.map α) = unstraighten.map α :=
  rfl

/-- The unstraightening into the split opfibrations is fully faithful, with the preimages of
`unstraighten`. -/
def unstraightenSplitFullyFaithful : unstraightenSplit.{u}.FullyFaithful where
  preimage w := unstraightenPreimage w
  map_preimage w := unstraighten_map_preimage w
  preimage_map α := unstraightenFullyFaithful.preimage_map α

end Displayed.Opfibration.Straightening
