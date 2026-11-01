module

public import LargeIndecomposable.Cleaving.Basic.Thin
public import LargeIndecomposable.Cleaving.Basic.Cleaving
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# Functors out of thin categories and a local cleaving criterion

A functor `ThinCat T ⥤ Q` is given by objects and a morphism for each pair
`le x y`, compatible with composition (`RayCat.ThinFunctorData`). If `Q` has
cancellation, such a functor is cleaving as soon as its morphisms are nonzero
and Gabriel–Roiter's condition b) of 13.8 holds for a generating family of
"arrows" of `T` (`RayCat.ThinFunctorData.isCleaving`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

variable {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}

open Classical in
variable (T) in
/-- The data of a functor `ThinCat T ⥤ Q`. -/
structure ThinFunctorData (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] where
  obj : V → Q
  mor : ∀ x y, T.le x y → (obj x ⟶ obj y)
  mor_id : ∀ x, mor x x (T.refl x) = 𝟙 _
  mor_comp : ∀ x y z (h : T.le x y) (h' : T.le y z),
    mor x y h ≫ mor y z h' = if hn : T.nz x y z then mor x z (T.nz_le x y z h h' hn) else 0

variable (T) in
/-- A generating family of arrows of `T`: every strict relation starts with an
arrow and ends with an arrow, with nonzero composites. -/
structure ThinArrows where
  ar : V → V → Prop
  ar_le : ∀ x y, ar x y → T.le x y
  ar_ne : ∀ x y, ar x y → x ≠ y
  first : ∀ x y, T.le x y → x ≠ y → ∃ z, ar x z ∧ T.le z y ∧ T.nz x z y
  last : ∀ x y, T.le x y → x ≠ y → ∃ z, T.le x z ∧ ar z y ∧ T.nz x z y

namespace ThinFunctorData

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (D : ThinFunctorData T Q)

/-- The functor. -/
def functor : ThinCat T ⥤ Q where
  obj X := D.obj X.as
  map {X Y} f := match f with
    | none => 0
    | some ⟨_, h⟩ => D.mor X.as Y.as h
  map_id X := D.mor_id X.as
  map_comp {X Y Z} f g := by
    rw [ThinCat.comp_def]
    rcases f with _ | ⟨⟨⟩, hf⟩
    · rw [ThinHom.comp_none_left]; simp
    rcases g with _ | ⟨⟨⟩, hg⟩
    · rw [ThinHom.comp_none_right]; simp
    rw [ThinHom.comp_some]
    change _ = D.mor _ _ hf ≫ D.mor _ _ hg
    rw [D.mor_comp]
    split_ifs <;> rfl

instance : D.functor.PreservesZeroMorphisms where
  map_zero _ _ := rfl

lemma functor_map_mor {X Y : ThinCat T} (h : T.le X.as Y.as) :
    D.functor.map (ThinCat.mor h) = D.mor X.as Y.as h := rfl

/-- The hypotheses of the local criterion. -/
structure Cleaves (Ar : ThinArrows T) : Prop where
  ne_zero : ∀ x y (h : T.le x y), D.mor x y h ≠ 0
  left : ∀ x z y (ha : Ar.ar x z) (hy : T.le x y),
    (∃ g, D.mor x z (Ar.ar_le x z ha) ≫ g = D.mor x y hy) → T.le z y ∧ T.nz x z y
  right : ∀ x z y (ha : Ar.ar z y) (hx : T.le x y),
    (∃ g, g ≫ D.mor z y (Ar.ar_le z y ha) = D.mor x y hx) → T.le x z ∧ T.nz x z y

variable [IsRayCategory Q] [Fintype Q] [DecidableEq Q]

lemma not_isIso_mor_of_ne {x y : V} (h : T.le x y) (hne : x ≠ y) :
    ¬IsIso (ThinCat.mor (X := (⟨x⟩ : ThinCat T)) (Y := ⟨y⟩) h) := fun hI ↦
  hne (congrArg ThinCat.as (IsRayCategory.skeletal ⟨asIso (ThinCat.mor h)⟩))

lemma mor_eq_comp {x z y : V} (h : T.le x z) (h' : T.le z y) (hn : T.nz x z y) :
    D.mor x y (T.nz_le x z y h h' hn) = D.mor x z h ≫ D.mor z y h' := by
  rw [D.mor_comp, dif_pos hn]

lemma image_aux {Ar : ThinArrows T} (hc : D.Cleaves Ar) (hL : LeftCancel Q) (hR : RightCancel Q) :
    ∀ (n : ℕ) {x' x y y' : V} (hμ : T.le x' x) (hν : T.le y y') (hκ : T.le x' y')
      (ρ : D.obj x ⟶ D.obj y),
      depth (ThinCat.mor (X := (⟨x'⟩ : ThinCat T)) (Y := ⟨x⟩) hμ) +
        depth (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨y'⟩) hν) ≤ n →
      D.mor x' x hμ ≫ ρ ≫ D.mor y y' hν = D.mor x' y' hκ →
      ∃ l : (⟨x⟩ : ThinCat T) ⟶ ⟨y⟩, ρ = D.functor.map l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x' x y y' hμ hν hκ ρ hn h
  by_cases hyy : y = y'
  · subst hyy
    by_cases hxx : x' = x
    · subst hxx
      rw [D.mor_id, D.mor_id, Category.id_comp, Category.comp_id] at h
      exact ⟨ThinCat.mor hκ, h⟩
    · obtain ⟨z, haz, hzx, hnz⟩ := Ar.first x' x hμ hxx
      have hμ' : D.mor x' x hμ = D.mor x' z (Ar.ar_le _ _ haz) ≫ D.mor z x hzx := mor_eq_comp D _ _ hnz
      rw [hμ', Category.assoc] at h
      obtain ⟨hzy, hnzy⟩ := hc.left x' z y haz hκ ⟨_, h⟩
      rw [mor_eq_comp D (Ar.ar_le _ _ haz) hzy hnzy] at h
      have h' := hL _ _ _ h (by rw [h, ← mor_eq_comp D _ _ hnzy]; exact hc.ne_zero _ _ _)
      have hd : depth (ThinCat.mor (X := (⟨z⟩ : ThinCat T)) (Y := ⟨x⟩) hzx) <
          depth (ThinCat.mor (X := (⟨x'⟩ : ThinCat T)) (Y := ⟨x⟩) hμ) := by
        have := depth_lt_comp_left (ThinCat.mor (X := (⟨x'⟩ : ThinCat T)) (Y := ⟨z⟩)
          (Ar.ar_le _ _ haz)) (ThinCat.mor (X := (⟨z⟩ : ThinCat T)) (Y := ⟨x⟩) hzx)
          (by rw [ThinCat.mor_comp _ _ hnz]; exact fun h0 ↦ by cases h0)
          (not_isIso_mor_of_ne _ (Ar.ar_ne _ _ haz))
        rwa [ThinCat.mor_comp _ _ hnz] at this
      exact ih (depth (ThinCat.mor (X := (⟨z⟩ : ThinCat T)) (Y := ⟨x⟩) hzx) +
        depth (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨y⟩) hν)) (by omega) hzx hν hzy ρ le_rfl h'
  · obtain ⟨w, hyw, haw, hnw⟩ := Ar.last y y' hν hyy
    have hν' : D.mor y y' hν = D.mor y w hyw ≫ D.mor w y' (Ar.ar_le _ _ haw) := mor_eq_comp D _ _ hnw
    rw [hν', ← Category.assoc, ← Category.assoc] at h
    obtain ⟨hxw, hnxw⟩ := hc.right x' w y' haw hκ ⟨_, h⟩
    rw [mor_eq_comp D hxw (Ar.ar_le _ _ haw) hnxw] at h
    have h' := hR _ _ _ h (by rw [h, ← mor_eq_comp D _ _ hnxw]; exact hc.ne_zero _ _ _)
    rw [Category.assoc] at h'
    have hd : depth (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨w⟩) hyw) <
        depth (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨y'⟩) hν) := by
      have := depth_lt_comp_right (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨w⟩) hyw)
        (ThinCat.mor (X := (⟨w⟩ : ThinCat T)) (Y := ⟨y'⟩) (Ar.ar_le _ _ haw))
        (by rw [ThinCat.mor_comp _ _ hnw]; exact fun h0 ↦ by cases h0)
        (not_isIso_mor_of_ne _ (Ar.ar_ne _ _ haw))
      rwa [ThinCat.mor_comp _ _ hnw] at this
    exact ih (depth (ThinCat.mor (X := (⟨x'⟩ : ThinCat T)) (Y := ⟨x⟩) hμ) +
      depth (ThinCat.mor (X := (⟨y⟩ : ThinCat T)) (Y := ⟨w⟩) hyw)) (by omega) hμ hyw hxw ρ le_rfl h'

/-- **The local cleaving criterion for thin sources.** -/
theorem isCleaving {Ar : ThinArrows T} (hc : D.Cleaves Ar) (hL : LeftCancel Q)
    (hR : RightCancel Q) : IsCleaving D.functor where
  map_eq_zero_iff {X Y} f := by
    rcases f with _ | ⟨⟨⟩, h⟩
    · exact ⟨fun _ ↦ rfl, fun _ ↦ D.functor.map_zero _ _⟩
    · exact ⟨fun h0 ↦ absurd h0 (hc.ne_zero _ _ h), fun h0 ↦ by cases h0⟩
  map_injective {X Y} f g h := by
    rcases f with _ | ⟨⟨⟩, hf⟩ <;> rcases g with _ | ⟨⟨⟩, hg⟩
    · rfl
    · exact absurd ((D.functor.map_zero _ _).symm.trans h).symm (hc.ne_zero _ _ hg)
    · exact absurd (h.trans (D.functor.map_zero _ _)) (hc.ne_zero _ _ hf)
    · rfl
  image_closed {X X' Y Y'} μ ρ ν κ h hκ := by
    rcases κ with _ | ⟨⟨⟩, hk⟩
    · exact absurd rfl hκ
    rcases μ with _ | ⟨⟨⟩, hμ⟩
    · have h0 : D.functor.map (none : ThinHom T X'.as X.as) = 0 := D.functor.map_zero X' X
      rw [h0, zero_comp] at h
      exact absurd h.symm (hc.ne_zero _ _ hk)
    rcases ν with _ | ⟨⟨⟩, hν⟩
    · have h0 : D.functor.map (none : ThinHom T Y.as Y'.as) = 0 := D.functor.map_zero Y Y'
      rw [h0, comp_zero, comp_zero] at h
      exact absurd h.symm (hc.ne_zero _ _ hk)
    exact D.image_aux hc hL hR _ hμ hν hk ρ le_rfl h

end ThinFunctorData

end RayCat

end LargeIndecomposable
