module

public import LargeIndecomposable.Crowns.Basic.CrownBand
public import LargeIndecomposable.RayCategories.Basic.Factor

/-!
# Closed chains give cleaving functors from the crown category

A closed chain of a ray category `Q` is a cyclic zigzag
`x₀ -ρ₀→ z₀ ←σ₀- x₁ -ρ₁→ z₁ ← ⋯ ←σₘ- x₀` of nonzero morphisms whose peaks
`(ρᵢ, σᵢ)` and valleys `(σᵢ, ρᵢ₊₁)` do not close to commutative triangles. It
defines a functor from the crown category `Cr m` (`RayCat.ClosedChain.functor`)
which is cleaving and along which every twisted multiplicative basis is
untwisted. With the band modules of `Cr m` and the cleaving lemma, an algebra
with a twisted multiplicative basis over `Q` is representation-infinite
(`RayCat.ClosedChain.not_isRepresentationFinite`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q]

/-- A closed chain with `m + 1` peaks. -/
structure ClosedChain (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] (m : ℕ) where
  x : Fin (m + 1) → Q
  z : Fin (m + 1) → Q
  ρ : ∀ i, x i ⟶ z i
  σ : ∀ i, x (i + 1) ⟶ z i
  ρ_ne : ∀ i, ρ i ≠ 0
  σ_ne : ∀ i, σ i ≠ 0
  peak₁ : ∀ i, ¬∃ c, c ≫ σ i = ρ i
  peak₂ : ∀ i, ¬∃ c, c ≫ ρ i = σ i
  valley₁ : ∀ i, ¬∃ c, σ i ≫ c = ρ (i + 1)
  valley₂ : ∀ i, ¬∃ c, ρ (i + 1) ≫ c = σ i

namespace ClosedChain

variable {m : ℕ} (C : ClosedChain Q m)

/-- The vertices. -/
def obj : Fin (m + 1) ⊕ Fin (m + 1) → Q := Sum.elim C.x C.z

/-- The arrows. -/
def arrMor : ∀ e, C.obj (crSrc m e) ⟶ C.obj (crTgt m e)
  | .inl i => C.ρ i
  | .inr i => C.σ i

lemma arrMor_ne (e) : C.arrMor e ≠ 0 := by
  rcases e with i | i
  · exact C.ρ_ne i
  · exact C.σ_ne i

/-- The functor `Cr m ⥤ Q`. -/
abbrev functor : Cr m ⥤ Q where
  obj X := C.obj X.as
  map {X Y} f := match f with
    | none => 0
    | some (.inl ⟨_, h⟩) => eqToHom (congrArg C.obj h)
    | some (.inr ⟨e, hs, ht⟩) =>
      eqToHom (congrArg C.obj hs).symm ≫ C.arrMor e ≫ eqToHom (congrArg C.obj ht)
  map_id X := rfl
  map_comp {X Y Z} f g := by
    rw [RSZ.comp_def]
    rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩ <;> rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
    all_goals simp [RHom.comp]
    exact absurd (ht.trans hs'.symm) (crTgt_ne_crSrc m e e')

instance : C.functor.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-! ### Cleaving -/

section Cleaving

variable [IsRayCategory Q]

/-- Two different arrows into the same sink form a peak. -/
lemma not_factor_tgt {e e' : Fin (m + 1) ⊕ Fin (m + 1)} (hne : e ≠ e')
    (ht : crTgt m e' = crTgt m e) (c : C.obj (crSrc m e') ⟶ C.obj (crSrc m e)) :
    c ≫ C.arrMor e ≠ C.arrMor e' ≫ eqToHom (congrArg C.obj ht) := by
  rcases e with i | i <;> rcases e' with j | j
  · obtain rfl : j = i := Sum.inr.inj ht
    exact absurd rfl hne
  · obtain rfl : j = i := Sum.inr.inj ht
    intro h
    exact C.peak₂ j ⟨c, h.trans (by erw [eqToHom_refl, Category.comp_id]; rfl)⟩
  · obtain rfl : j = i := Sum.inr.inj ht
    intro h
    exact C.peak₁ j ⟨c, h.trans (by erw [eqToHom_refl, Category.comp_id]; rfl)⟩
  · obtain rfl : j = i := Sum.inr.inj ht
    exact absurd rfl hne

/-- Two different arrows out of the same source form a valley. -/
lemma not_factor_src {e e' : Fin (m + 1) ⊕ Fin (m + 1)} (hne : e ≠ e')
    (hs : crSrc m e' = crSrc m e) (c : C.obj (crTgt m e) ⟶ C.obj (crTgt m e')) :
    C.arrMor e ≫ c ≠ eqToHom (congrArg C.obj hs.symm) ≫ C.arrMor e' := by
  rcases e with i | i <;> rcases e' with j | j
  · obtain rfl : j = i := Sum.inl.inj hs
    exact absurd rfl hne
  · obtain rfl : j + 1 = i := Sum.inl.inj hs
    intro h
    exact C.valley₂ j ⟨c, h.trans (by erw [eqToHom_refl, Category.id_comp]; rfl)⟩
  · obtain rfl : j = i + 1 := Sum.inl.inj hs
    intro h
    exact C.valley₁ i ⟨c, h.trans (by erw [eqToHom_refl, Category.id_comp]; rfl)⟩
  · obtain rfl : j = i := add_right_cancel (Sum.inl.inj hs)
    exact absurd rfl hne

/-- An arrow of the chain is not invertible. -/
lemma not_isIso_arrMor (e) : ¬IsIso (C.arrMor e) := by
  intro hI
  obtain ⟨h, he⟩ := RayQuiver.eq_id_of_isIso (C.arrMor e)
  rcases e with i | i
  · change C.x i = C.z i at h
    change C.ρ i = eqToHom h at he
    exact C.peak₂ i ⟨C.σ i ≫ eqToHom h.symm, by rw [he]; simp⟩
  · change C.x (i + 1) = C.z i at h
    change C.σ i = eqToHom h at he
    exact C.peak₁ i ⟨C.ρ i ≫ eqToHom h.symm, by rw [he]; simp⟩

lemma arrMor_not_splitMono (e) (r : C.obj (crTgt m e) ⟶ C.obj (crSrc m e)) :
    C.arrMor e ≫ r ≠ 𝟙 _ := by
  intro h
  have h2 : r ≫ C.arrMor e = 𝟙 _ := by
    have := (IsRayCategory.eq_id_of_two_sided (C.arrMor e) (C.arrMor_ne e) (𝟙 _) (r ≫ C.arrMor e)
      (by rw [Category.id_comp, ← Category.assoc, h, Category.id_comp])).2
    exact this
  exact C.not_isIso_arrMor e ⟨r, h, h2⟩

lemma arrMor_not_splitEpi (e) (r : C.obj (crTgt m e) ⟶ C.obj (crSrc m e)) :
    r ≫ C.arrMor e ≠ 𝟙 _ := by
  intro h
  have h2 : C.arrMor e ≫ r = 𝟙 _ := by
    have := (IsRayCategory.eq_id_of_two_sided (C.arrMor e) (C.arrMor_ne e) (C.arrMor e ≫ r) (𝟙 _)
      (by rw [Category.comp_id, Category.assoc, h, Category.comp_id])).1
    exact this
  exact C.not_isIso_arrMor e ⟨r, h2, h⟩

lemma functor_map_inr {e : Fin (m + 1) ⊕ Fin (m + 1)} :
    C.functor.map (X := ⟨crSrc m e⟩) (Y := ⟨crTgt m e⟩) (some (.inr ⟨e, rfl, rfl⟩)) = C.arrMor e := by
  simp [functor]

lemma functor_map_id' {a : Fin (m + 1) ⊕ Fin (m + 1)} :
    C.functor.map (X := ⟨a⟩) (Y := ⟨a⟩) (some (.inl ⟨(), rfl⟩)) = 𝟙 _ := rfl

lemma functor_map_eq_zero_iff {X Y : Cr m} (f : X ⟶ Y) : C.functor.map f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  obtain ⟨a⟩ := X
  obtain ⟨b⟩ := Y
  rcases f with _ | ⟨⟨_, hab⟩ | ⟨e, hs, ht⟩⟩
  · rfl
  · change a = b at hab
    subst hab
    exact absurd h (IsRayCategory.id_ne_zero _)
  · change crSrc m e = a at hs
    change crTgt m e = b at ht
    subst hs ht
    rw [functor_map_inr] at h
    exact absurd h (C.arrMor_ne e)

lemma functor_map_inr' {a b : Fin (m + 1) ⊕ Fin (m + 1)} (e) (hs : crSrc m e = a)
    (ht : crTgt m e = b) :
    C.functor.map (X := ⟨a⟩) (Y := ⟨b⟩) (some (.inr ⟨e, hs, ht⟩)) =
      eqToHom (congrArg C.obj hs).symm ≫ C.arrMor e ≫ eqToHom (congrArg C.obj ht) := rfl

@[simp] lemma functor_map_inl {a b : Fin (m + 1) ⊕ Fin (m + 1)} (u : Unit) (h : a = b) :
    C.functor.map (X := ⟨a⟩) (Y := ⟨b⟩) (some (.inl ⟨u, h⟩)) = eqToHom (congrArg C.obj h) := rfl

/-- The functor of a closed chain is cleaving. -/
theorem isCleaving [Fintype Q] [DecidableEq Q] : IsCleaving C.functor where
  map_eq_zero_iff := C.functor_map_eq_zero_iff
  map_injective := by
    rintro ⟨a⟩ ⟨b⟩ f g h
    rcases f with _ | ⟨⟨_, hab⟩ | ⟨e, hs, ht⟩⟩
    · exact ((C.functor_map_eq_zero_iff g).1 h.symm).symm
    · change a = b at hab
      subst hab
      rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
      · exact absurd h (IsRayCategory.id_ne_zero _)
      · rfl
      · change crSrc m e' = a at hs'
        change crTgt m e' = a at ht'
        exact absurd (ht'.trans hs'.symm) (crTgt_ne_crSrc m e' e')
    · change crSrc m e = a at hs
      change crTgt m e = b at ht
      subst hs ht
      rw [functor_map_inr] at h
      rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
      · exact absurd h (C.arrMor_ne e)
      · exact absurd (h' : crSrc m e = crTgt m e).symm (crTgt_ne_crSrc m e e)
      · change crSrc m e' = crSrc m e at hs'
        change crTgt m e' = crTgt m e at ht'
        by_cases he : e = e'
        · subst he; rfl
        · rw [functor_map_inr' C e' hs' ht'] at h
          exact absurd (by rw [h]; simp) (C.not_factor_tgt he ht' (eqToHom (congrArg C.obj hs')))
  image_closed := by
    rintro ⟨x⟩ ⟨x'⟩ ⟨y⟩ ⟨y'⟩ μ ρ ν κ h hκ
    change C.obj x ⟶ C.obj y at ρ
    have hFκ : C.functor.map κ ≠ 0 := fun h0 ↦ hκ ((C.functor_map_eq_zero_iff κ).1 h0)
    rcases μ with _ | ⟨⟨_, hμ⟩ | ⟨e, hs, ht⟩⟩
    · exact absurd (h.symm.trans (zero_comp)) hFκ
    · change x' = x at hμ
      subst hμ
      rcases ν with _ | ⟨⟨_, hν⟩ | ⟨e'', hs'', ht''⟩⟩
      · exact absurd (h.symm.trans (by rw [show C.functor.map (none : RHom _ _ y y') = 0 from rfl, comp_zero, comp_zero])) hFκ
      · change y = y' at hν
        subst hν
        exact ⟨κ, by simpa using h⟩
      · change crSrc m e'' = y at hs''
        change crTgt m e'' = y' at ht''
        subst hs'' ht''
        rw [functor_map_inr] at h
        rcases κ with _ | ⟨⟨_, hκ'⟩ | ⟨e', hs', ht'⟩⟩
        · exact absurd rfl hκ
        · change x' = crTgt m e'' at hκ'
          subst hκ'
          exact absurd (by simpa using h) (C.arrMor_not_splitEpi e'' ρ)
        · change crSrc m e' = x' at hs'
          change crTgt m e' = crTgt m e'' at ht'
          subst hs'
          rw [functor_map_inr' C e' rfl ht'] at h
          by_cases he : e'' = e'
          · subst he
            have := (IsRayCategory.eq_id_of_two_sided (C.arrMor e'') (C.arrMor_ne e'') ρ (𝟙 _)
              (by simpa using h.symm)).1
            subst this
            exact ⟨𝟙 _, rfl⟩
          · exact absurd (by simpa using h) (C.not_factor_tgt he ht' ρ)
    · change crSrc m e = x' at hs
      change crTgt m e = x at ht
      subst hs ht
      rw [functor_map_inr] at h
      rcases ν with _ | ⟨⟨_, hν⟩ | ⟨e'', hs'', ht''⟩⟩
      · exact absurd (h.symm.trans (by rw [show C.functor.map (none : RHom _ _ y y') = 0 from rfl, comp_zero, comp_zero])) hFκ
      · change y = y' at hν
        subst hν
        rcases κ with _ | ⟨⟨_, hκ'⟩ | ⟨e', hs', ht'⟩⟩
        · exact absurd rfl hκ
        · change crSrc m e = y at hκ'
          subst hκ'
          exact absurd (by simpa using h) (C.arrMor_not_splitMono e ρ)
        · change crSrc m e' = crSrc m e at hs'
          change crTgt m e' = y at ht'
          subst ht'
          rw [functor_map_inr' C e' hs' rfl] at h
          by_cases he : e = e'
          · subst he
            have := (IsRayCategory.eq_id_of_two_sided (C.arrMor e) (C.arrMor_ne e) (𝟙 _) ρ
              (by simpa using h.symm)).2
            subst this
            exact ⟨𝟙 _, rfl⟩
          · exact absurd (by simpa using h) (C.not_factor_src he hs' ρ)
      · change crSrc m e'' = y at hs''
        change crTgt m e'' = y' at ht''
        subst hs'' ht''
        rw [functor_map_inr] at h
        rcases κ with _ | ⟨⟨_, hκ'⟩ | ⟨e', hs', ht'⟩⟩
        · exact absurd rfl hκ
        · exact absurd (hκ' : crSrc m e = crTgt m e'').symm (crTgt_ne_crSrc m e'' e)
        · change crSrc m e' = crSrc m e at hs'
          change crTgt m e' = crTgt m e'' at ht'
          rw [functor_map_inr' C e' hs' ht'] at h
          by_cases he : e'' = e'
          · subst he
            have h1 := (IsRayCategory.eq_id_of_two_sided (C.arrMor e'') (C.arrMor_ne e'')
              (eqToHom (congrArg C.obj hs') ≫ C.arrMor e ≫ ρ) (𝟙 _) (by
                simp only [Category.comp_id, Category.assoc]; rw [h]; simp)).1
            exact absurd (by
              rw [← Category.assoc]
              calc _ = eqToHom (congrArg C.obj hs').symm ≫
                  (eqToHom (congrArg C.obj hs') ≫ C.arrMor e ≫ ρ) ≫ eqToHom (congrArg C.obj hs') := by
                    simp
                _ = 𝟙 _ := by rw [h1]; simp) (C.arrMor_not_splitMono e (ρ ≫ eqToHom (congrArg C.obj hs')))
          · exact absurd (by
              simp only [Category.assoc]; rw [h]; simp)
              (C.not_factor_tgt he ht' (eqToHom (congrArg C.obj hs') ≫ C.arrMor e ≫ ρ))

end Cleaving

/-! ### Closed chains make algebras representation-infinite -/

section RepInf

variable [IsRayCategory Q] [Fintype Q] [DecidableEq Q] {k : Type u} [Field k] {A : Type u} [Ring A]
  [Algebra k A]

include C in
/-- Every twisted multiplicative basis is untwisted along the functor of a
closed chain: nonzero composites in `Cr m` involve an identity. -/
lemma untwisted (B : MulBasis k Q A) : B.Untwisted C.functor := by
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ f g hfg
  rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩
  · exact absurd rfl hfg
  · change a = b at h
    subst h
    rw [functor_map_inl, eqToHom_refl]
    exact B.tw_id_left _
  · rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
    · exact absurd rfl hfg
    · change b = c at h'
      subst h'
      rw [functor_map_inl, eqToHom_refl]
      exact B.tw_id_right _
    · exact absurd ((ht : crTgt m e = b).trans (hs' : crSrc m e' = b).symm) (crTgt_ne_crSrc m e e')

include C in
/-- **A closed chain makes an algebra with a twisted multiplicative basis
representation-infinite** (Gabriel–Roiter 13.8 with the band modules of the
crown). -/
theorem not_isRepresentationFinite [Infinite k] (B : MulBasis k Q A) :
    ¬Statement.IsRepresentationFinite A := fun h ↦
  not_isRepresentationFinite_crown k m
    (isRepresentationFinite_of_cleaving (B := B) (F := C.functor) C.isCleaving (C.untwisted B) h)

end RepInf

end ClosedChain

end RayCat

end LargeIndecomposable
