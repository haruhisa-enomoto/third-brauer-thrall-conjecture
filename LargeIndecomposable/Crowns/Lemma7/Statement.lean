module

public import LargeIndecomposable.Crowns.Lemma7.Core

/-!
# BO13a Lemma 7: a minimal crown has length at least six

* `MulBasis.lemma7`: a minimal crown does not have length four.
* `MulBasis.l7_mk4`: a crown `(f₀, f₁, f₂, f₃)` of length four with `f₁ ≠ f₃` long,
  `f₀`, `f₂` not long and either `f₂ ≤ f₁, f₀ ≤ f₃` or `f₀ ≤ f₁, f₂ ≤ f₃` is
  impossible (`l7_core`, in `Pᵒᵖ` for the second case).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

omit [HasZeroMorphisms P] in
lemma not_op_right {X X' Y : P} {f : X ⟶ Y} {g : X' ⟶ Y} (h : ¬∃ c, c ≫ f = g) :
    ¬∃ c, f.op ≫ c = g.op := by
  rintro ⟨c, hc⟩
  exact h ⟨c.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hc)⟩

omit [HasZeroMorphisms P] in
lemma not_op_left {X Y Y' : P} {f : X ⟶ Y} {g : X ⟶ Y'} (h : ¬∃ c, f ≫ c = g) :
    ¬∃ c, c ≫ f.op = g.op := by
  rintro ⟨c, hc⟩
  exact h ⟨c.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hc)⟩


omit [HasZeroMorphisms P] in
/-- The positions of two different long entries of a crown of length four. -/
lemma pos_pair {α : Type} {L : ℕ → Prop} {F : ℕ → α} (s₀ s₁ : ℕ) (h₀ : s₀ < 4) (h₁ : s₁ < 4)
    (hl₀ : L s₀) (hl₁ : L s₁) (hne : F s₁ ≠ F s₀) (a01 : L 0 → L 1 → False)
    (a12 : L 1 → L 2 → False) (a23 : L 2 → L 3 → False) (a30 : L 3 → L 0 → False) :
    (L 1 ∧ L 3 ∧ F 1 ≠ F 3) ∨ (L 0 ∧ L 2 ∧ F 0 ≠ F 2) := by
  interval_cases s₀ <;> interval_cases s₁ <;>
    first
    | exact absurd rfl hne
    | exact Or.inl ⟨hl₀, hl₁, hne.symm⟩
    | exact Or.inl ⟨hl₁, hl₀, hne⟩
    | exact Or.inr ⟨hl₀, hl₁, hne.symm⟩
    | exact Or.inr ⟨hl₁, hl₀, hne⟩
    | exact (a01 hl₀ hl₁).elim
    | exact (a01 hl₁ hl₀).elim
    | exact (a12 hl₀ hl₁).elim
    | exact (a12 hl₁ hl₀).elim
    | exact (a23 hl₀ hl₁).elim
    | exact (a23 hl₁ hl₀).elim
    | exact (a30 hl₀ hl₁).elim
    | exact (a30 hl₁ hl₀).elim

/-- Lemma 5 b) assigns the two non-long entries to the two long ones. -/
lemma assign {G : ℕ → RayMor P} {X₀ Y₀ X₂ Y₂ : P} (f₀ : X₀ ⟶ Y₀) (f₂ : X₂ ⟶ Y₂) (s s' : ℕ)
    (hs : s < 4) (hs' : s' < 4) (hls : IsLong (G s).2.2) (hls' : IsLong (G s').2.2)
    (hn0 : ¬IsLong (G 0).2.2) (hn2 : ¬IsLong (G 2).2.2)
    (hfs : FactorsThroughMorphism f₀ (G s).2.2) (hfs' : FactorsThroughMorphism f₂ (G s').2.2)
    (b0 : ¬(FactorsThroughMorphism f₀ (G 1).2.2 ∧ FactorsThroughMorphism f₂ (G 1).2.2))
    (b1 : ¬(FactorsThroughMorphism f₂ (G 3).2.2 ∧ FactorsThroughMorphism f₀ (G 3).2.2)) :
    (FactorsThroughMorphism f₂ (G 1).2.2 ∧ FactorsThroughMorphism f₀ (G 3).2.2) ∨
      (FactorsThroughMorphism f₀ (G 1).2.2 ∧ FactorsThroughMorphism f₂ (G 3).2.2) := by
  interval_cases s <;> interval_cases s' <;>
    first
    | exact absurd hls hn0
    | exact absurd hls hn2
    | exact absurd hls' hn0
    | exact absurd hls' hn2
    | exact (b0 ⟨hfs, hfs'⟩).elim
    | exact (b1 ⟨hfs', hfs⟩).elim
    | exact Or.inl ⟨hfs', hfs⟩
    | exact Or.inr ⟨hfs, hfs'⟩

/-- The same for long entries at the even positions. -/
lemma assign' {G : ℕ → RayMor P} {X₁ Y₁ X₃ Y₃ : P} (f₁ : X₁ ⟶ Y₁) (f₃ : X₃ ⟶ Y₃) (s s' : ℕ)
    (hs : s < 4) (hs' : s' < 4) (hls : IsLong (G s).2.2) (hls' : IsLong (G s').2.2)
    (hn1 : ¬IsLong (G 1).2.2) (hn3 : ¬IsLong (G 3).2.2)
    (hfs : FactorsThroughMorphism f₁ (G s).2.2) (hfs' : FactorsThroughMorphism f₃ (G s').2.2)
    (b0 : ¬(FactorsThroughMorphism f₁ (G 2).2.2 ∧ FactorsThroughMorphism f₃ (G 2).2.2))
    (b1 : ¬(FactorsThroughMorphism f₃ (G 0).2.2 ∧ FactorsThroughMorphism f₁ (G 0).2.2)) :
    (FactorsThroughMorphism f₃ (G 0).2.2 ∧ FactorsThroughMorphism f₁ (G 2).2.2) ∨
      (FactorsThroughMorphism f₁ (G 0).2.2 ∧ FactorsThroughMorphism f₃ (G 2).2.2) := by
  interval_cases s <;> interval_cases s' <;>
    first
    | exact absurd hls hn1
    | exact absurd hls hn3
    | exact absurd hls' hn1
    | exact absurd hls' hn3
    | exact (b0 ⟨hfs, hfs'⟩).elim
    | exact (b1 ⟨hfs', hfs⟩).elim
    | exact Or.inl ⟨hfs', hfs⟩
    | exact Or.inr ⟨hfs, hfs'⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 7** for a crown `(f₀, f₁, f₂, f₃)` of length four with long `f₁`, `f₃`. -/
theorem l7_mk4
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {a₀ a₁ b₀ b₁ : P} (f₀ : a₀ ⟶ b₀) (f₁ : a₁ ⟶ b₀) (f₂ : a₁ ⟶ b₁) (f₃ : a₀ ⟶ b₁)
    (p1 : ¬∃ c, c ≫ f₁ = f₀) (p2 : ¬∃ c, c ≫ f₀ = f₁) (v1 : ¬∃ c, f₁ ≫ c = f₂)
    (v2 : ¬∃ c, f₂ ≫ c = f₁) (p3 : ¬∃ c, c ≫ f₃ = f₂) (p4 : ¬∃ c, c ≫ f₂ = f₃)
    (v3 : ¬∃ c, f₃ ≫ c = f₀) (v4 : ¬∃ c, f₀ ≫ c = f₃) (h0 : f₀ ≠ 0) (h2 : f₂ ≠ 0)
    (hl1 : IsLong f₁) (hl3 : IsLong f₃) (hn0 : ¬IsLong f₀) (hn2 : ¬IsLong f₂)
    (hne : (⟨a₁, b₀, f₁⟩ : RayMor P) ≠ ⟨a₀, b₁, f₃⟩)
    (hle : (FactorsThroughMorphism f₂ f₁ ∧ FactorsThroughMorphism f₀ f₃) ∨
      (FactorsThroughMorphism f₀ f₁ ∧ FactorsThroughMorphism f₂ f₃))
    (hD44 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F73.thin) k)) : False := by
  rcases hle with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact B.l7_core hmin hL hR hQ hcont hl1 hl3 h2 h0 hn2 hn0 v1 v2 p3 p4 v3 v4 p1 p2 k1 k2 hne
      hD44
  · let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
    let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
    let _ : DecidableEq Pᵒᵖ := Classical.decEq _
    have _ : FiniteDimensional k A := B.finiteDimensional
    refine (B.op).l7_core (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
      (oneSidedCyclic_op hQ) (hcont_op hcont) (σ₁ := f₁.op) (ρ₁ := f₀.op) (σ₂ := f₃.op)
      (ρ₂ := f₂.op) ((isLong_op_iff _).2 hl1) ((isLong_op_iff _).2 hl3)
      (fun h ↦ h0 (by rw [← Quiver.Hom.unop_op f₀, h]; rfl))
      (fun h ↦ h2 (by rw [← Quiver.Hom.unop_op f₂, h]; rfl))
      (fun h ↦ hn0 ((isLong_op_iff _).1 h)) (fun h ↦ hn2 ((isLong_op_iff _).1 h))
      (not_op_right p1) (not_op_right p2) (not_op_left v3) (not_op_left v4) (not_op_right p3)
      (not_op_right p4) (not_op_left v1) (not_op_left v2) ((ftm_op_iff _ _).2 k1)
      ((ftm_op_iff _ _).2 k2) (fun h ↦ hne (by have := congrArg unopRM h; exact this)) hD44

include B in
/-- **BO13a Lemma 7**: a minimal crown does not have length four. -/
theorem lemma7
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k)
    (hD44 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F73.thin) k))
    {a b : P} (μ : a ⟶ b) (hμ : IsLong μ) : C.n ≠ 2 := by
  intro hn
  have hper : ∀ t, C.f t = C.f (t % 4) := fun t ↦ by rw [C.f_mod t, hn]
  have adj : ∀ t, IsLong (C.f t).2.2 → IsLong (C.f (t + 1)).2.2 → False :=
    fun t ↦ B.lemma6 hmin hL hR hQ hcont C hC hS t
  have e4 : C.f 4 = C.f 0 := hper 4
  have e5 : C.f 5 = C.f 1 := hper 5
  obtain ⟨t₀, ht₀⟩ := B.long_entry hmin C μ hμ
  have hl₀ : IsLong (C.f t₀).2.2 := by rw [ht₀]; exact hμ
  obtain ⟨t₁, hl₁, hne⟩ := B.lemma5c hmin hL hR hQ hcont C t₀ hl₀
  have hl₀' : IsLong (C.f (t₀ % 4)).2.2 := by rw [← hper]; exact hl₀
  have hl₁' : IsLong (C.f (t₁ % 4)).2.2 := by rw [← hper]; exact hl₁
  have hne' : C.f (t₁ % 4) ≠ C.f (t₀ % 4) := by rw [← hper, ← hper]; exact hne
  have a30 : IsLong (C.f 3).2.2 → IsLong (C.f 0).2.2 → False := fun h3 h0 ↦
    adj 3 h3 (by rw [e4]; exact h0)
  have a01 := adj 0
  have a12 := adj 1
  have a23 := adj 2
  have key : (IsLong (C.f 1).2.2 ∧ IsLong (C.f 3).2.2 ∧ C.f 1 ≠ C.f 3) ∨
      (IsLong (C.f 0).2.2 ∧ IsLong (C.f 2).2.2 ∧ C.f 0 ≠ C.f 2) :=
    pos_pair (L := fun t ↦ IsLong (C.f t).2.2) (F := C.f) _ _ (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) hl₀' hl₁' hne' a01 a12 a23 a30
  -- every reducible nonzero non-invertible morphism lies below a long entry
  have up : ∀ {X Y : P} (f : X ⟶ Y), f ≠ 0 → ¬IsIso f → ¬IsIrreducible f →
      ∃ s, s < 4 ∧ IsLong (C.f s).2.2 ∧ FactorsThroughMorphism f (C.f s).2.2 := by
    intro X Y f hf0 hfi hfr
    obtain ⟨_, _, μ', hμ', hfμ⟩ := exists_isLong_above hf0 hfi hfr
    obtain ⟨s, hs⟩ := B.long_entry hmin C μ' hμ'
    have hs' : C.f (s % 4) = ⟨_, _, μ'⟩ := by rw [← hper]; exact hs
    exact ⟨s % 4, Nat.mod_lt _ (by norm_num), by rw [hs']; exact hμ',
      ftm_of_rayMor_eq hs'.symm hfμ⟩
  have hP0 : Peak (C.f 0) (C.f 1) := C.peak 0
  have hV0 : Valley (C.f 1) (C.f 2) := C.valley 0
  have hP1 : Peak (C.f 2) (C.f 3) := C.peak 1
  have hV1 : Valley (C.f 3) (C.f 0) := by have := C.valley 1; rwa [e4] at this
  have h0 := C.ne 0
  have h1 := C.ne 1
  have h2 := C.ne 2
  have h3 := C.ne 3
  rcases key with ⟨hL1, hL3, hne13⟩ | ⟨hL0, hL2, hne02⟩
  · have hn0 : ¬IsLong (C.f 0).2.2 := fun h ↦ a01 h hL1
    have hn2 : ¬IsLong (C.f 2).2.2 := fun h ↦ a12 hL1 h
    have hσ0 : IsLong (C.toZChain.σ 0) := isLong_of_rayMor_eq (C.toZChain_σ 0).symm hL1
    obtain ⟨hr1, hr0⟩ := B.σ_nbr_red hmin hL hR hQ hcont C 0 hσ0
    have b0 := C.toZChain.not_le_both_σ hQ 0
    have b1 := C.toZChain.not_le_both_σ hQ 1
    have t0 : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism f (C.f 1).2.2 →
        FactorsThroughMorphism f (C.toZChain.σ 0) := fun h ↦
      ftm_of_rayMor_eq (C.toZChain_σ 0).symm h
    have t1 : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism f (C.f 3).2.2 →
        FactorsThroughMorphism f (C.toZChain.σ 1) := fun h ↦
      ftm_of_rayMor_eq (C.toZChain_σ 1).symm h
    obtain ⟨s, hs, hls, hfs⟩ := up (C.f 0).2.2 h0 (C.toZChain.ρ_not_isIso 0) hr0
    obtain ⟨s', hs', hls', hfs'⟩ := up (C.f 2).2.2 h2 (C.toZChain.ρ_not_isIso 1) hr1
    have hle := assign (G := C.f) (C.f 0).2.2 (C.f 2).2.2 s s' hs hs' hls hls' hn0 hn2 hfs hfs'
      (fun h ↦ b0 ⟨t0 h.1, t0 h.2⟩)
      (fun h ↦ b1 ⟨t1 h.1, by change FactorsThroughMorphism (C.f 4).2.2 _; rw [e4]; exact t1 h.2⟩)
    clear b0 b1 t0 t1 hσ0 hr0 hr1 up hfs hfs' hls hls'
    generalize C.f 0 = F0 at hP0 hV1 h0 hn0 hle
    generalize C.f 1 = F1 at hP0 hV0 h1 hL1 hne13 hle
    generalize C.f 2 = F2 at hV0 hP1 h2 hn2 hle
    generalize C.f 3 = F3 at hP1 hV1 h3 hL3 hne13 hle
    obtain ⟨a₀, b₀, f₀⟩ := F0
    obtain ⟨a₁, b₁, f₁⟩ := F1
    obtain ⟨a₂, b₂, f₂⟩ := F2
    obtain ⟨a₃, b₃, f₃⟩ := F3
    obtain ⟨hb, p1, p2⟩ := hP0
    obtain ⟨ha, v1, v2⟩ := hV0
    obtain ⟨hb', p3, p4⟩ := hP1
    obtain ⟨ha', v3, v4⟩ := hV1
    simp only at hb ha hb' ha'
    subst hb ha hb' ha'
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at p1 p2 v1 v2 p3 p4 v3 v4
    exact B.l7_mk4 hmin hL hR hQ hcont f₀ f₁ f₂ f₃ p1 p2 v1 v2 p3 p4 v3 v4 h0 h2 hL1 hL3 hn0 hn2
      hne13 hle hD44
  · have hn1 : ¬IsLong (C.f 1).2.2 := fun h ↦ a01 hL0 h
    have hn3 : ¬IsLong (C.f 3).2.2 := fun h ↦ a23 hL2 h
    obtain ⟨hr0, hr1⟩ := B.ρ_nbr_red hmin hL hR hQ hcont C 0 hL2
    have b0 := C.toZChain.not_le_both_ρ hQ 0
    have b1 := C.toZChain.not_le_both_ρ hQ 1
    have t0 : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism (C.f 1).2.2 f →
        FactorsThroughMorphism (C.toZChain.σ 0) f := fun h ↦ by
      have e := C.toZChain_σ 0
      generalize C.f 1 = F at h e
      subst e
      exact h
    have t1 : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism (C.f 3).2.2 f →
        FactorsThroughMorphism (C.toZChain.σ 1) f := fun h ↦ by
      have e := C.toZChain_σ 1
      generalize C.f 3 = F at h e
      subst e
      exact h
    have t2 : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism (C.f 1).2.2 f →
        FactorsThroughMorphism (C.toZChain.σ 2) f := fun h ↦ by
      have e := (C.toZChain_σ 2).trans e5
      generalize C.f 1 = F at h e
      subst e
      exact h
    have iσ1 : ¬IsIso (C.f 1).2.2 := fun hi ↦ C.toZChain.σ_not_isIso 0 (by
      have e := C.toZChain_σ 0
      generalize C.f 1 = F at hi e
      subst e
      exact hi)
    have iσ3 : ¬IsIso (C.f 3).2.2 := fun hi ↦ C.toZChain.σ_not_isIso 1 (by
      have e := C.toZChain_σ 1
      generalize C.f 3 = F at hi e
      subst e
      exact hi)
    have rσ1 : ¬IsIrreducible (C.f 1).2.2 := fun hi ↦ hr0 (by
      have e := C.toZChain_σ 0
      generalize C.f 1 = F at hi e
      subst e
      exact hi)
    have rσ3 : ¬IsIrreducible (C.f 3).2.2 := fun hi ↦ hr1 (by
      have e := C.toZChain_σ 1
      generalize C.f 3 = F at hi e
      subst e
      exact hi)
    obtain ⟨s, hs, hls, hfs⟩ := up (C.f 1).2.2 h1 iσ1 rσ1
    obtain ⟨s', hs', hls', hfs'⟩ := up (C.f 3).2.2 h3 iσ3 rσ3
    have hle := assign' (G := C.f) (C.f 1).2.2 (C.f 3).2.2 s s' hs hs' hls hls' hn1 hn3 hfs hfs'
      (fun h ↦ b0 ⟨t0 h.1, t1 h.2⟩)
      (fun h ↦ b1 ⟨t1 (by change FactorsThroughMorphism _ (C.f 4).2.2; rw [e4]; exact h.1),
        t2 (by change FactorsThroughMorphism _ (C.f 4).2.2; rw [e4]; exact h.2)⟩)
    clear b0 b1 t0 t1 t2 hr0 hr1 up hfs hfs' hls hls' iσ1 iσ3 rσ1 rσ3
    generalize C.f 0 = F0 at hP0 hV1 h0 hL0 hne02 hle
    generalize C.f 1 = F1 at hP0 hV0 h1 hn1 hle
    generalize C.f 2 = F2 at hV0 hP1 h2 hL2 hne02 hle
    generalize C.f 3 = F3 at hP1 hV1 h3 hn3 hle
    obtain ⟨a₀, b₀, f₀⟩ := F0
    obtain ⟨a₁, b₁, f₁⟩ := F1
    obtain ⟨a₂, b₂, f₂⟩ := F2
    obtain ⟨a₃, b₃, f₃⟩ := F3
    obtain ⟨hb, p1, p2⟩ := hP0
    obtain ⟨ha, v1, v2⟩ := hV0
    obtain ⟨hb', p3, p4⟩ := hP1
    obtain ⟨ha', v3, v4⟩ := hV1
    simp only at hb ha hb' ha'
    subst hb ha hb' ha'
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at p1 p2 v1 v2 p3 p4 v3 v4
    exact B.l7_mk4 hmin hL hR hQ hcont f₁ f₀ f₃ f₂ p2 p1 v4 v3 p4 p3 v2 v1 h1 h3 hL0 hL2 hn1 hn3
      hne02 hle hD44

end MulBasis

end RayQuiver

end LargeIndecomposable
