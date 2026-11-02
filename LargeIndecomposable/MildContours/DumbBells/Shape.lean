module

public import LargeIndecomposable.MildContours.Contours.Theorem3
public import LargeIndecomposable.MildContours.Diamonds.CaseA
public import LargeIndecomposable.RayCategories.Distributive.OneSided
public import LargeIndecomposable.RayCategories.Basic.MorphismDepth
public import LargeIndecomposable.Cleaving.Shapes.ShapeDB23A
public import LargeIndecomposable.Cleaving.Shapes.ShapeDB23B

/-!
# Dumb-bells: the shape of the contour ([mild] PDB)

Case (DB) of [mild] Lemma 2.2: `v = q β α`, `w = w' β`, `α` the loop at `y`.
`suffix`: `w' = χ q` for a cycle `χ` at `x` (comparability with ray axiom e),
`OneSidedCyclic`; [mild] PDB, first paragraph).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Two paths with a common nonempty prefix and the same nonzero value are interlaced. -/
lemma interlaced_prefix (hL : LeftCancel P) {x a y : RayVert P} (p : Quiver.Path x a)
    (v₁ w₁ : Quiver.Path a y) (hp : 0 < p.length) (hval : pathVal (p.comp v₁) = pathVal (p.comp w₁))
    (h0 : pathVal (p.comp v₁) ≠ 0) : Interlaced (p.comp v₁) (p.comp w₁) := by
  rw [pathVal_comp, pathVal_comp] at hval
  rw [pathVal_comp] at h0
  have hv : pathVal v₁ = pathVal w₁ := hL _ _ _ hval h0
  exact interlaced_step p v₁ w₁ .nil hv (fun h ↦ h0 (by rw [h, comp_zero])) (Or.inl hp)

/-- A path for every nonzero endomorphism. -/
lemma exists_path_endo {z : RayVert P} (b : z.out ⟶ z.out) (hb : b ≠ 0) :
    ∃ p : Quiver.Path z z, pathVal p = b := exists_path b hb

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace DBData

variable {x y : RayVert P} (D : DBData x y)

/-- The underlying mild contour. -/
def C : MildContour x.out y.out :=
  ⟨y, D.t, D.q.cons D.β, D.α, D.w', D.β, D.hval, D.h0, D.hni, D.α.1, D.hρ, D.hωρ⟩

/-- **[mild] PDB, first step**: `w' = χ q` for a cycle `χ` at `x`. -/
theorem suffix (hM : MildHyp k P) (hOS : OneSidedCyclic P) :
    ∃ χ : Quiver.Path x x, D.w' = χ.comp D.q := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := D.C.apart hR
  have hw'pos := D.C.w'_pos hR
  obtain ⟨α, t, w', β, q, hval, h0, hni, hρ, hωρ⟩ := D
  change ArrowsApart α β at hap
  change 0 < w'.length at hw'pos
  dsimp only
  have hα := α.2.2.1
  have hvω : pathVal ((q.cons β).cons α) = pathVal q ≫ β.1 ≫ α.1 := by
    simp [pathVal]
  have hwω : pathVal (w'.cons β) = pathVal w' ≫ β.1 := rfl
  have hQ : pathVal q ≠ 0 := fun h ↦ h0 (by rw [hvω, h, zero_comp])
  have hW : pathVal w' ≠ 0 := fun h ↦ h0 (by rw [hval, hwω, h, zero_comp])
  have uniq := fun (u : Quiver.Path x y) (hu : pathVal u = pathVal ((q.cons β).cons α)) ↦
    hM.path_unique hval h0 hni hα hωρ u hu
  -- `ω = a ≫ ω ≫ α` is impossible
  have absorb : ∀ a : x.out ⟶ x.out, pathVal ((q.cons β).cons α) =
      a ≫ pathVal ((q.cons β).cons α) ≫ α.1 → False := fun a h ↦
    hα (by rw [(IsRayCategory.eq_id_of_two_sided _ h0 a α.1 h).2]; infer_instance)
  have hβα : ArrowsApart β α := ⟨hap.2, hap.1⟩
  have hnotv : ∀ (X : Quiver.Path x t), X.cons β ≠ (q.cons β).cons α :=
    fun X ↦ cons_ne_of_apart X β (q.cons β) α hβα
  rcases IsFiniteRayCategory.factorization_comparable (pathVal q) (pathVal w') with hT | hT
  · -- `w'` lies in the bimodule of `q`
    obtain ⟨b, hb⟩ | ⟨a, ha⟩ : (∃ b, pathVal w' = pathVal q ≫ b) ∨ ∃ a, pathVal w' = a ≫ pathVal q := by
      rcases hOS x.out t.out with h | h
      · exact Or.inl (h _ _ hW hT)
      · exact Or.inr (h _ _ hW hT)
    · by_cases hbi : IsIso b
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso b
        exact (absorb (𝟙 _) (by conv_rhs => rw [hval, hwω, hb]
                                simp [hvω])).elim
      have hb0 : b ≠ 0 := fun h ↦ hW (by rw [hb, h, comp_zero])
      obtain ⟨pb, hpb⟩ := exists_path_endo (z := t) b hb0
      rcases uniq ((q.comp pb).cons β) (by
          rw [hval]; change pathVal (q.comp pb) ≫ β.1 = _; rw [pathVal_comp, hpb, ← hb]; rfl)
        with h | h
      · exact (hnotv _ h).elim
      · have hw : w' = q.comp pb := (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)).symm
        subst hw
        cases q with
        | nil => exact ⟨pb, by simp⟩
        | cons q' e =>
          exfalso
          apply hni
          have := interlaced_prefix hL (q'.cons e) ((Quiver.Path.nil.cons β).cons α) (pb.cons β)
            (by simp) hval h0
          exact this
    · by_cases hai : IsIso a
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso a
        exact (absorb (𝟙 _) (by conv_rhs => rw [hval, hwω, ha]
                                simp [hvω])).elim
      have ha0 : a ≠ 0 := fun h ↦ hW (by rw [ha, h, zero_comp])
      obtain ⟨pa, hpa⟩ := exists_path_endo (z := x) a ha0
      rcases uniq ((pa.comp q).cons β) (by
          rw [hval]; change pathVal (pa.comp q) ≫ β.1 = _; rw [pathVal_comp, hpa, ← ha]; rfl)
        with h | h
      · exact (hnotv _ h).elim
      · exact ⟨pa, (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)).symm⟩
  · -- `q` lies in the bimodule of `w'`
    obtain ⟨b, hb⟩ | ⟨a, ha⟩ : (∃ b, pathVal q = pathVal w' ≫ b) ∨ ∃ a, pathVal q = a ≫ pathVal w' := by
      rcases hOS x.out t.out with h | h
      · exact Or.inl (h _ _ hQ hT)
      · exact Or.inr (h _ _ hQ hT)
    · by_cases hbi : IsIso b
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso b
        exact (absorb (𝟙 _) (by conv_lhs => rw [hvω, hb]
                                rw [hval, hwω]; simp)).elim
      have hb0 : b ≠ 0 := fun h ↦ hQ (by rw [hb, h, comp_zero])
      obtain ⟨pb, hpb⟩ := exists_path_endo (z := t) b hb0
      rcases uniq (((w'.comp pb).cons β).cons α) (by
          change (pathVal (w'.comp pb) ≫ β.1) ≫ α.1 = _; rw [pathVal_comp, hpb, hvω, hb]; simp)
        with h | h
      · exfalso
        have hq : q = w'.comp pb :=
          (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons (eq_of_heq
            (Quiver.Path.heq_of_cons_eq_cons h)))).symm
        subst hq
        apply hni
        have := interlaced_prefix hL w' ((pb.cons β).cons α) (Quiver.Path.nil.cons β) hw'pos
          hval h0
        exact this
      · exact (cons_ne_of_apart _ α w' β hap h).elim
    · have e : pathVal ((q.cons β).cons α) = a ≫ pathVal ((q.cons β).cons α) ≫ α.1 := by
        conv_lhs => rw [hvω, ha]
        rw [hval, hwω]; simp
      exact (absorb a e).elim

/-- `μ = q β`. -/
abbrev μ : x.out ⟶ y.out := pathVal D.q ≫ D.β.1

/-- The path `v`. -/
abbrev v : Quiver.Path x y := (D.q.cons D.β).cons D.α

lemma ω_v : pathVal D.v = D.μ ≫ D.α.1 := rfl

lemma ω_w {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q) : pathVal D.v = pathVal χ ≫ D.μ := by
  rw [D.hval, hχ]; change pathVal (χ.comp D.q) ≫ D.β.1 = _; rw [pathVal_comp, Category.assoc]

lemma apβα (hM : MildHyp k P) : ArrowsApart D.β D.α :=
  ⟨(D.C.apart hM.right).2, (D.C.apart hM.right).1⟩

lemma uniq (hM : MildHyp k P) (u : Quiver.Path x y) (hu : pathVal u = pathVal D.v) :
    u = D.v ∨ u = D.w'.cons D.β :=
  hM.path_unique D.hval D.h0 D.hni D.α.2.2.1 D.hωρ u hu

/-- The only path with value `μ` is `q β`. -/
lemma uniq_μ (hM : MildHyp k P) (u : Quiver.Path x y) (hu : pathVal u = D.μ) :
    u = D.q.cons D.β := by
  rcases D.uniq hM (u.cons D.α) (by change pathVal u ≫ D.α.1 = _; rw [hu]; rfl) with h | h
  · exact eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
  · exact (cons_ne_of_apart u D.α D.w' D.β (D.C.apart hM.right) h).elim

/-- The only path with value `χ` is `χ`. -/
lemma uniq_χ (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q)
    (u : Quiver.Path x x) (hu : pathVal u = pathVal χ) : u = χ := by
  rcases D.uniq hM ((u.comp D.q).cons D.β) (by
      change pathVal (u.comp D.q) ≫ D.β.1 = _; rw [pathVal_comp, hu, D.ω_w hχ]; simp) with h | h
  · exact (cons_ne_of_apart _ D.β _ D.α (D.apβα hM) h).elim
  · rw [hχ] at h
    exact Quiver.Path.comp_inj_left.1 (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h))

/-- `χ` is not empty. -/
lemma χ_pos (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q) :
    0 < χ.length := by
  by_contra h
  have hl : χ.length = 0 := by omega
  have hc : pathVal χ = 𝟙 _ := by
    cases χ with
    | nil => rfl
    | cons _ _ => simp at hl
  have e : D.μ = 𝟙 _ ≫ D.μ ≫ D.α.1 := by
    rw [← D.ω_v, D.ω_w hχ, hc]; simp
  have hμ0 : D.μ ≠ 0 := fun h ↦ D.h0 (by rw [D.ω_v, h, zero_comp])
  exact D.α.2.2.1 (by rw [(IsRayCategory.eq_id_of_two_sided _ hμ0 _ _ e).2]; infer_instance)

include D in
/-- **`x ≠ y`** ([mild] PDB). -/
lemma x_ne_y (hM : MildHyp k P) : x ≠ y := by
  intro hxy
  obtain ⟨α, t, w', β, q, hval, h0, hni, hρ, hωρ⟩ := D
  subst hxy
  have hap : ArrowsApart β α := (DBData.apβα ⟨α, t, w', β, q, hval, h0, hni, hρ, hωρ⟩ hM)
  have hμ : ¬IsIso (pathVal (q.cons β)) := not_isIso_pathVal _ (by simp)
  obtain ⟨n, hn, hμn⟩ := hρ _ hμ
  have hu := hM.path_unique hval h0 hni α.2.2.1 hωρ (loopPath α (n + 1)) (by
    rw [pathVal_loopPath, rpow_succ, ← hμn]; rfl)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases hu with h | h
  · have h' := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
    exact cons_ne_of_apart _ α _ β ⟨hap.2, hap.1⟩ h'
  · exact cons_ne_of_apart _ α _ β ⟨hap.2, hap.1⟩ h

/-- `v` and `w` have no common nonempty prefix. -/
lemma ni_prefix (hM : MildHyp k P) {a : RayVert P} (p : Quiver.Path x a) (v₁ w₁ : Quiver.Path a y)
    (hp : 0 < p.length) (hv : D.v = p.comp v₁) (hw : D.w'.cons D.β = p.comp w₁) : False := by
  apply D.hni
  change Interlaced D.v (D.w'.cons D.β)
  rw [hv, hw]
  exact interlaced_prefix hM.left p v₁ w₁ hp (by rw [← hv, ← hw]; exact D.hval)
    (by rw [← hv]; exact D.h0)

/-- `χ` does not start with `q β`. -/
lemma χ_not_after_μ (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q)
    (p : Quiver.Path y x) (h : χ = (D.q.cons D.β).comp p) : False := by
  refine D.ni_prefix hM (D.q.cons D.β) (Quiver.Path.nil.cons D.α) ((p.comp D.q).cons D.β)
    (by simp) rfl ?_
  rw [hχ, h, Quiver.Path.comp_assoc]; rfl

/-- **`P(y, x) = 0`** ([mild] PDB, the crown `Ã(χ, μ, α, ν)`). -/
theorem no_yx (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q)
    (ν₀ : y.out ⟶ x.out) : ν₀ = 0 := by
  classical
  by_contra hν₀
  have hR : RightCancel P := hM.right
  have hxy := D.x_ne_y hM
  have hap := D.C.apart hR
  have hβα := D.apβα hM
  have hcn : ¬IsIso (pathVal χ) := not_isIso_pathVal _ (D.χ_pos hM hχ)
  have hμn : ¬IsIso D.μ := not_isIso_pathVal (D.q.cons D.β) (by simp)
  have hα := D.α.2
  have hω : pathVal D.v = pathVal χ ≫ D.μ := D.ω_w hχ
  have h0 := D.h0
  set c := pathVal χ with hc
  set τ := pathVal D.v ≫ D.α.1 with hτ
  have hτ0 : τ ≠ 0 := D.hωρ
  have hτn : ¬IsIso τ := not_isIso_comp_right' _ hα.2.1
  have hτc : c ≫ c ≫ D.μ = τ := by
    rw [hτ]; conv_rhs => rw [hω, Category.assoc, ← D.ω_v, hω]
  have hτμ : D.μ ≫ D.α.1 ≫ D.α.1 = τ := by
    rw [hτ]; show _ = pathVal D.v ≫ _; rw [D.ω_v]; simp
  have noiso : ∀ (g : y.out ⟶ x.out), ¬IsIso g := fun g h ↦
    hxy (show x.out = y.out from (eq_of_isIso h).symm)
  have noiso' : ∀ (g : x.out ⟶ y.out), ¬IsIso g := fun g h ↦
    hxy (show x.out = y.out from eq_of_isIso h)
  -- a nonzero `ν` of minimal depth
  have hex : ∃ n, ∃ ν : y.out ⟶ x.out, ν ≠ 0 ∧ depth ν = n := ⟨_, ν₀, hν₀, rfl⟩
  obtain ⟨ν, hν, hνd⟩ := Nat.find_spec hex
  have hmin : ∀ ν' : y.out ⟶ x.out, ν' ≠ 0 → ¬depth ν' < depth ν := fun ν' h hlt ↦
    Nat.find_min hex (hνd ▸ hlt) ⟨ν', h, rfl⟩
  -- paths
  have path_of : ∀ {a b : P} (g : a ⟶ b), g ≠ 0 →
      ∃ p : Quiver.Path (RayVert.mk a) (RayVert.mk b), pathVal p = g := fun g hg ↦ exists_path g hg
  have h₁c : ¬∃ g, g ≫ ν = c := by
    rintro ⟨g, hg⟩
    have hgν : g ≫ ν ≫ D.μ = pathVal D.v := by rw [hω, ← hg, Category.assoc]
    have hνμ0 : ν ≫ D.μ ≠ 0 := fun h ↦ h0 (by rw [← hgν, h, comp_zero])
    have hνμn : ¬IsIso (ν ≫ D.μ) := fun h ↦ noiso ν (ray_isIso_factors ν D.μ).1
    obtain ⟨m, hm, hνμ⟩ := D.hρ _ hνμn
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [← hgν, h, zero_comp])
    obtain ⟨pg, hpg⟩ := path_of g hg0
    rcases D.uniq hM ((pg.comp (loopPath D.α m')).cons D.α) (by
        change pathVal (pg.comp (loopPath D.α m')) ≫ D.α.1 = _
        rw [pathVal_comp, pathVal_loopPath, hpg, Category.assoc, ← rpow_succ, ← hνμ, hgν])
      with h | h
    · have h' := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
      cases m' with
      | succ m'' => exact cons_ne_of_apart _ D.α _ D.β hap h'
      | zero =>
        change pg = D.q.cons D.β at h'
        have hν0 : ν ≠ 0 := hν
        obtain ⟨pν, hpν⟩ := path_of ν hν0
        exact D.χ_not_after_μ hM hχ pν (D.uniq_χ hM hχ _ (by
          rw [pathVal_comp, ← h', hpg, hpν, hg])).symm
    · exact cons_ne_of_apart _ D.α _ D.β hap h
  have h₃c : ¬∃ g, D.μ ≫ g = c := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [hω, ← hg, h, comp_zero, zero_comp])
    obtain ⟨pg, hpg⟩ := path_of g hg0
    exact D.χ_not_after_μ hM hχ pg (D.uniq_χ hM hχ _ (by
      rw [pathVal_comp, hpg]; exact hg)).symm
  have h₄c : ¬∃ g, c ≫ g = D.μ := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, ← hg, h, comp_zero, zero_comp])
    obtain ⟨pg, hpg⟩ := path_of g hg0
    have e := D.uniq_μ hM (χ.comp pg) (by rw [pathVal_comp, hpg, hg])
    refine D.ni_prefix hM χ (pg.cons D.α) (D.q.cons D.β) (D.χ_pos hM hχ) ?_ ?_
    · change (D.q.cons D.β).cons D.α = _; rw [← e]; rfl
    · rw [hχ]; rfl
  refine hM.not_crown2 τ hτn hτ0 c ν D.α.1 D.μ
    (nfp hτ0 (𝟙 _) c (c ≫ D.μ) (Or.inr (not_isIso_comp_right' _ hμn)) (by simp [hτc]))
    ?_
    (nfp hτ0 D.μ D.α.1 D.α.1 (Or.inl hμn) hτμ)
    (nfp hτ0 (𝟙 _) D.μ (D.α.1 ≫ D.α.1) (Or.inr (not_isIso_comp_right' _ hα.2.1))
      (by simp [hτμ]))
    h₁c ?_ ?_ ?_ ?_ ?_ h₃c h₄c
  · rintro ⟨u, w, hu⟩
    have hu0 : u ≫ τ ≫ w ≠ 0 := by rw [← hu]; exact hν
    have hn : ¬IsIso (τ ≫ w) := fun h ↦ hτn (ray_isIso_factors τ w).1
    refine hmin u (fun h ↦ hu0 (by rw [h, zero_comp])) ?_
    rw [hu]; exact depth_lt_comp_right u (τ ≫ w) hu0 hn
  · rintro ⟨g, hg⟩
    refine hmin g (fun h ↦ hν (by rw [← hg, h, zero_comp])) ?_
    rw [← hg]; exact depth_lt_comp_right g c (by rw [hg]; exact hν) hcn
  · rintro ⟨g, hg⟩
    rcases hα.2.2 _ g D.μ hg.symm with h | h
    · exact noiso g h
    · exact noiso' D.μ h
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, ← hg, h, zero_comp, zero_comp])
    obtain ⟨pg, hpg⟩ := path_of g hg0
    have e := D.uniq_μ hM (pg.cons D.α) (by change pathVal pg ≫ D.α.1 = _; rw [hpg, hg])
    exact cons_ne_of_apart _ D.α _ D.β hap e
  · rintro ⟨g, hg⟩
    rcases hα.2.2 _ ν g hg.symm with h | h
    · exact noiso ν h
    · exact noiso' g h
  · rintro ⟨g, hg⟩
    refine hmin g (fun h ↦ hν (by rw [← hg, h, comp_zero])) ?_
    rw [← hg]; exact depth_lt_comp_left D.α.1 g (by rw [hg]; exact hν) hα.2.1

/-- No path with value `ω` ends with `α α`. -/
lemma no_αα (hM : MildHyp k P) (p' : Quiver.Path x y)
    (h : pathVal ((p'.cons D.α).cons D.α) = pathVal D.v) : False := by
  have hap := D.C.apart hM.right
  rcases D.uniq hM _ h with e | e
  · exact cons_ne_of_apart _ D.α _ D.β hap (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons e))
  · exact cons_ne_of_apart _ D.α _ D.β hap e

/-- **`χ` is an arrow** ([mild] PDB, figure 2.3, first diagram, `Ẽ₆`). -/
theorem χ_len (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q) :
    χ.length = 1 := by
  have hpos := D.χ_pos hM hχ
  by_contra hne
  have hR : RightCancel P := hM.right
  have hμn : ¬IsIso D.μ := not_isIso_pathVal (D.q.cons D.β) (by simp)
  have hα := D.α.2
  have hω : pathVal D.v = pathVal χ ≫ D.μ := D.ω_w hχ
  have h0 := D.h0
  have hτ0 : pathVal D.v ≫ D.α.1 ≠ 0 := D.hωρ
  have hτn : ¬IsIso (pathVal D.v ≫ D.α.1) := not_isIso_comp_right' _ hα.2.1
  have hnz := D.no_yx hM hχ
  match χ, hχ, hpos, hne, hω with
  | .cons χ' e, hχ, _, hne, hω =>
  have hχ' : 0 < χ'.length := by simp at hne; omega
  set c₁ := pathVal χ' with hc₁
  set c₂ := e.1 with hc₂
  have hc : pathVal (χ'.cons e) = c₁ ≫ c₂ := rfl
  have hc₁n : ¬IsIso c₁ := not_isIso_pathVal _ hχ'
  have hc₂n : ¬IsIso c₂ := e.2.2.1
  set τ := pathVal D.v ≫ D.α.1 with hτ
  have hτc : c₁ ≫ c₂ ≫ c₁ ≫ c₂ ≫ D.μ = τ := by
    rw [hτ]; conv_rhs => rw [hω, hc, Category.assoc, Category.assoc, ← D.ω_v, hω, hc]
    simp
  have hτμ : D.μ ≫ D.α.1 ≫ D.α.1 = τ := by
    rw [hτ]; show _ = pathVal D.v ≫ _; rw [D.ω_v]; simp
  refine hM.not_db23a τ hτn hτ0 c₁ c₂ c₁ c₂ D.μ (D.α.1 ≫ D.α.1)
    (nfp hτ0 (c₁ ≫ c₂) c₁ (c₂ ≫ D.μ) (Or.inl (not_isIso_comp_left' _ hc₁n))
      (by rw [← hτc]; simp))
    (nfp hτ0 (c₁ ≫ c₂) (c₁ ≫ c₂) D.μ (Or.inl (not_isIso_comp_left' _ hc₁n))
      (by rw [← hτc]; simp))
    (nfp hτ0 (𝟙 _) D.μ (D.α.1 ≫ D.α.1) (Or.inr (not_isIso_comp_right' _ hα.2.1))
      (by rw [← hτμ]; simp))
    (nfp hτ0 c₁ c₂ (c₁ ≫ c₂ ≫ D.μ) (Or.inl hc₁n) hτc)
    (nfp hτ0 c₁ (c₂ ≫ c₁) (c₂ ≫ D.μ) (Or.inl hc₁n) (by rw [← hτc]; simp))
    (nfp hτ0 c₁ ((c₂ ≫ c₁) ≫ c₂) D.μ (Or.inl hc₁n) (by rw [← hτc]; simp))
    (nfp hτ0 (c₁ ≫ c₂ ≫ c₁) (c₂ ≫ D.μ) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hc₁n))
      (by rw [← hτc]; simp))
    (nfp hτ0 (𝟙 _) c₁ (c₂ ≫ c₁ ≫ c₂ ≫ D.μ) (Or.inr (not_isIso_comp_left' _ hc₂n)) (by
      rw [← hτc]; simp))
    (nfp hτ0 (𝟙 _) (c₁ ≫ c₂) (c₁ ≫ c₂ ≫ D.μ) (Or.inr (not_isIso_comp_left' _ hc₁n)) (by
      rw [← hτc]; simp))
    (nfp hτ0 (𝟙 _) ((c₁ ≫ c₂) ≫ c₁) (c₂ ≫ D.μ) (Or.inr (not_isIso_comp_left' _ hc₂n)) (by
      rw [← hτc]; simp))
    (nfp hτ0 (𝟙 _) (((c₁ ≫ c₂) ≫ c₁) ≫ c₂) D.μ (Or.inr hμn) (by rw [← hτc]; simp))
    (nfp hτ0 (c₁ ≫ c₂) ((c₁ ≫ c₂) ≫ D.μ) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hc₁n))
      (by rw [← hτc]; simp))
    (nfp hτ0 c₁ c₂ (c₁ ≫ c₂ ≫ D.μ) (Or.inl hc₁n) hτc)
    (nfp hτ0 D.μ (D.α.1 ≫ D.α.1) (𝟙 _) (Or.inl hμn) (by rw [← hτμ]; simp))
    hc₁n hc₂n hc₁n hc₂n hμn (not_isIso_comp_right' _ hα.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, ← hg, h, comp_zero, zero_comp])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    have e' := D.uniq_μ hM (χ'.comp pg) (by rw [pathVal_comp, hpg, hg])
    refine D.ni_prefix hM χ' (pg.cons D.α) (((Quiver.Path.nil.cons e).comp D.q).cons D.β) hχ'
      ?_ ?_
    · change (D.q.cons D.β).cons D.α = _; rw [← e']; rfl
    · rw [hχ]
      show _ = (χ'.comp ((Quiver.Path.nil.cons e).comp D.q)).cons D.β
      rw [← Quiver.Path.comp_assoc]; rfl
  · rintro ⟨g, hg⟩
    apply h0
    rw [hω, hc, ← hg]; simp only [Category.assoc]
    rw [← Category.assoc g, hnz (g ≫ c₂)]; simp
  · rintro ⟨g, hg⟩
    apply h0
    rw [hω, hc, ← hg, hnz g, comp_zero, zero_comp]
  · rintro ⟨g, hg⟩
    apply hτ0
    rw [← hτμ, ← hg, hnz g, zero_comp, comp_zero]
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, ← hg, h, zero_comp, zero_comp])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    exact D.no_αα hM (pg.cons D.α) (by
      change ((pathVal pg ≫ D.α.1) ≫ D.α.1) ≫ D.α.1 = _; rw [hpg, D.ω_v, ← hg]; simp)
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by
      rw [hω, hc, Category.assoc, ← hg, h, zero_comp, comp_zero])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    exact D.no_αα hM (χ'.comp pg) (by
      change (pathVal (χ'.comp pg) ≫ D.α.1) ≫ D.α.1 = _
      rw [pathVal_comp, hpg, hω, hc]; simp only [Category.assoc]; rw [← hg])
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [hω, hc, ← hg, h, zero_comp])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    exact D.no_αα hM pg (by
      change (pathVal pg ≫ D.α.1) ≫ D.α.1 = _; rw [hpg, hω, hc, ← hg]; simp)

/-- The only path with value `q` is `q`. -/
lemma uniq_q (hM : MildHyp k P) (u : Quiver.Path x D.t) (hu : pathVal u = pathVal D.q) :
    u = D.q :=
  eq_of_heq (Quiver.Path.heq_of_cons_eq_cons
    (D.uniq_μ hM (u.cons D.β) (by change pathVal u ≫ D.β.1 = _; rw [hu])))

/-- `μ` does not factor through `χ`. -/
lemma not_c_μ (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q) :
    ¬∃ g, pathVal χ ≫ g = D.μ := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := fun h ↦ D.h0 (by rw [D.ω_v, ← hg, h, comp_zero, zero_comp])
  obtain ⟨pg, hpg⟩ := exists_path g hg0
  have e := D.uniq_μ hM (χ.comp pg) (by rw [pathVal_comp, hpg, hg])
  refine D.ni_prefix hM χ (pg.cons D.α) (D.q.cons D.β) (D.χ_pos hM hχ) ?_ ?_
  · change (D.q.cons D.β).cons D.α = _; rw [← e]; rfl
  · rw [hχ]; rfl

/-- `χ` does not factor as `q ≫ g`. -/
lemma not_q_g (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q)
    (hq : 0 < D.q.length) (g : D.t.out ⟶ x.out) (hg : pathVal D.q ≫ g = pathVal χ) : False := by
  have hg0 : g ≠ 0 := fun h ↦ D.h0 (by rw [D.ω_w hχ, ← hg, h, comp_zero, zero_comp])
  obtain ⟨pg, hpg⟩ := exists_path g hg0
  have e := D.uniq_χ hM hχ (D.q.comp pg) (by rw [pathVal_comp, hpg, hg])
  refine D.ni_prefix hM D.q ((Quiver.Path.nil.cons D.β).cons D.α) ((pg.comp D.q).cons D.β) hq
    rfl ?_
  rw [hχ, ← e, Quiver.Path.comp_assoc]; rfl

/-- **`q` is empty** ([mild] PDB, figure 2.3, second diagram, `D̃₇`). -/
theorem q_nil (hM : MildHyp k P) {χ : Quiver.Path x x} (hχ : D.w' = χ.comp D.q) :
    D.q.length = 0 := by
  by_contra hne
  have hq : 0 < D.q.length := by omega
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := D.C.apart hR
  have hμn : ¬IsIso D.μ := not_isIso_pathVal (D.q.cons D.β) (by simp)
  have hα := D.α.2
  have hβ := D.β.2
  have hω : pathVal D.v = pathVal χ ≫ D.μ := D.ω_w hχ
  have h0 := D.h0
  have hτ0 : pathVal D.v ≫ D.α.1 ≠ 0 := D.hωρ
  have hτn : ¬IsIso (pathVal D.v ≫ D.α.1) := not_isIso_comp_right' _ hα.2.1
  have hnz := D.no_yx hM hχ
  have hcirr : IsIrreducible (pathVal χ) := irr_of_length_one χ (D.χ_len hM hχ)
  set c := pathVal χ with hc
  set φ := pathVal D.q with hφ
  have hφn : ¬IsIso φ := not_isIso_pathVal _ hq
  have hμ : D.μ = φ ≫ D.β.1 := rfl
  set τ := pathVal D.v ≫ D.α.1 with hτ
  have hτc : c ≫ c ≫ D.μ = τ := by
    rw [hτ]; conv_rhs => rw [hω, Category.assoc, ← D.ω_v, hω]
  have hτμ : D.μ ≫ D.α.1 ≫ D.α.1 = τ := by
    rw [hτ]; show _ = pathVal D.v ≫ _; rw [D.ω_v]; simp
  have hτφ : c ≫ φ ≫ D.β.1 ≫ D.α.1 = τ := by
    rw [hτ, hω]; simp [hμ]
  have nφg : ¬∃ g, φ ≫ g = c := by
    rintro ⟨g, hg⟩
    exact D.not_q_g hM hχ hq g hg
  refine hM.not_db23b τ hτn hτ0 c c φ D.μ D.α.1 D.α.1 D.β.1
    (nfp hτ0 c c D.μ (Or.inl hcirr.2.1) hτc)
    (nfp hτ0 c φ (D.β.1 ≫ D.α.1) (Or.inl hcirr.2.1) hτφ)
    (nfp hτ0 (𝟙 _) c (c ≫ D.μ) (Or.inr (not_isIso_comp_right' _ hμn)) (by simp [hτc]))
    (nfp hτ0 (𝟙 _) (c ≫ c) D.μ (Or.inr hμn) (by simp [hτc]))
    (nfp hτ0 (𝟙 _) (c ≫ φ) (D.β.1 ≫ D.α.1) (Or.inr (not_isIso_comp_right' _ hα.2.1))
      (by simp [hτφ]))
    (nfp hτ0 (𝟙 _) D.μ (D.α.1 ≫ D.α.1) (Or.inr (not_isIso_comp_right' _ hα.2.1))
      (by simp [hτμ]))
    (nfp hτ0 D.μ D.α.1 D.α.1 (Or.inl hμn) hτμ)
    (nfp hτ0 D.μ D.α.1 D.α.1 (Or.inl hμn) hτμ)
    (nfp hτ0 D.μ (D.α.1 ≫ D.α.1) (𝟙 _) (Or.inl hμn) (by simp [hτμ]))
    (nfp hτ0 (c ≫ φ) D.β.1 D.α.1 (Or.inl (not_isIso_comp_left' _ hcirr.2.1)) (by simp [hτφ]))
    (nfp hτ0 (c ≫ φ) (D.β.1 ≫ D.α.1) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hcirr.2.1))
      (by simp [hτφ]))
    hcirr.2.1 hcirr.2.1 hφn hμn hα.2.1 hα.2.1 hβ.2.1 ?_ nφg (D.not_c_μ hM hχ) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ hap.2 hap.1
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, hμ, ← hg, h, comp_zero, zero_comp, zero_comp])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    have e := D.uniq_q hM (χ.comp pg) (by rw [pathVal_comp, hpg, hg])
    refine D.ni_prefix hM χ ((pg.cons D.β).cons D.α) (D.q.cons D.β) (D.χ_pos hM hχ) ?_ ?_
    · change ((D.q).cons D.β).cons D.α = _; rw [← e]; rfl
    · rw [hχ]; rfl
  · rintro ⟨g, hg⟩
    exact h0 (by rw [hω, ← hg, hnz g, comp_zero, zero_comp])
  · rintro ⟨g, hg⟩
    exact hτ0 (by rw [← hτc, ← Category.assoc, ← hg, hnz g, comp_zero, zero_comp])
  · rintro ⟨g, hg⟩
    have e : D.μ ≫ D.α.1 = D.μ ≫ (g ≫ D.β.1) := by
      rw [← D.ω_v, hω, hμ, ← Category.assoc, ← hg]; simp [hμ]
    exact hap.1 ⟨g, (hL _ _ _ e (by rw [← D.ω_v]; exact h0)).symm⟩
  · rintro ⟨g, hg⟩
    exact hα.1 (by rw [← hg, hnz g, zero_comp])
  · rintro ⟨g, hg⟩
    exact hτ0 (by rw [← hτμ, ← hg, hnz g, zero_comp, comp_zero])
  · rintro ⟨g, hg⟩
    have e : c ≫ (φ ≫ D.β.1) = (φ ≫ g) ≫ (φ ≫ D.β.1) := by
      rw [← hμ, ← hω, D.ω_v, hμ, Category.assoc, ← hg]; simp [hμ]
    exact nφg ⟨g, (hR _ _ _ e (by rw [← hμ, ← hω]; exact h0)).symm⟩
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [D.ω_v, ← hg, h, zero_comp, zero_comp])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    exact cons_ne_of_apart _ D.α _ D.β hap
      (D.uniq_μ hM (pg.cons D.α) (by change pathVal pg ≫ D.α.1 = _; rw [hpg, hg]))

end DBData

end RayCat

end LargeIndecomposable
