module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.ZChain

/-!
# The base of a cyclic walk is joined (Fischbacher, Lemma 4.4, positive form)

In a cyclic zigzag walk whose peaks are distinct vertices and whose inner peaks are separating
in the hull, every vertex lies below the base (`cyc_max`), and the two arrows at the base lie in
one component of the morphisms into it inside the hull (`cyc_join`). This is the form of
Lemma 4.4 used to restore separation after the cuts of Fischbacher's §5.4.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- A point with no arrow into `H` reaches no other point of a convex `H`. -/
lemma eq_of_max_reach {H : Set A} (hH : ConvexR H) {q y : A} (hq : q ∈ H) (hy : y ∈ H)
    (hmax : ∀ {z : RayVert A} (_ : RayVert.mk q ⟶ z), z.out ∉ H) (h : Reaches q y) : y = q := by
  obtain ⟨p⟩ := h
  rcases hlen : p.length with _ | n
  · exact (Quiver.Path.eq_of_length_zero p hlen).symm
  · obtain ⟨z, f, r, -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ p hlen
    exact absurd (hH _ hq _ hy z.out ⟨f.toPath⟩ ⟨r⟩) (hmax f)

/-- Vertices of a segment of a cyclic list reach the peaks at its ends. -/
lemma cyc_reach {e : A} {C : List (ZSeg A)} (hl : ZLinked e C) (hc : ZLast e C = e) (r : ℕ)
    (hr : r < C.length) {v : A} :
    (v ∈ pathVerts C[r].t → Reaches v (zPeak e C r)) ∧
      (v ∈ pathVerts C[r].s → Reaches v (zPeak e C (if r + 1 < C.length then r + 1 else 0))) := by
  have hpk := zPeak_seg e C hl
  have hwrap : zPeak e C C.length = zPeak e C 0 := by rw [zPeak_length, hc, zPeak_zero]
  refine ⟨fun hv ↦ (hpk r hr).1 ▸ (reaches_of_mem_pathVerts _ hv).2, fun hv ↦ ?_⟩
  have h := (hpk r hr).2 ▸ (reaches_of_mem_pathVerts _ hv).2
  split_ifs with h'
  · exact h
  · rwa [show r + 1 = C.length by omega, hwrap] at h

lemma zPeak_mem_segsVerts {e : A} {C : List (ZSeg A)} (hl : ZLinked e C) {r : ℕ}
    (hr : r < C.length) : zPeak e C r ∈ segsVerts C := by
  rw [← (zPeak_seg e C hl r hr).1]
  exact mem_segsVerts (List.getElem_mem hr) (Or.inl (mem_pathVerts_end _))

/-- Entries of `L₂ ++ L₁` sit at positions other than those of the two middle entries. -/
lemma exists_idx_other {C L₁ L₂ : List (ZSeg A)} {ρ₁ ρ₂ ρ : ZSeg A}
    (hsplit : C = L₁ ++ ρ₁ :: ρ₂ :: L₂) (hρ : ρ ∈ L₂ ++ L₁) :
    ∃ r, ∃ hr : r < C.length, C[r] = ρ ∧ r ≠ L₁.length ∧ r ≠ L₁.length + 1 := by
  have hClen : C.length = L₁.length + 2 + L₂.length := by rw [hsplit]; simp; omega
  rcases List.mem_append.1 hρ with h | h
  · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
    refine ⟨L₁.length + 2 + r', by omega, ?_, by omega, by omega⟩
    simp only [hsplit, List.getElem_append_right (show L₁.length ≤ L₁.length + 2 + r' by omega)]
    simp [show L₁.length + 2 + r' - L₁.length = r' + 2 by omega]
  · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
    exact ⟨r', by omega, by simp [hsplit, List.getElem_append_left hr'], by omega, by omega⟩

/-- **Every vertex of a cyclic walk with distinct peaks and separating inner peaks lies below
the base.** -/
theorem cyc_max (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {e : A} {C : List (ZSeg A)} (hl : ZLinked e C) (hc : ZLast e C = e) (hne : C ≠ [])
    (hpos : ∀ ρ ∈ C, 0 < ρ.s.length ∧ 0 < ρ.t.length)
    (hdist : ∀ i j, i < C.length → j < C.length → zPeak e C i = zPeak e C j → i = j)
    (hsep : SepAll (hullOf (segsVerts C)) C) {u : A} (hu : u ∈ segsVerts C) : Reaches u e := by
  obtain ⟨M₁, M₂, π, hsplit, hup, hmax⟩ := exists_max_peak hcf hint hl hc hne hu
  by_cases hπ : π.d = e
  · exact hπ ▸ hup
  exfalso
  obtain ⟨π₂, R, rfl⟩ : ∃ (π₂ : ZSeg A) (R : List (ZSeg A)), M₂ = π₂ :: R := by
    rcases M₂ with _ | ⟨π₂, R⟩
    · exfalso
      apply hπ
      have hc' := hc
      rw [hsplit, zLast_append] at hc'
      exact hc'
    · exact ⟨π₂, R, rfl⟩
  obtain ⟨c, dl, q, t, s⟩ := π
  obtain ⟨c', q', d', t', s'⟩ := π₂
  have hlink := hl
  rw [hsplit, zLinked_append] at hlink
  obtain ⟨-, -, hq', -⟩ := hlink
  change q' = q at hq'
  subst hq'
  have hπmem : (⟨c, dl, q', t, s⟩ : ZSeg A) ∈ C := by rw [hsplit]; simp
  have hπ₂mem : (⟨c', q', d', t', s'⟩ : ZSeg A) ∈ C := by rw [hsplit]; simp
  obtain ⟨x₁, s₀, e₁, rfl⟩ : ∃ (x₁ : RayVert A) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q'), s = s₀.cons e₁ := by
    rcases s with _ | ⟨s₀, e₁⟩
    · exact absurd (hpos _ hπmem).1 (lt_irrefl 0)
    · exact ⟨_, s₀, e₁, rfl⟩
  obtain ⟨x₂, t₀, e₂, rfl⟩ : ∃ (x₂ : RayVert A) (t₀ : Quiver.Path (RayVert.mk c') x₂)
      (e₂ : x₂ ⟶ RayVert.mk q'), t' = t₀.cons e₂ := by
    rcases t' with _ | ⟨t₀, e₂⟩
    · exact absurd (hpos _ hπ₂mem).2 (lt_irrefl 0)
    · exact ⟨_, t₀, e₂, rfl⟩
  have hns := hsep M₁ R c dl q' c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
  -- rotate to the front
  obtain ⟨hl', hc'⟩ := zCyc_rotate e M₁ (_ :: _ :: R) (hsplit ▸ hl) (hsplit ▸ hc)
  have hdl : ZLast e M₁ = dl := by
    have := hl
    rw [hsplit, zLinked_append] at this
    exact this.2.1.symm
  rw [hdl] at hl' hc'
  obtain ⟨-, -, hlR'⟩ := hl'
  change ZLast d' (R ++ M₁) = dl at hc'
  set H := hullOf (segsVerts C) with hH
  have hfin : (segsVerts C).Finite :=
    C.finite_toSet.biUnion fun σ _ ↦ (pathVerts_finite σ.t).union (pathVerts_finite σ.s)
  have hsub : segsVerts (⟨c, dl, q', t, s₀.cons e₁⟩ :: ⟨c', q', d', t₀.cons e₂, s'⟩ :: (R ++ M₁))
      ⊆ H := by
    intro x hx
    apply subset_hullOf
    obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
    refine mem_segsVerts (σ := σ) ?_ hxσ
    rw [hsplit]
    simp only [List.mem_cons, List.mem_append] at hσ ⊢
    tauto
  -- positions
  have hpk := zPeak_seg e C hl
  have hClen : C.length = M₁.length + 2 + R.length := by rw [hsplit]; simp; omega
  have hCm : C[M₁.length]'(by omega) = ⟨c, dl, q', t, s₀.cons e₁⟩ := by
    simp only [hsplit, List.getElem_append_right (le_refl _), Nat.sub_self,
      List.getElem_cons_zero]
  have hCm1 : C[M₁.length + 1]'(by omega) = ⟨c', q', d', t₀.cons e₂, s'⟩ := by
    rw [List.getElem_of_eq hsplit]
    simp [List.getElem_append_right (Nat.le_succ M₁.length)]
  have hq : q' = zPeak e C (M₁.length + 1) := by
    have := (hpk M₁.length (by omega)).2
    rw [hCm] at this
    exact this
  have hqH : q' ∈ H := subset_hullOf _ (mem_segsVerts hπmem (Or.inr (mem_pathVerts_end _)))
  have hcon : ∀ x, x < C.length → x ≠ M₁.length + 1 → Reaches q' (zPeak e C x) → False := by
    intro x hx hxm h
    have h1 := eq_of_max_reach (convexR_hullOf _) hqH
      (subset_hullOf _ (zPeak_mem_segsVerts hl hx)) hmax h
    rw [hq] at h1
    exact hxm (hdist _ _ hx (by omega) h1)
  have hreach := cyc_reach hl hc
  have hav' : q' ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts (R ++ M₁) ∪ pathVerts s₀ ∪
      pathVerts t₀ := by
    intro hqv
    rcases hqv with (((hv | hv) | hv) | hv) | hv
    · have := (hreach M₁.length (by omega) (v := q')).1 (by rw [hCm]; exact hv)
      exact hcon _ (by omega) (by omega) this
    · have := (hreach (M₁.length + 1) (by omega) (v := q')).2 (by rw [hCm1]; exact hv)
      split_ifs at this with h
      · exact hcon _ h (by omega) this
      · exact hcon 0 (by omega) (by omega) this
    · obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
      obtain ⟨r, hr, hCr, hrm, hrm1⟩ := exists_idx_other hsplit hρ
      rcases hvρ with hv' | hv'
      · have := (hreach r hr (v := q')).1 (by rw [hCr]; exact hv')
        exact hcon r hr hrm1 this
      · have := (hreach r hr (v := q')).2 (by rw [hCr]; exact hv')
        split_ifs at this with h
        · exact hcon (r + 1) h (by omega) this
        · exact hcon 0 (by omega) (by omega) this
    · obtain ⟨p₁⟩ := (reaches_of_mem_pathVerts s₀ hv).2
      have := hcf q' (p₁.cons e₁)
      simp at this
    · obtain ⟨p₂⟩ := (reaches_of_mem_pathVerts t₀ hv).2
      have := hcf q' (p₂.cons e₂)
      simp at this
  exact hns (sepComp_front2 (finite_hullOf hint hfin) (convexR_hullOf _)
    (hsc _ (finite_hullOf hint hfin) (convexR_hullOf _)) hlR' hc' hsub hav' hmax)

/-- **The two arrows at the base of a cyclic walk with distinct peaks and separating inner peaks
lie in one component** (Fischbacher, Lemma 4.4). -/
theorem cyc_join (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {e : A} {C : List (ZSeg A)} (hl : ZLinked e C) (hc : ZLast e C = e)
    (hpos : ∀ ρ ∈ C, 0 < ρ.s.length ∧ 0 < ρ.t.length)
    (hdist : ∀ i j, i < C.length → j < C.length → zPeak e C i = zPeak e C j → i = j)
    (hsep : SepAll (hullOf (segsVerts C)) C)
    {c c' dl d' : A} {x₁ x₂ : RayVert A} {t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)}
    {s₀ : Quiver.Path (RayVert.mk c) x₁} {e₁ : x₁ ⟶ RayVert.mk e}
    {t₀ : Quiver.Path (RayVert.mk c') x₂} {e₂ : x₂ ⟶ RayVert.mk e}
    {s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')} {M L' : List (ZSeg A)}
    (h1 : C = ⟨c', e, d', t₀.cons e₂, s'⟩ :: M) (h2 : C = L' ++ [⟨c, dl, e, t, s₀.cons e₁⟩]) :
    SepComp (hullOf (segsVerts C)) e ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  set H := hullOf (segsVerts C) with hH
  have hne : C ≠ [] := by rw [h1]; simp
  have hfin : (segsVerts C).Finite :=
    C.finite_toSet.biUnion fun σ _ ↦ (pathVerts_finite σ.t).union (pathVerts_finite σ.s)
  have hHfin : H.Finite := finite_hullOf hint hfin
  have h0 : 0 < C.length := List.length_pos_of_ne_nil hne
  have heV : e ∈ segsVerts C := by
    have := zPeak_mem_segsVerts hl h0
    rwa [zPeak_zero] at this
  have heH : e ∈ H := subset_hullOf _ heV
  have hmaxe : ∀ {y : RayVert A} (_ : RayVert.mk e ⟶ y), y.out ∉ H := by
    intro y f hy
    obtain ⟨-, -, b', hb', -, ⟨hyb⟩⟩ := hy
    obtain ⟨hbe⟩ := cyc_max hcf hint hsc hl hc hne hpos hdist hsep hb'
    have := hcf e ((f.toPath.comp hyb).comp hbe)
    simp [Quiver.Path.length_comp] at this
  have hmx : ∀ y ∈ H, Reaches e y → y = e := fun y hy h ↦
    eq_of_max_reach (convexR_hullOf _) heH hy hmaxe h
  have hσV : ∀ ρ ∈ C, ρ.verts ⊆ H := fun ρ hρ _ hx ↦ subset_hullOf _ (mem_segsVerts hρ hx)
  have hav₀ : e ∉ pathVerts s₀ ∪ pathVerts t₀ := by
    rintro (hv | hv)
    · obtain ⟨p₁⟩ := (reaches_of_mem_pathVerts s₀ hv).2
      have := hcf e (p₁.cons e₁)
      simp at this
    · obtain ⟨p₂⟩ := (reaches_of_mem_pathVerts t₀ hv).2
      have := hcf e (p₂.cons e₂)
      simp at this
  rcases M with _ | ⟨σ₂, M'⟩
  · -- one segment
    have h12 := h1.symm.trans h2
    rcases L' with _ | ⟨x, L'⟩
    · simp only [List.nil_append, List.cons.injEq, ZSeg.mk.injEq, and_true] at h12
      obtain ⟨rfl, rfl, rfl, ht, hs⟩ := h12
      obtain rfl := eq_of_heq ht
      obtain rfl := eq_of_heq hs
      refine sepComp_front1 (s₀ := s₀) (t₀ := t₀) hHfin (convexR_hullOf _)
        (hsc _ hHfin (convexR_hullOf _))
        (hσV _ (by rw [h1]; simp)) (by simpa [Set.union_comm] using hav₀) hmaxe
    · simp at h12
  · -- at least two segments: rotate the base to the front
    obtain ⟨R, hR⟩ : ∃ R, L' = ⟨c', e, d', t₀.cons e₂, s'⟩ :: R := by
      rcases L' with _ | ⟨x, R⟩
      · have := h1.symm.trans h2
        simp at this
      · have := h1.symm.trans h2
        simp only [List.cons_append, List.cons.injEq] at this
        exact ⟨R, by rw [this.1]⟩
    subst hR
    have hC : C = ⟨c', e, d', t₀.cons e₂, s'⟩ :: (R ++ [⟨c, dl, e, t, s₀.cons e₁⟩]) := by
      rw [h2]; rfl
    have hClen : C.length = R.length + 2 := by rw [hC]; simp
    have hl2 := hl
    rw [hC] at hl2
    obtain ⟨-, hl3⟩ := hl2
    change ZLinked d' (R ++ [_]) at hl3
    obtain ⟨hlR, hdl⟩ := zLinked_concat.1 hl3
    change dl = ZLast d' R at hdl
    have hpk := zPeak_seg e C hl
    have hlast : C[R.length + 1]'(by omega) = ⟨c, dl, e, t, s₀.cons e₁⟩ := by
      simp [hC, List.getElem_append_right]
    have hfirst : C[0]'h0 = ⟨c', e, d', t₀.cons e₂, s'⟩ := by simp [hC]
    have hmid : ∀ r (hr : r < R.length), C[r + 1]'(by omega) = R[r] := by
      intro r hr
      simp [hC, List.getElem_append_left hr]
    have hcon : ∀ x, x < C.length → x ≠ 0 → Reaches e (zPeak e C x) → False := by
      intro x hx hx0 h
      have h' := hmx _ (subset_hullOf _ (zPeak_mem_segsVerts hl hx)) h
      rw [← zPeak_zero e C] at h'
      exact hx0 (hdist _ _ hx h0 h')
    have hV : segsVerts (⟨c, dl, e, t, s₀.cons e₁⟩ :: ⟨c', e, d', t₀.cons e₂, s'⟩ :: R) ⊆ H := by
      intro x hx
      obtain ⟨ρ, hρ, hxρ⟩ := Set.mem_iUnion₂.1 hx
      refine hσV ρ ?_ hxρ
      rw [hC]
      simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hρ ⊢
      tauto
    have hav : e ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts R ∪ pathVerts s₀ ∪ pathVerts t₀ := by
      intro hv
      rcases hv with (((hv | hv) | hv) | hv) | hv
      · have := (reaches_of_mem_pathVerts t hv).2
        have hdlp := (hpk (R.length + 1) (by omega)).1
        rw [hlast] at hdlp
        change dl = _ at hdlp
        rw [hdlp] at this
        exact hcon _ (by omega) (by omega) this
      · have := (reaches_of_mem_pathVerts s' hv).2
        have hdp := (hpk 0 h0).2
        rw [hfirst] at hdp
        change d' = _ at hdp
        rw [hdp] at this
        exact hcon _ (by omega) (by omega) this
      · obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
        obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hρ
        have hp := hpk (r + 1) (by omega)
        rw [hmid r hr] at hp
        rcases hvρ with hv' | hv'
        · have := (reaches_of_mem_pathVerts _ hv').2
          rw [hp.1] at this
          exact hcon _ (by omega) (by omega) this
        · have := (reaches_of_mem_pathVerts _ hv').2
          rw [hp.2] at this
          exact hcon _ (by omega) (by omega) this
      · exact hav₀ (Or.inl hv)
      · exact hav₀ (Or.inr hv)
    exact sepComp_front2 hHfin (convexR_hullOf _) (hsc _ hHfin (convexR_hullOf _)) hlR hdl.symm
      hV hav hmaxe

end LargeIndecomposable.RayCat
