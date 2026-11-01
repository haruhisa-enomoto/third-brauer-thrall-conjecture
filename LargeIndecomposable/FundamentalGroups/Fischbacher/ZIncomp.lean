module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.ZCycle

/-!
# Incomparability of peaks (Fischbacher, proof of Lemma 5.2, property (4))

`closeB`: a linked list of segments whose peaks are pairwise incomparable except possibly the
two end peaks, with every inner peak separating, admits no path from its last peak back to its
first: splicing such a path into the last segment closes a cycle whose base is the first peak, and
`cyc_top` puts the second peak below the first.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

lemma SepComp.mono {D D' : Set A} {b : A} (h : D ⊆ D') {f g : Σ x : A, x ⟶ b}
    (hfg : SepComp D b f g) : SepComp D' b f g :=
  Relation.EqvGen.mono (fun _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ ↦ ⟨h1, h2, h h3, h h4, h5, h6, h7⟩) _ _ hfg

lemma zLinked_concat {e : A} {M : List (ZSeg A)} {σ : ZSeg A} :
    ZLinked e (M ++ [σ]) ↔ ZLinked e M ∧ σ.dl = ZLast e M := by
  rw [zLinked_append]
  simp [ZLinked]

lemma zLast_concat (e : A) (M : List (ZSeg A)) (σ : ZSeg A) : ZLast e (M ++ [σ]) = σ.d := by
  rw [zLast_append]; rfl

lemma zPeak_concat_lt (e : A) (M : List (ZSeg A)) (σ σ' : ZSeg A) {r : ℕ} (hr : r ≤ M.length) :
    zPeak e (M ++ [σ']) r = zPeak e (M ++ [σ]) r := by
  simp only [zPeak, List.take_append_of_le_length hr]

lemma zPeak_length (e : A) (M : List (ZSeg A)) : zPeak e M M.length = ZLast e M := by
  simp [zPeak]

variable [IsRayCategory A]

lemma hullOf_subset {T H : Set A} (hH : ConvexR H) (hT : T ⊆ H) : hullOf T ⊆ H :=
  fun _ ⟨a, ha, b, hb, h1, h2⟩ ↦ hH _ (hT ha) _ (hT hb) _ h1 h2

lemma reaches_of_mem_seg {ρ : ZSeg A} {v : A} (hv : v ∈ ρ.verts) :
    Reaches v ρ.dl ∨ Reaches v ρ.d := by
  rcases hv with hv | hv
  · exact Or.inl (reaches_of_mem_pathVerts ρ.t hv).2
  · exact Or.inr (reaches_of_mem_pathVerts ρ.s hv).2

/-- Vertices of entries of a list. -/
lemma exists_idx_of_mem_segsVerts {L : List (ZSeg A)} {v : A} (hv : v ∈ segsVerts L) :
    ∃ (r : ℕ) (hr : r < L.length), v ∈ L[r].verts := by
  obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hρ
  exact ⟨r, hr, hvρ⟩

/-- **Closing a linked list by a path from its last peak back to its first is impossible**
when all other pairs of peaks are incomparable and the inner peaks are separating. -/
theorem closeB (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {M' : List (ZSeg A)} {σ : ZSeg A} (hne : M' ≠ [])
    (hl : ZLinked e (M' ++ [σ])) (hV : segsVerts (M' ++ [σ]) ⊆ Hb) (he : e ∈ Hb)
    (hinc : ∀ a b, a < b → b ≤ M'.length + 1 → ¬(a = 0 ∧ b = M'.length + 1) →
      ¬Reaches (zPeak e (M' ++ [σ]) a) (zPeak e (M' ++ [σ]) b) ∧
        ¬Reaches (zPeak e (M' ++ [σ]) b) (zPeak e (M' ++ [σ]) a))
    (hsep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      M' ++ [σ] = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩)
    (hpos : ∀ ρ ∈ M' ++ [σ], 0 < ρ.s.length ∧ 0 < ρ.t.length) (hp : Reaches σ.d e) : False := by
  obtain ⟨σc, σdl, σd, σt, σs⟩ := σ
  obtain ⟨p⟩ := hp
  set M := M' ++ [(⟨σc, σdl, σd, σt, σs⟩ : ZSeg A)] with hM
  set σ' : ZSeg A := ⟨σc, σdl, e, σt, σs.comp p⟩ with hσ'
  set C := M' ++ [σ'] with hC
  have hlM := zLinked_concat.1 hl
  have hlC : ZLinked e C := zLinked_concat.2 ⟨hlM.1, hlM.2⟩
  have hcC : ZLast e C = e := zLast_concat _ _ _
  have hlen : M.length = M'.length + 1 := by simp [hM]
  have hCM : ∀ r (hr : r < M'.length), C[r]'(by simp [hC]; omega) = M[r]'(by omega) := by
    intro r hr
    simp [hC, hM, List.getElem_append_left hr]
  have hCl : C[M'.length]'(by simp [hC]) = σ' := by simp [hC]
  have hpk : ∀ r (hr : r < M.length), M[r].dl = zPeak e M r ∧ M[r].d = zPeak e M (r + 1) :=
    zPeak_seg e M hl
  have hpk0 : zPeak e M 0 = e := zPeak_zero e M
  have hσdl : σdl = zPeak e M M'.length := by
    have := (hpk M'.length (by omega)).1
    simpa [hM] using this
  -- vertices of `C` reach peaks
  have hreach : ∀ r (hr : r < C.length) {v : A}, v ∈ C[r].verts →
      (v ∈ pathVerts C[r].t → Reaches v (zPeak e M r)) ∧
      (v ∈ pathVerts C[r].s → Reaches v (zPeak e M (if r < M'.length then r + 1 else 0))) := by
    intro r hr v _
    have hCr : r ≤ M'.length := by simp [hC] at hr; omega
    rcases Nat.lt_or_ge r M'.length with h | h
    · rw [hCM r h, if_pos h]
      have := hpk r (by omega)
      exact ⟨fun hv ↦ this.1 ▸ (reaches_of_mem_pathVerts _ hv).2,
        fun hv ↦ this.2 ▸ (reaches_of_mem_pathVerts _ hv).2⟩
    · have hr' : r = M'.length := by omega
      subst hr'
      rw [hCl, if_neg (lt_irrefl _), hpk0]
      refine ⟨fun hv ↦ hσdl ▸ (reaches_of_mem_pathVerts σt hv).2, fun hv ↦ ?_⟩
      change v ∈ pathVerts (σs.comp p) at hv
      rw [pathVerts_comp] at hv
      rcases hv with hv | hv
      · exact (reaches_of_mem_pathVerts σs hv).2.trans ⟨p⟩
      · exact (reaches_of_mem_pathVerts p hv).2
  have hM'pos : 0 < M'.length := List.length_pos_of_ne_nil hne
  -- the contradiction from a comparison with the peak at an inner position
  have hcon : ∀ k x, 1 ≤ k → k ≤ M'.length → x ≤ M'.length + 1 → x ≠ k →
      Reaches (zPeak e M k) (zPeak e M x) → False := by
    intro k x hk1 hk2 hx hxk h
    rcases Nat.lt_or_gt_of_ne hxk with hlt | hgt
    · exact (hinc x k hlt (by omega) (by omega)).2 h
    · exact (hinc k x hgt hx (by omega)).1 h
  -- the hull of `C` lies in `Hb`
  have hσM : (⟨σc, σdl, σd, σt, σs⟩ : ZSeg A) ∈ M := by simp [hM]
  have hCV : segsVerts C ⊆ Hb := by
    intro v hv
    obtain ⟨r, hr, hvr⟩ := exists_idx_of_mem_segsVerts hv
    have hCr : r ≤ M'.length := by simp [hC] at hr; omega
    rcases Nat.lt_or_ge r M'.length with h | h
    · rw [hCM r h] at hvr
      exact hV (mem_segsVerts (List.getElem_mem _) hvr)
    · have hr' : r = M'.length := by omega
      subst hr'
      rw [hCl] at hvr
      rcases hvr with hv' | hv'
      · exact hV (mem_segsVerts hσM (Or.inl hv'))
      · change v ∈ pathVerts (σs.comp p) at hv'
        rw [pathVerts_comp] at hv'
        rcases hv' with hv' | hv'
        · exact hV (mem_segsVerts hσM (Or.inr hv'))
        · obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p hv'
          exact hHb _ (hV (mem_segsVerts hσM (Or.inr (mem_pathVerts_end σs)))) _ he _ h1 h2
  have hHC : hullOf (segsVerts C) ⊆ Hb := hullOf_subset hHb hCV
  -- the cycle conditions
  have hposC : ∀ ρ ∈ C, 0 < ρ.s.length ∧ 0 < ρ.t.length := by
    intro ρ hρ
    rcases List.mem_append.1 hρ with h | h
    · exact hpos ρ (List.mem_append_left _ h)
    · rw [List.mem_singleton] at h
      subst h
      have := hpos _ hσM
      refine ⟨?_, this.2⟩
      change 0 < (σs.comp p).length
      rw [Quiver.Path.length_comp]
      exact Nat.lt_of_lt_of_le this.1 (Nat.le_add_right _ _)
  have hsepC : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      C = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ → q ≠ e →
        ¬SepComp (hullOf (segsVerts C)) q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ ∧
        q ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts (L₂ ++ L₁) := by
    intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit hqe
    have hClen' : C.length = M'.length + 1 := by simp [hC]
    have hClen : C.length = L₁.length + 2 + L₂.length := by rw [hsplit]; simp; omega
    have hCm : C[L₁.length]'(by omega) = ⟨c, dl, q, t, s₀.cons e₁⟩ := by
      simp only [hsplit, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
    have hCm1 : C[L₁.length + 1]'(by omega) = ⟨c', q, d', t₀.cons e₂, s'⟩ := by
      rw [List.getElem_of_eq hsplit]
      simp [List.getElem_append_right (Nat.le_succ L₁.length)]
    have hmlt : L₁.length < M'.length := by omega
    have hq : q = zPeak e M (L₁.length + 1) := by
      have := (hpk L₁.length (by omega)).2
      rw [← hCM L₁.length hmlt, hCm] at this
      exact this
    have hsM := split_two M L₁.length (by omega)
    have hMm : M[L₁.length]'(by omega) = ⟨c, dl, q, t, s₀.cons e₁⟩ := by rw [← hCM _ hmlt, hCm]
    have hns : ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
      rcases Nat.lt_or_ge (L₁.length + 1) M'.length with h | h
      · have hMm1 : M[L₁.length + 1]'(by omega) = ⟨c', q, d', t₀.cons e₂, s'⟩ := by
          rw [← hCM _ h, hCm1]
        rw [hMm, hMm1] at hsM
        exact hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsM
      · have hm1 : L₁.length + 1 = M'.length := by omega
        have h2 : C[M'.length]'(by omega) = ⟨c', q, d', t₀.cons e₂, s'⟩ := by
          convert hCm1 using 2
          omega
        have hσeq := hCl.symm.trans h2
        simp only [hσ', ZSeg.mk.injEq] at hσeq
        obtain ⟨rfl, rfl, rfl, h4, -⟩ := hσeq
        have h4' := eq_of_heq h4
        have hMm1 : M[L₁.length + 1]'(by omega) = ⟨σc, σdl, σd, t₀.cons e₂, σs⟩ := by
          rw [← h4']
          simp [hM, hm1]
        rw [hMm, hMm1] at hsM
        exact hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsM
    refine ⟨fun h ↦ hns (SepComp.mono hHC h), ?_⟩
    intro hqv
    rcases hqv with (hv | hv) | hv
    · have := (hreach L₁.length (by omega) (v := q) (by rw [hCm]; exact Or.inl hv)).1
        (by rw [hCm]; exact hv)
      rw [hq] at this
      exact hcon (L₁.length + 1) L₁.length (by omega) (by omega) (by omega) (by omega) this
    · have := (hreach (L₁.length + 1) (by omega) (v := q) (by rw [hCm1]; exact Or.inr hv)).2
        (by rw [hCm1]; exact hv)
      rw [hq] at this
      split_ifs at this with h
      · exact hcon (L₁.length + 1) (L₁.length + 1 + 1) (by omega) (by omega) (by omega)
          (by omega) this
      · exact hcon (L₁.length + 1) 0 (by omega) (by omega) (by omega) (by omega) this
    · obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
      obtain ⟨r, hr, hCr, hrm, hrm1⟩ : ∃ r, ∃ hr : r < C.length, C[r] = ρ ∧ r ≠ L₁.length ∧
          r ≠ L₁.length + 1 := by
        rcases List.mem_append.1 hρ with h | h
        · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
          refine ⟨L₁.length + 2 + r', by omega, ?_, by omega, by omega⟩
          simp only [hsplit, List.getElem_append_right (show L₁.length ≤ L₁.length + 2 + r' by omega)]
          simp [show L₁.length + 2 + r' - L₁.length = r' + 2 by omega]
        · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
          exact ⟨r', by omega, by simp [hsplit, List.getElem_append_left hr'], by omega, by omega⟩
      rcases hvρ with hv' | hv'
      · have := (hreach r hr (v := q) (by rw [hCr]; exact Or.inl hv')).1 (by rw [hCr]; exact hv')
        rw [hq] at this
        exact hcon (L₁.length + 1) r (by omega) (by omega) (by omega) (by omega) this
      · have := (hreach r hr (v := q) (by rw [hCr]; exact Or.inr hv')).2 (by rw [hCr]; exact hv')
        rw [hq] at this
        split_ifs at this with h
        · exact hcon (L₁.length + 1) (r + 1) (by omega) (by omega) (by omega) (by omega) this
        · exact hcon (L₁.length + 1) 0 (by omega) (by omega) (by omega) (by omega) this
  obtain ⟨τ, M'', hτ⟩ := List.exists_cons_of_ne_nil hne
  have hτC : τ ∈ C := by rw [hC, hτ]; simp
  have key := cyc_top hcf hint hsc hlC hcC (by simp [hC]) hsepC hposC
    (mem_segsVerts hτC (Or.inr (mem_pathVerts_end τ.s)))
  have hτd : τ.d = zPeak e M 1 := by
    have := (hpk 0 (by omega)).2
    simpa [hM, hτ] using this
  rw [hτd, ← hpk0] at key
  exact hcon 1 0 (le_refl _) (by omega) (by omega) (by omega) key

/-- Peaks of a reversed list are the original peaks in reverse order. -/
lemma zPeak_reverse {e : A} {L : List (ZSeg A)} (hl : ZLinked e L) {k : ℕ} (hk : k ≤ L.length) :
    zPeak (ZLast e L) (L.reverse.map ZSeg.swap) k = zPeak e L (L.length - k) := by
  set j := L.length - k
  have hsplit : L = L.take j ++ L.drop j := (List.take_append_drop j L).symm
  have hl' : ZLinked (zPeak e L j) (L.drop j) := by
    have := hl
    rw [hsplit, zLinked_append] at this
    exact this.2
  have hlast : ZLast e L = ZLast (zPeak e L j) (L.drop j) := by
    conv_lhs => rw [hsplit]
    rw [zLast_append]
    rfl
  have htake : (L.reverse.map ZSeg.swap).take k = (L.drop j).reverse.map ZSeg.swap := by
    rw [List.map_reverse, List.take_reverse, List.length_map, ← List.map_drop, List.map_reverse]
  rw [zPeak, htake, hlast]
  exact (zLinked_reverse _ _ hl').2

lemma ZSeg.swap_swap (σ : ZSeg A) : σ.swap.swap = σ := rfl

lemma zLast_mem_segsVerts : ∀ (e : A) (L : List (ZSeg A)), L ≠ [] → ZLast e L ∈ segsVerts L
  | _, [], h => absurd rfl h
  | _, [σ], _ => mem_segsVerts (List.mem_singleton_self σ) (Or.inr (mem_pathVerts_end σ.s))
  | _, σ :: τ :: L, _ => by
    have := zLast_mem_segsVerts σ.d (τ :: L) (List.cons_ne_nil _ _)
    obtain ⟨ρ, hρ, hv⟩ := Set.mem_iUnion₂.1 this
    exact mem_segsVerts (List.mem_cons_of_mem _ hρ) hv

lemma segsVerts_reverse_swap (L : List (ZSeg A)) :
    segsVerts (L.reverse.map ZSeg.swap) = segsVerts L := by
  ext v
  simp only [segsVerts, Set.mem_iUnion, List.mem_map, List.mem_reverse, exists_prop]
  constructor
  · rintro ⟨_, ⟨ρ, hρ, rfl⟩, hv⟩
    exact ⟨ρ, hρ, by rwa [ZSeg.verts_swap] at hv⟩
  · rintro ⟨ρ, hρ, hv⟩
    exact ⟨ρ.swap, ⟨ρ, hρ, rfl⟩, by rwa [ZSeg.verts_swap]⟩

/-- `closeB` for a list of length at least two. -/
theorem closeB' (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {L : List (ZSeg A)} (hlen : 2 ≤ L.length)
    (hl : ZLinked e L) (hV : segsVerts L ⊆ Hb) (he : e ∈ Hb)
    (hinc : ∀ a b, a < b → b ≤ L.length → ¬(a = 0 ∧ b = L.length) →
      ¬Reaches (zPeak e L a) (zPeak e L b) ∧ ¬Reaches (zPeak e L b) (zPeak e L a))
    (hsep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      L = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩)
    (hpos : ∀ ρ ∈ L, 0 < ρ.s.length ∧ 0 < ρ.t.length) (hp : Reaches (ZLast e L) e) : False := by
  rcases List.eq_nil_or_concat' L with rfl | ⟨M', σ, rfl⟩
  · simp at hlen
  have hne : M' ≠ [] := by rintro rfl; simp at hlen
  have hlen' : (M' ++ [σ]).length = M'.length + 1 := by simp
  rw [hlen'] at hinc
  rw [zLast_concat] at hp
  exact closeB hcf hint hsc hHb hne hl hV he hinc hsep hpos hp

/-- **The mirror of `closeB`**: no path from the first peak to the last. -/
theorem closeA (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {L : List (ZSeg A)} (hlen : 2 ≤ L.length)
    (hl : ZLinked e L) (hV : segsVerts L ⊆ Hb)
    (hinc : ∀ a b, a < b → b ≤ L.length → ¬(a = 0 ∧ b = L.length) →
      ¬Reaches (zPeak e L a) (zPeak e L b) ∧ ¬Reaches (zPeak e L b) (zPeak e L a))
    (hsep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      L = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩)
    (hpos : ∀ ρ ∈ L, 0 < ρ.s.length ∧ 0 < ρ.t.length) (hp : Reaches e (ZLast e L)) : False := by
  have hLne : L ≠ [] := by rintro rfl; simp at hlen
  obtain ⟨hlR, hcR⟩ := zLinked_reverse e L hl
  set R := L.reverse.map ZSeg.swap with hR
  have hRlen : R.length = L.length := by simp [hR]
  have hLR : L = (R.map ZSeg.swap).reverse := by
    simp [hR, List.map_reverse, List.map_map, Function.comp_def, ZSeg.swap_swap]
  refine closeB' hcf hint hsc hHb (e := ZLast e L) (L := R) (by omega) hlR
    (by rw [hR, segsVerts_reverse_swap]; exact hV) (hV (zLast_mem_segsVerts e L hLne)) ?_ ?_ ?_
    (by rw [hcR]; exact hp)
  · intro a b hab hb hab'
    rw [hRlen] at hb hab'
    rw [zPeak_reverse hl (by omega), zPeak_reverse hl (by omega)]
    obtain ⟨h1, h2⟩ := hinc (L.length - b) (L.length - a) (by omega) (by omega) (by omega)
    exact ⟨h2, h1⟩
  · intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
    have hL : L = (L₂.map ZSeg.swap).reverse ++ ⟨c', d', q, s', t₀.cons e₂⟩ ::
        ⟨c, q, dl, s₀.cons e₁, t⟩ :: (L₁.map ZSeg.swap).reverse := by
      rw [hLR, hsplit]
      simp [ZSeg.swap]
    exact fun h ↦ hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL (Relation.EqvGen.symm _ _ h)
  · intro ρ hρ
    obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.1 hρ
    have := hpos ρ' (List.mem_reverse.1 hρ')
    exact ⟨this.2, this.1⟩

/-- The sublist between positions `a` and `b`. -/
def zSub (L : List (ZSeg A)) (a b : ℕ) : List (ZSeg A) := (L.drop a).take (b - a)

lemma zSub_split (L : List (ZSeg A)) {a b : ℕ} (hab : a ≤ b) :
    L = L.take a ++ zSub L a b ++ L.drop b := by
  conv_lhs => rw [← List.take_append_drop a L, ← List.take_append_drop (b - a) (L.drop a)]
  rw [List.drop_drop, List.append_assoc, zSub, show a + (b - a) = b by omega]

lemma mem_of_mem_zSub {L : List (ZSeg A)} {a b : ℕ} {ρ : ZSeg A} (h : ρ ∈ zSub L a b) : ρ ∈ L :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

lemma zSub_length {L : List (ZSeg A)} {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L.length) :
    (zSub L a b).length = b - a := by
  simp [zSub]; omega

lemma zLinked_zSub {e : A} {L : List (ZSeg A)} (hl : ZLinked e L) (a b : ℕ) :
    ZLinked (zPeak e L a) (zSub L a b) := by
  have h1 := hl
  rw [← List.take_append_drop a L, zLinked_append] at h1
  have h2 := h1.2
  rw [← List.take_append_drop (b - a) (L.drop a), zLinked_append] at h2
  exact h2.1

lemma zPeak_zSub (e : A) (L : List (ZSeg A)) {a b i : ℕ} (hi : i ≤ b - a) :
    zPeak (zPeak e L a) (zSub L a b) i = zPeak e L (a + i) := by
  simp only [zPeak, zSub, List.take_take, Nat.min_eq_left hi, List.take_add, zLast_append]

lemma segsVerts_mono {L L' : List (ZSeg A)} (h : ∀ ρ ∈ L, ρ ∈ L') : segsVerts L ⊆ segsVerts L' :=
  fun _ hv ↦ by
    obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
    exact mem_segsVerts (h ρ hρ) hvρ

/-- **Peaks of a linked list are pairwise incomparable** when consecutive peaks are
incomparable and every inner peak is separating (Fischbacher, property (4)). -/
theorem zPeak_incomp (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {L : List (ZSeg A)}
    (hl : ZLinked e L) (hV : segsVerts L ⊆ Hb) (he : e ∈ Hb)
    (hadj : ∀ σ ∈ L, ¬Reaches σ.dl σ.d ∧ ¬Reaches σ.d σ.dl)
    (hsep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      L = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩)
    (hpos : ∀ ρ ∈ L, 0 < ρ.s.length ∧ 0 < ρ.t.length) :
    ∀ a b, a < b → b ≤ L.length →
      ¬Reaches (zPeak e L a) (zPeak e L b) ∧ ¬Reaches (zPeak e L b) (zPeak e L a) := by
  have hpk := zPeak_seg e L hl
  have hmem : ∀ a, a ≤ L.length → zPeak e L a ∈ Hb := by
    intro a ha
    rcases a with _ | a
    · rw [zPeak_zero]; exact he
    · rw [← (hpk a (by omega)).2]
      exact hV (mem_segsVerts (List.getElem_mem _) (Or.inr (mem_pathVerts_end _)))
  suffices H : ∀ m a, 1 ≤ m → a + m ≤ L.length →
      ¬Reaches (zPeak e L a) (zPeak e L (a + m)) ∧ ¬Reaches (zPeak e L (a + m)) (zPeak e L a) by
    intro a b hab hb
    have := H (b - a) a (by omega) (by omega)
    rwa [show a + (b - a) = b by omega] at this
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hm ham
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    have := hadj _ (List.getElem_mem (show a < L.length by omega))
    rwa [(hpk a (by omega)).1, (hpk a (by omega)).2] at this
  -- the sublist between the two peaks
  set S := zSub L a (a + m) with hS
  have hSlen : S.length = m := by rw [hS, zSub_length (by omega) ham]; omega
  have hlS := zLinked_zSub hl a (a + m)
  have hpS : ∀ i, i ≤ m → zPeak (zPeak e L a) S i = zPeak e L (a + i) :=
    fun i hi ↦ zPeak_zSub e L (by omega)
  have hlastS : ZLast (zPeak e L a) S = zPeak e L (a + m) := by
    rw [← hpS m le_rfl, ← hSlen, zPeak_length]
  have hVS : segsVerts S ⊆ Hb := (segsVerts_mono fun _ h ↦ mem_of_mem_zSub h).trans hV
  have hincS : ∀ i j, i < j → j ≤ S.length → ¬(i = 0 ∧ j = S.length) →
      ¬Reaches (zPeak (zPeak e L a) S i) (zPeak (zPeak e L a) S j) ∧
        ¬Reaches (zPeak (zPeak e L a) S j) (zPeak (zPeak e L a) S i) := by
    intro i j hij hj hij'
    rw [hSlen] at hj hij'
    rw [hpS i (by omega), hpS j hj]
    have := ih (j - i) (by omega) (a + i) (by omega) (by omega)
    rwa [show a + i + (j - i) = a + j by omega] at this
  have hsepS : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      S = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
    intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
    have hL : L = (L.take a ++ L₁) ++ ⟨c, dl, q, t, s₀.cons e₁⟩ ::
        ⟨c', q, d', t₀.cons e₂, s'⟩ :: (L₂ ++ L.drop (a + m)) := by
      conv_lhs => rw [zSub_split L (show a ≤ a + m by omega), ← hS, hsplit]
      simp
    exact hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL
  have hposS : ∀ ρ ∈ S, 0 < ρ.s.length ∧ 0 < ρ.t.length := fun ρ h ↦ hpos ρ (mem_of_mem_zSub h)
  constructor
  · intro hr
    rw [← hlastS] at hr
    exact closeA hcf hint hsc hHb (L := S) (by rw [hSlen]; omega) hlS hVS hincS hsepS hposS hr
  · intro hr
    rw [← hlastS] at hr
    exact closeB' hcf hint hsc hHb (L := S) (by rw [hSlen]; omega) hlS hVS (hmem a (by omega)) hincS hsepS hposS hr

/-- **The peaks of a good walk are pairwise incomparable** (Fischbacher, proof of Lemma 5.2,
property (4)). -/
theorem ZWalk.Good.zPeak_incomp
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w)
    {i j : ℕ} (hij : i < j) (hj : j ≤ z.segs.length) :
    ¬Reaches (zPeak z.d₀ z.segs i) (zPeak z.d₀ z.segs j) ∧
      ¬Reaches (zPeak z.d₀ z.segs j) (zPeak z.d₀ z.segs i) :=
  RayCat.zPeak_incomp hcf hint hsc z.convexR_hull z.linked
    (fun v hv ↦ z.verts_subset_hull (Or.inr hv))
    (z.verts_subset_hull (Or.inl (Or.inl (mem_pathVerts_start z.v'))))
    hz.incomp hz.sep (fun ρ h ↦ ⟨hz.spos ρ h, hz.tpos ρ h⟩) i j hij hj

/-- Every inner peak of a segment list is separating in `Hb`. -/
def SepAll (Hb : Set A) (L : List (ZSeg A)) : Prop :=
  ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
    (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
    (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
    (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
    L = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
      ¬SepComp Hb q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩

/-- **A cyclic walk with at least two segments**, pairwise incomparable peaks and separating
inner peaks, does not exist. -/
theorem cyc_contra (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {e : A} {C : List (ZSeg A)} (hl : ZLinked e C) (hc : ZLast e C = e) (hlen : 2 ≤ C.length)
    (hinc : ∀ i j, i < j → j < C.length →
      ¬Reaches (zPeak e C i) (zPeak e C j) ∧ ¬Reaches (zPeak e C j) (zPeak e C i))
    (hsep : SepAll (hullOf (segsVerts C)) C)
    (hpos : ∀ ρ ∈ C, 0 < ρ.s.length ∧ 0 < ρ.t.length) : False := by
  have hpk := zPeak_seg e C hl
  have hwrap : zPeak e C C.length = zPeak e C 0 := by rw [zPeak_length, hc, zPeak_zero]
  have hcon : ∀ k x, k < C.length → x < C.length → x ≠ k →
      Reaches (zPeak e C k) (zPeak e C x) → False := by
    intro k x hk hx hxk h
    rcases Nat.lt_or_gt_of_ne hxk with hlt | hgt
    · exact (hinc x k hlt hk).2 h
    · exact (hinc k x hgt hx).1 h
  have hreach : ∀ r (hr : r < C.length) {v : A},
      (v ∈ pathVerts C[r].t → Reaches v (zPeak e C r)) ∧
      (v ∈ pathVerts C[r].s → Reaches v (zPeak e C (if r + 1 < C.length then r + 1 else 0))) := by
    intro r hr v
    refine ⟨fun hv ↦ (hpk r hr).1 ▸ (reaches_of_mem_pathVerts _ hv).2, fun hv ↦ ?_⟩
    have h := (hpk r hr).2 ▸ (reaches_of_mem_pathVerts _ hv).2
    split_ifs with h'
    · exact h
    · rwa [show r + 1 = C.length by omega, hwrap] at h
  have hsepC : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      C = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ → q ≠ e →
        ¬SepComp (hullOf (segsVerts C)) q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ ∧
        q ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts (L₂ ++ L₁) := by
    intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit _
    have hClen : C.length = L₁.length + 2 + L₂.length := by rw [hsplit]; simp; omega
    have hCm : C[L₁.length]'(by omega) = ⟨c, dl, q, t, s₀.cons e₁⟩ := by
      simp only [hsplit, List.getElem_append_right (le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
    have hCm1 : C[L₁.length + 1]'(by omega) = ⟨c', q, d', t₀.cons e₂, s'⟩ := by
      rw [List.getElem_of_eq hsplit]
      simp [List.getElem_append_right (Nat.le_succ L₁.length)]
    have hq : q = zPeak e C (L₁.length + 1) := by
      have := (hpk L₁.length (by omega)).2
      rw [hCm] at this
      exact this
    refine ⟨hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsplit, ?_⟩
    intro hqv
    rcases hqv with (hv | hv) | hv
    · have := (hreach L₁.length (by omega) (v := q)).1 (by rw [hCm]; exact hv)
      rw [hq] at this
      exact hcon (L₁.length + 1) L₁.length (by omega) (by omega) (by omega) this
    · have := (hreach (L₁.length + 1) (by omega) (v := q)).2 (by rw [hCm1]; exact hv)
      rw [hq] at this
      split_ifs at this with h
      · exact hcon (L₁.length + 1) (L₁.length + 1 + 1) (by omega) h (by omega) this
      · exact hcon (L₁.length + 1) 0 (by omega) (by omega) (by omega) this
    · obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
      obtain ⟨r, hr, hCr, hrm, hrm1⟩ : ∃ r, ∃ hr : r < C.length, C[r] = ρ ∧ r ≠ L₁.length ∧
          r ≠ L₁.length + 1 := by
        rcases List.mem_append.1 hρ with h | h
        · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
          refine ⟨L₁.length + 2 + r', by omega, ?_, by omega, by omega⟩
          simp only [hsplit,
            List.getElem_append_right (show L₁.length ≤ L₁.length + 2 + r' by omega)]
          simp [show L₁.length + 2 + r' - L₁.length = r' + 2 by omega]
        · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
          exact ⟨r', by omega, by simp [hsplit, List.getElem_append_left hr'], by omega,
            by omega⟩
      rcases hvρ with hv' | hv'
      · have := (hreach r hr (v := q)).1 (by rw [hCr]; exact hv')
        rw [hq] at this
        exact hcon (L₁.length + 1) r (by omega) hr (by omega) this
      · have := (hreach r hr (v := q)).2 (by rw [hCr]; exact hv')
        rw [hq] at this
        split_ifs at this with h
        · exact hcon (L₁.length + 1) (r + 1) (by omega) h (by omega) this
        · exact hcon (L₁.length + 1) 0 (by omega) (by omega) (by omega) this
  have hne : C ≠ [] := by rintro rfl; simp at hlen
  have h0 : 0 < C.length := by omega
  have key := cyc_top hcf hint hsc hl hc hne hsepC hpos
    (mem_segsVerts (List.getElem_mem h0) (Or.inr (mem_pathVerts_end (C[0]'h0).s)))
  have key' : Reaches (zPeak e C 1) (zPeak e C 0) := by
    rw [zPeak_zero, ← (hpk 0 h0).2]; exact key
  exact hcon 1 0 (by omega) h0 (by omega) key'

/-- **A one-segment cyclic walk**: its peak is not separating. -/
theorem cyc_contra1 (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {c q : A} {x₁ x₂ : RayVert A} {s₀ : Quiver.Path (RayVert.mk c) x₁}
    {e₁ : x₁ ⟶ RayVert.mk q} {t₀ : Quiver.Path (RayVert.mk c) x₂} {e₂ : x₂ ⟶ RayVert.mk q}
    (hns : ¬SepComp (hullOf (segsVerts [⟨c, q, q, t₀.cons e₂, s₀.cons e₁⟩])) q
      ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩) : False := by
  set σ : ZSeg A := ⟨c, q, q, t₀.cons e₂, s₀.cons e₁⟩ with hσ
  have hl : ZLinked q [σ] := ⟨rfl, trivial⟩
  have hc : ZLast q [σ] = q := rfl
  obtain ⟨M₁, M₂, π, hsplit, -, hmax⟩ := exists_max_peak hcf hint hl hc (List.cons_ne_nil _ _)
    (mem_segsVerts (List.mem_singleton_self σ) (Or.inr (mem_pathVerts_end σ.s)))
  have hπ : π = σ := by
    rcases M₁ with _ | ⟨_, M₁⟩
    · simp at hsplit; exact hsplit.1.symm
    · simp at hsplit
  subst hπ
  have hfin : (segsVerts [σ]).Finite :=
    [σ].finite_toSet.biUnion fun ρ _ ↦ (pathVerts_finite ρ.t).union (pathVerts_finite ρ.s)
  have hav : q ∉ pathVerts s₀ ∪ pathVerts t₀ := by
    rintro (hq | hq)
    · obtain ⟨p₁⟩ := (reaches_of_mem_pathVerts s₀ hq).2
      have := hcf q (p₁.cons e₁)
      simp at this
    · obtain ⟨p₂⟩ := (reaches_of_mem_pathVerts t₀ hq).2
      have := hcf q (p₂.cons e₂)
      simp at this
  have hV : σ.verts ⊆ hullOf (segsVerts [σ]) :=
    fun x hx ↦ subset_hullOf _ (mem_segsVerts (List.mem_singleton_self σ) hx)
  exact hns (sepComp_front1 (finite_hullOf hint hfin) (convexR_hullOf _)
    (hsc _ (finite_hullOf hint hfin) (convexR_hullOf _)) hV hav hmax)

/-- **No path from an earlier valley to a later one** in a linked list with pairwise incomparable
peaks and separating inner peaks (Fischbacher, property (5), first half). -/
theorem valley_fwd (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {L : List (ZSeg A)} (hl : ZLinked e L)
    (hV : segsVerts L ⊆ Hb)
    (hinc : ∀ i j, i < j → j ≤ L.length →
      ¬Reaches (zPeak e L i) (zPeak e L j) ∧ ¬Reaches (zPeak e L j) (zPeak e L i))
    (hsep : SepAll Hb L) (hpos : ∀ ρ ∈ L, 0 < ρ.s.length ∧ 0 < ρ.t.length)
    {a b : ℕ} (hab : a < b) (hb : b < L.length) (hp : Reaches (L[a]'(by omega)).c L[b].c) :
    False := by
  have hal : a < L.length := by omega
  have hpk := zPeak_seg e L hl
  have hda := (hpk a hal).2
  have hdlb := (hpk b hb).1
  have hsplitL : L = L.take a ++ L[a] :: (zSub L (a + 1) b ++ L[b] :: L.drop (b + 1)) := by
    have h1 := zSub_split L (show a + 1 ≤ b by omega)
    rw [List.take_succ_eq_append_getElem hal, List.drop_eq_getElem_cons hb] at h1
    exact h1.trans (by simp only [List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append])
  set mid := zSub L (a + 1) b with hmid
  have hmidlen : mid.length = b - (a + 1) := zSub_length (by omega) (by omega)
  have hlmid : ZLinked (zPeak e L (a + 1)) mid := zLinked_zSub hl (a + 1) b
  have hpmid : ∀ i, i ≤ b - (a + 1) →
      zPeak (zPeak e L (a + 1)) mid i = zPeak e L (a + 1 + i) := fun i hi ↦ zPeak_zSub e L hi
  have hlastmid : ZLast (zPeak e L (a + 1)) mid = zPeak e L b := by
    rw [← zPeak_length, hmidlen, hpmid _ le_rfl]; congr 1; omega
  have hmidL : ∀ ρ ∈ mid, ρ ∈ L := fun ρ h ↦ mem_of_mem_zSub h
  rcases ha' : L[a] with ⟨ca, dla, da, ta, sa⟩
  rcases hb' : L[b] with ⟨cb, dlb, db, tb, sb⟩
  rw [ha', hb'] at hp
  rw [ha', hb'] at hsplitL
  rw [ha'] at hda
  rw [hb'] at hdlb
  change da = _ at hda
  change dlb = _ at hdlb
  obtain ⟨p⟩ := hp
  have hσa : (⟨ca, dla, da, ta, sa⟩ : ZSeg A) ∈ L := by rw [← ha']; exact List.getElem_mem _
  have hσb : (⟨cb, dlb, db, tb, sb⟩ : ZSeg A) ∈ L := by rw [← hb']; exact List.getElem_mem _
  have hcaH : ca ∈ Hb := hV (mem_segsVerts hσa (Or.inr (mem_pathVerts_start sa)))
  have hcbH : cb ∈ Hb := hV (mem_segsVerts hσb (Or.inl (mem_pathVerts_start tb)))
  have hCV : ∀ M : List (ZSeg A), (∀ ρ ∈ M, ρ ∈ L) →
      segsVerts ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: M) ⊆ Hb := by
    intro M hM v hv
    obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hv
    rcases List.mem_cons.1 hρ with rfl | hρ
    · rcases hvρ with hv' | hv'
      · change v ∈ pathVerts (p.comp tb) at hv'
        rw [pathVerts_comp] at hv'
        rcases hv' with hv' | hv'
        · obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p hv'
          exact hHb _ hcaH _ hcbH _ h1 h2
        · exact hV (mem_segsVerts hσb (Or.inl hv'))
      · exact hV (mem_segsVerts hσa (Or.inr hv'))
    · exact hV (mem_segsVerts (hM ρ hρ) hvρ)
  have hposC : ∀ M : List (ZSeg A), (∀ ρ ∈ M, ρ ∈ L) →
      ∀ ρ ∈ (⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: M, 0 < ρ.s.length ∧ 0 < ρ.t.length := by
    intro M hM ρ hρ
    rcases List.mem_cons.1 hρ with rfl | hρ
    · refine ⟨(hpos _ hσa).1, ?_⟩
      change 0 < (p.comp tb).length
      rw [Quiver.Path.length_comp]
      have := (hpos _ hσb).2
      change 0 < tb.length at this
      omega
    · exact hpos ρ (hM ρ hρ)
  rcases Nat.lt_or_ge (a + 1) b with hab2 | hab1
  · -- at least two segments: `cyc_contra`
    have hlen : 2 ≤ ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid).length := by
      simp only [List.length_cons]; omega
    have hlC : ZLinked dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) := by
      refine ⟨rfl, ?_⟩
      change ZLinked da mid
      rw [hda]; exact hlmid
    have hcC : ZLast dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) = dlb := by
      change ZLast da mid = dlb
      rw [hda, hlastmid, hdlb]
    have hpC0 : zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) 0 = zPeak e L b := by
      rw [zPeak_zero, hdlb]
    have hpCs : ∀ i, i ≤ b - (a + 1) →
        zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) (i + 1) =
          zPeak e L (a + 1 + i) := by
      intro i hi
      change zPeak da mid i = _
      rw [hda]; exact hpmid i hi
    have hincC : ∀ i j, i < j → j < ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid).length →
        ¬Reaches (zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) i)
            (zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) j) ∧
          ¬Reaches (zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) j)
            (zPeak dlb ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) i) := by
      intro i j hij hj
      simp only [List.length_cons] at hj
      rcases j with _ | j
      · omega
      rw [hpCs j (by omega)]
      rcases i with _ | i
      · rw [hpC0]
        have := hinc (a + 1 + j) b (by omega) (by omega)
        exact ⟨this.2, this.1⟩
      · rw [hpCs i (by omega)]
        exact hinc (a + 1 + i) (a + 1 + j) (by omega) (by omega)
    have hHC := hullOf_subset hHb (hCV mid hmidL)
    have hsepC : SepAll (hullOf (segsVerts ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid)))
        ((⟨ca, dlb, da, p.comp tb, sa⟩ : ZSeg A) :: mid) := by
      intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit h
      rcases L₁ with _ | ⟨ρ₀, L₁'⟩
      · simp only [List.nil_append, List.cons.injEq, ZSeg.mk.injEq] at hsplit
        obtain ⟨⟨rfl, rfl, rfl, -, hs⟩, hmid'⟩ := hsplit
        obtain rfl := eq_of_heq hs
        rw [hmid', List.cons_append] at hsplitL
        exact hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsplitL (SepComp.mono hHC h)
      · simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨-, hmid'⟩ := hsplit
        rw [hmid'] at hsplitL
        have hL2 : L = (L.take a ++ ⟨ca, dla, da, ta, sa⟩ :: L₁') ++ ⟨c, dl, q, t, s₀.cons e₁⟩ ::
            ⟨c', q, d', t₀.cons e₂, s'⟩ :: (L₂ ++ ⟨cb, dlb, db, tb, sb⟩ :: L.drop (b + 1)) :=
          hsplitL.trans (by simp)
        exact hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL2 (SepComp.mono hHC h)
    exact cyc_contra hcf hint hsc hlC hcC hlen hincC hsepC (hposC mid hmidL)
  · -- one segment: `cyc_contra1`
    have hb1 : b = a + 1 := by omega
    have hmid0 : mid = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hdd : dlb = da := by rw [hdlb, hda, hb1]
    subst hdd
    obtain ⟨x₁, s₀, e₁, rfl⟩ : ∃ (x₁ : RayVert A) (s₀ : Quiver.Path (RayVert.mk ca) x₁)
        (e₁ : x₁ ⟶ RayVert.mk dlb), sa = s₀.cons e₁ := by
      rcases sa with _ | ⟨s₀, e₁⟩
      · exact absurd (hpos _ hσa).1 (lt_irrefl 0)
      · exact ⟨_, s₀, e₁, rfl⟩
    obtain ⟨x₂, t₀, e₂, rfl⟩ : ∃ (x₂ : RayVert A) (t₀ : Quiver.Path (RayVert.mk cb) x₂)
        (e₂ : x₂ ⟶ RayVert.mk dlb), tb = t₀.cons e₂ := by
      rcases tb with _ | ⟨t₀, e₂⟩
      · exact absurd (hpos _ hσb).2 (lt_irrefl 0)
      · exact ⟨_, t₀, e₂, rfl⟩
    rw [hmid0] at hsplitL
    have hL2 : L = L.take a ++ ⟨ca, dla, dlb, ta, s₀.cons e₁⟩ ::
        ⟨cb, dlb, db, t₀.cons e₂, sb⟩ :: L.drop (b + 1) := hsplitL.trans (by simp)
    have hns := hsep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL2
    have hHC := hullOf_subset hHb (hCV [] (by simp))
    exact cyc_contra1 hcf hint hsc (t₀ := p.comp t₀) (fun h ↦ hns (SepComp.mono hHC h))

lemma sepAll_reverse {Hb : Set A} {L : List (ZSeg A)} (h : SepAll Hb L) :
    SepAll Hb (L.reverse.map ZSeg.swap) := by
  intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
  have hLR : L = ((L.reverse.map ZSeg.swap).map ZSeg.swap).reverse := by
    simp [List.map_reverse, List.map_map, Function.comp_def, ZSeg.swap_swap]
  have hL : L = (L₂.map ZSeg.swap).reverse ++ ⟨c', d', q, s', t₀.cons e₂⟩ ::
      ⟨c, q, dl, s₀.cons e₁, t⟩ :: (L₁.map ZSeg.swap).reverse := by
    rw [hLR, hsplit]
    simp [ZSeg.swap]
  exact fun h' ↦ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL (Relation.EqvGen.symm _ _ h')

lemma getElem_reverse_swap (L : List (ZSeg A)) {i : ℕ} (hi : i < L.length) :
    (L.reverse.map ZSeg.swap)[i]'(by simpa using hi) = (L[L.length - 1 - i]'(by omega)).swap := by
  simp [List.getElem_reverse]

/-- **No path from a later valley to an earlier one** (property (5), second half). -/
theorem valley_bwd (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {Hb : Set A} (hHb : ConvexR Hb) {e : A} {L : List (ZSeg A)} (hl : ZLinked e L)
    (hV : segsVerts L ⊆ Hb)
    (hinc : ∀ i j, i < j → j ≤ L.length →
      ¬Reaches (zPeak e L i) (zPeak e L j) ∧ ¬Reaches (zPeak e L j) (zPeak e L i))
    (hsep : SepAll Hb L) (hpos : ∀ ρ ∈ L, 0 < ρ.s.length ∧ 0 < ρ.t.length)
    {a b : ℕ} (hab : a < b) (hb : b < L.length) (hp : Reaches L[b].c (L[a]'(by omega)).c) :
    False := by
  obtain ⟨hlR, -⟩ := zLinked_reverse e L hl
  have hRlen : (L.reverse.map ZSeg.swap).length = L.length := by simp
  refine valley_fwd hcf hint hsc hHb hlR (by rw [segsVerts_reverse_swap]; exact hV) ?_
    (sepAll_reverse hsep) ?_ (a := L.length - 1 - b) (b := L.length - 1 - a) (by omega)
    (by omega) ?_
  · intro i j hij hj
    rw [hRlen] at hj
    rw [zPeak_reverse hl (by omega), zPeak_reverse hl (by omega)]
    obtain ⟨h1, h2⟩ := hinc (L.length - j) (L.length - i) (by omega) (by omega)
    exact ⟨h2, h1⟩
  · intro ρ hρ
    obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.1 hρ
    have := hpos ρ' (List.mem_reverse.1 hρ')
    exact ⟨this.2, this.1⟩
  · rw [getElem_reverse_swap L (by omega), getElem_reverse_swap L (by omega)]
    have h1 : L.length - 1 - (L.length - 1 - b) = b := by omega
    have h2 : L.length - 1 - (L.length - 1 - a) = a := by omega
    simp only [h1, h2]
    exact hp

/-- **The valleys of a good walk are pairwise incomparable** (Fischbacher, proof of Lemma 5.2,
property (5)). -/
theorem ZWalk.Good.valley_incomp
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w)
    {i j : ℕ} (hij : i < j) (hj : j < z.segs.length) :
    ¬Reaches (z.segs[i]'(by omega)).c z.segs[j].c ∧ ¬Reaches z.segs[j].c (z.segs[i]'(by omega)).c :=
  have hV : segsVerts z.segs ⊆ z.hull := fun v hv ↦ z.verts_subset_hull (Or.inr hv)
  have hinc := fun i j (hij : i < j) (hj : j ≤ z.segs.length) ↦
    hz.zPeak_incomp hcf hint hsc hij hj
  have hpos : ∀ ρ ∈ z.segs, 0 < ρ.s.length ∧ 0 < ρ.t.length :=
    fun ρ h ↦ ⟨hz.spos ρ h, hz.tpos ρ h⟩
  ⟨valley_fwd hcf hint hsc z.convexR_hull z.linked hV hinc hz.sep hpos hij hj,
    valley_bwd hcf hint hsc z.convexR_hull z.linked hV hinc hz.sep hpos hij hj⟩

end LargeIndecomposable.RayCat
