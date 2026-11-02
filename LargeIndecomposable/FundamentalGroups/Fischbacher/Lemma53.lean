module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.ZChain
/-!
# Fischbacher §5.3: the key fact and the case of a common first arrow

For a good walk and a segment with valley `c`, no vertex of the walk outside that segment lies
below `c` (`ZWalk.Good.key`), and on the segment only `c` does. This is the fact (K) behind
Fischbacher's §5.3: after the segment is replaced, `c` leaves the convex hull.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

omit [IsRayCategory A] in
lemma no_pos_cycle (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0) {x y : A} (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) (hp : 0 < p.length)
    (h : Reaches y x) : False := by
  obtain ⟨q⟩ := h
  have := hcf x (p.comp q)
  rw [Quiver.Path.length_comp] at this
  omega

omit [IsRayCategory A] in
/-- Entries of `L₁ ++ L₂` sit at positions other than that of the middle entry. -/
lemma exists_idx_other1 {C L₁ L₂ : List (ZSeg A)} {σ ρ : ZSeg A}
    (hsplit : C = L₁ ++ σ :: L₂) (hρ : ρ ∈ L₁ ++ L₂) :
    ∃ r, ∃ hr : r < C.length, C[r] = ρ ∧ r ≠ L₁.length := by
  have hClen : C.length = L₁.length + 1 + L₂.length := by rw [hsplit]; simp; omega
  rcases List.mem_append.1 hρ with h | h
  · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
    exact ⟨r', by omega, by simp [hsplit, List.getElem_append_left hr'], by omega⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 h
    refine ⟨L₁.length + 1 + r', by omega, ?_, by omega⟩
    simp only [hsplit, List.getElem_append_right (show L₁.length ≤ L₁.length + 1 + r' by omega)]
    simp [show L₁.length + 1 + r' - L₁.length = r' + 1 by omega]

lemma ZSeg.reaches_of_mem_verts {ρ : ZSeg A} {u : A} (hu : u ∈ ρ.verts) : Reaches ρ.c u := by
  rcases hu with hu | hu
  · exact (reaches_of_mem_pathVerts ρ.t hu).1
  · exact (reaches_of_mem_pathVerts ρ.s hu).1

/-- **Key fact (K)**: no vertex of a good walk outside a segment lies below its valley. -/
theorem ZWalk.Good.key (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w)
    {L₁ L₂ : List (ZSeg A)} {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) {u : A}
    (hu : u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂)) (hr : Reaches u σ.c) :
    False := by
  have hlen : z.segs.length = L₁.length + 1 + L₂.length := by rw [hsplit]; simp; omega
  set k := L₁.length with hk
  have hσ : z.segs[k]'(by omega) = σ := by simp [hsplit, hk]
  have hpk := zPeak_seg z.d₀ z.segs z.linked k (by omega)
  rw [hσ] at hpk
  have hσmem : σ ∈ z.segs := by rw [hsplit]; simp
  have ht := hz.tpos σ hσmem
  have hs := hz.spos σ hσmem
  rcases hu with (hu | hu) | hu
  · -- on `v'`
    have h1 := (reaches_of_mem_pathVerts z.v' hu).1
    have h2 : Reaches z.d₀ σ.c := h1.trans hr
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hdl : σ.dl = z.d₀ := by rw [hpk.1, hk0, zPeak_zero]
      have : Reaches σ.dl σ.c := hdl ▸ h2
      exact no_pos_cycle hcf σ.t ht this
    · have h3 : Reaches (zPeak z.d₀ z.segs 0) (zPeak z.d₀ z.segs k) := by
        rw [zPeak_zero, ← hpk.1]
        exact h2.trans ⟨σ.t⟩
      exact (hz.zPeak_incomp hcf hint hsc hk0 (by omega)).1 h3
  · -- on `w'`
    have h1 := (reaches_of_mem_pathVerts z.w' hu).1
    have h2 : Reaches (zPeak z.d₀ z.segs z.segs.length) σ.c := by
      rw [zPeak_length]; exact h1.trans hr
    rcases Nat.lt_or_ge (k + 1) z.segs.length with hk1 | hk1
    · have h3 : Reaches (zPeak z.d₀ z.segs z.segs.length) (zPeak z.d₀ z.segs (k + 1)) := by
        rw [← hpk.2]; exact h2.trans ⟨σ.s⟩
      exact (hz.zPeak_incomp hcf hint hsc hk1 le_rfl).2 h3
    · have hkn : k + 1 = z.segs.length := by omega
      have : Reaches σ.d σ.c := by rw [hpk.2, hkn]; exact h2
      exact no_pos_cycle hcf σ.s hs this
  · -- on another segment
    obtain ⟨ρ, hρ, hvρ⟩ := Set.mem_iUnion₂.1 hu
    obtain ⟨r, hr', hρr, hrk⟩ := exists_idx_other1 hsplit hρ
    have h2 : Reaches z.segs[r].c z.segs[k].c := by
      rw [hρr, hσ]; exact (ZSeg.reaches_of_mem_verts hvρ).trans hr
    rcases Nat.lt_or_gt_of_ne hrk with hlt | hgt
    · exact (hz.valley_incomp hcf hint hsc hlt (by omega)).1 h2
    · exact (hz.valley_incomp hcf hint hsc hgt hr').2 h2

/-- On its own segment, only the valley lies below the valley. -/
lemma ZSeg.eq_of_reaches_c (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0) {σ : ZSeg A} {u : A} (hu : u ∈ σ.verts) (hr : Reaches u σ.c) : u = σ.c :=
  eq_of_reaches_cycle (H := Set.univ) (fun x _ p ↦ hcf x p) trivial
    (ZSeg.reaches_of_mem_verts hu) hr

end LargeIndecomposable.RayCat
