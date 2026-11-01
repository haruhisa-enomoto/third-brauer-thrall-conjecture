module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.ZWalk

/-!
# Cyclic zigzag walks (Fischbacher's Lemma 4.4, cyclic form)

A cyclic zigzag walk is a linked list of segments whose last peak is its first left peak
(`ZLinked d₀ L`, `ZLast d₀ L = d₀`). Rotations stay cyclic (`zCyc_rotate`). A maximal point of
the convex hull of the walk is a peak (`exists_max_peak`), and a front peak of a rotation that
meets no other vertex and is maximal in a simply connected hull is not separating
(`sepComp_front`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The peak at position `k`: the last peak of the first `k` segments. -/
def zPeak (d₀ : A) (L : List (ZSeg A)) (k : ℕ) : A := ZLast d₀ (L.take k)

lemma zPeak_zero (d₀ : A) (L : List (ZSeg A)) : zPeak d₀ L 0 = d₀ := by simp [zPeak, ZLast]

/-- Segment `k` runs from peak `k` to peak `k + 1`. -/
lemma zPeak_seg : ∀ (d₀ : A) (L : List (ZSeg A)), ZLinked d₀ L → ∀ (k : ℕ) (hk : k < L.length),
    L[k].dl = zPeak d₀ L k ∧ L[k].d = zPeak d₀ L (k + 1)
  | _, [], _, _, hk => absurd hk (by simp)
  | d₀, σ :: L, ⟨hdl, hl⟩, 0, _ => ⟨by simpa [zPeak, ZLast] using hdl, by simp [zPeak, ZLast]⟩
  | d₀, σ :: L, ⟨_, hl⟩, k + 1, hk => by
    have := zPeak_seg σ.d L hl k (by simpa using hk)
    simpa [zPeak, ZLast, List.take_succ_cons] using this

/-- Splitting a list around two adjacent entries. -/
lemma split_two {α : Type*} (L : List α) (k : ℕ) (hk : k + 1 < L.length) :
    L = L.take k ++ L[k] :: L[k + 1] :: L.drop (k + 2) := by
  conv_lhs => rw [← List.take_append_drop k L]
  congr 1
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by simpa using hk)]

/-- Rotating a cyclic list of segments. -/
lemma zCyc_rotate (d₀ : A) (M₁ M₂ : List (ZSeg A)) (h : ZLinked d₀ (M₁ ++ M₂))
    (hc : ZLast d₀ (M₁ ++ M₂) = d₀) :
    ZLinked (ZLast d₀ M₁) (M₂ ++ M₁) ∧ ZLast (ZLast d₀ M₁) (M₂ ++ M₁) = ZLast d₀ M₁ := by
  rw [zLinked_append] at h
  rw [zLast_append] at hc
  refine ⟨?_, ?_⟩
  · rw [zLinked_append, hc]
    exact ⟨h.2, h.1⟩
  · rw [zLast_append, hc]

/-- The vertices of a list of segments. -/
def segsVerts (L : List (ZSeg A)) : Set A := ⋃ σ ∈ L, σ.verts

/-- In a cyclic list, every left peak is the right peak of some segment. -/
lemma exists_d_eq_dl {d₀ : A} {L : List (ZSeg A)} (h : ZLinked d₀ L) (hc : ZLast d₀ L = d₀)
    (hne : L ≠ []) {ρ : ZSeg A} (hρ : ρ ∈ L) : ∃ π ∈ L, π.d = ρ.dl := by
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hρ
  rcases M₁.eq_nil_or_concat with rfl | ⟨M₀, π, rfl⟩
  · -- ρ is the head: its left peak is the last peak
    simp only [List.nil_append] at h hc
    obtain ⟨hdl, h'⟩ := h
    rcases M₂.eq_nil_or_concat with rfl | ⟨M₃, π, rfl⟩
    · exact ⟨ρ, by simp, by change ρ.d = ρ.dl; rw [hdl]; exact hc⟩
    · rw [List.concat_eq_append] at hc ⊢
      refine ⟨π, by simp, ?_⟩
      change ZLast ρ.d (M₃ ++ [π]) = d₀ at hc
      rw [zLast_append] at hc
      rw [hdl, ← hc]
      rfl
  · rw [List.concat_eq_append] at h ⊢
    rw [List.append_assoc, List.singleton_append, zLinked_append] at h
    obtain ⟨-, -, hρdl, -⟩ := h
    exact ⟨π, by simp, hρdl.symm⟩

lemma mem_segsVerts {L : List (ZSeg A)} {σ : ZSeg A} (h : σ ∈ L) : σ.verts ⊆ segsVerts L :=
  fun _ hx ↦ Set.mem_biUnion h hx

variable [IsRayCategory A]

/-- **A maximal point of the hull of a cyclic walk is a peak.** -/
lemma exists_max_peak (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0) (hint : ∀ a b : A, (interval a b).Finite) {d₀ : A} {L : List (ZSeg A)}
    (h : ZLinked d₀ L) (hc : ZLast d₀ L = d₀) (hne : L ≠ []) {u : A} (hu : u ∈ segsVerts L) :
    ∃ (M₁ M₂ : List (ZSeg A)) (σ : ZSeg A), L = M₁ ++ σ :: M₂ ∧ Reaches u σ.d ∧
      ∀ {y : RayVert A} (_ : RayVert.mk σ.d ⟶ y), y.out ∉ hullOf (segsVerts L) := by
  set H := hullOf (segsVerts L)
  have hfin : (segsVerts L).Finite :=
    L.finite_toSet.biUnion fun σ _ ↦ (pathVerts_finite σ.t).union (pathVerts_finite σ.s)
  have hHfin : H.Finite := finite_hullOf hint hfin
  have hcfH : CycleFreeOn H := fun x _ p ↦ hcf x p
  obtain ⟨m, hmH, hum, hmax⟩ := exists_max_above hcfH hHfin (subset_hullOf _ hu)
  -- `m` is a vertex
  obtain ⟨-, -, b', hb', -, hmb'⟩ := hmH
  have hmb := (hmax b' (subset_hullOf _ hb') hmb').symm
  subst hmb
  obtain ⟨ρ, hρ, hmρ⟩ := Set.mem_iUnion₂.1 hb'
  -- `m` is the top of a piece, hence a peak
  have key : ∃ π ∈ L, π.d = m := by
    rcases hmρ with hm | hm
    · have h1 := (reaches_of_mem_pathVerts ρ.t hm).2
      have h2 := hmax _ (subset_hullOf _ (mem_segsVerts hρ (Or.inl (mem_pathVerts_end _)))) h1
      obtain ⟨π, hπ, hπd⟩ := exists_d_eq_dl h hc hne hρ
      exact ⟨π, hπ, hπd.trans h2⟩
    · have h1 := (reaches_of_mem_pathVerts ρ.s hm).2
      have h2 := hmax _ (subset_hullOf _ (mem_segsVerts hρ (Or.inr (mem_pathVerts_end _)))) h1
      exact ⟨ρ, hρ, h2⟩
  obtain ⟨π, hπ, hπd⟩ := key
  obtain ⟨M₁, M₂, hsplit⟩ := List.append_of_mem hπ
  refine ⟨M₁, M₂, π, hsplit, hπd ▸ hum, fun {y} e hy ↦ ?_⟩
  rw [hπd] at e
  have := hmax _ hy ⟨e.toPath⟩
  obtain rfl : RayVert.mk m = y := this.symm
  have := hcf m e.toPath
  simp at this

/-- **A front peak of a cyclic walk is not separating** (at least two segments). -/
lemma sepComp_front2 {H : Set A} (hHfin : H.Finite) (hHconv : ConvexR H)
    (hsc : ∀ c : ArrowWeight A, IsCocycleOn H c → IsCoboundaryOn H c)
    {R : List (ZSeg A)} {c dl q c' d' : A} {x₁ x₂ : RayVert A}
    {t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)} {s₀ : Quiver.Path (RayVert.mk c) x₁}
    {e₁ : x₁ ⟶ RayVert.mk q} {t₀ : Quiver.Path (RayVert.mk c') x₂} {e₂ : x₂ ⟶ RayVert.mk q}
    {s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')}
    (hl : ZLinked d' R) (hc : ZLast d' R = dl)
    (hV : segsVerts (⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: R) ⊆ H)
    (hav : q ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts R ∪ pathVerts s₀ ∪ pathVerts t₀)
    (hmax : ∀ {y : RayVert A} (_ : RayVert.mk q ⟶ y), y.out ∉ H) :
    SepComp H q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  have hin : ∀ {X : Set A}, X ⊆ H → q ∉ X → X ⊆ H \ {q} := fun hX hq _ hx ↦
    ⟨hX hx, fun h ↦ hq (by rw [Set.mem_singleton_iff] at h; exact h ▸ hx)⟩
  have hσ : ∀ X, X ⊆ ZSeg.verts ⟨c, dl, q, t, s₀.cons e₁⟩ → X ⊆ H := fun X hX ↦
    hX.trans ((mem_segsVerts (by simp)).trans hV)
  have hτ : ∀ X, X ⊆ ZSeg.verts ⟨c', q, d', t₀.cons e₂, s'⟩ → X ⊆ H := fun X hX ↦
    hX.trans ((mem_segsVerts (by simp)).trans hV)
  have qt : q ∉ pathVerts t := fun h ↦ hav (by simp [h])
  have qs' : q ∉ pathVerts s' := fun h ↦ hav (by simp [h])
  have qR : q ∉ segsVerts R := fun h ↦ hav (by simp [h])
  have qs₀ : q ∉ pathVerts s₀ := fun h ↦ hav (by simp [h])
  have qt₀ : q ∉ pathVerts t₀ := fun h ↦ hav (by simp [h])
  have h1 := eqvGen_of_path (D := H) (q := q) s₀
    (hin (hσ _ fun _ hx ↦ Or.inr (Set.mem_insert_of_mem _ hx)) qs₀)
  have h2 := eqvGen_of_path (D := H) (q := q) t (hin (hσ _ fun _ hx ↦ Or.inl hx) qt)
  have hRH : ∀ τ ∈ R, τ.verts ⊆ H \ {q} := fun τ hτ ↦
    hin (fun _ hx ↦ hV (mem_segsVerts (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hτ)) hx))
      (fun h ↦ qR (mem_segsVerts hτ h))
  have hd' : d' ∈ H \ {q} :=
    hin (hτ _ fun _ hx ↦ Or.inr hx) qs' (mem_pathVerts_end s')
  have h3 := eqvGen_of_linked d' R hl hRH hd'
  rw [hc] at h3
  have h4 := eqvGen_of_path (D := H) (q := q) s' (hin (hτ _ fun _ hx ↦ Or.inr hx) qs')
  have h5 := eqvGen_of_path (D := H) (q := q) t₀
    (hin (hτ _ fun _ hx ↦ Or.inl (Set.mem_insert_of_mem _ hx)) qt₀)
  have hconn : Relation.EqvGen (AdjOff H q) x₁.out x₂.out :=
    h1.symm.trans _ _ _ (h2.trans _ _ _ (h3.symm.trans _ _ _ (h4.symm.trans _ _ _ h5)))
  have hx₁ : x₁.out ∈ H \ {q} :=
    hin (hσ _ fun _ hx ↦ Or.inr (Set.mem_insert_of_mem _ hx)) qs₀ (mem_pathVerts_end s₀)
  have hx₂ : x₂.out ∈ H \ {q} :=
    hin (hτ _ fun _ hx ↦ Or.inl (Set.mem_insert_of_mem _ hx)) qt₀ (mem_pathVerts_end t₀)
  exact sepComp_of_coboundary (hσ _ (fun _ hx ↦ Or.inr hx) (Set.mem_insert _ _)) hmax hsc e₁ e₂
    hx₁.1 hx₂.1 hx₁.2 hx₂.2 hconn

/-- **Every vertex of a cyclic walk lies below its base** if all other peaks are separating
in the hull and meet no other vertex. -/
theorem cyc_top (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {d₀ : A} {C : List (ZSeg A)} (h : ZLinked d₀ C) (hc : ZLast d₀ C = d₀) (hne : C ≠ [])
    (hsep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      C = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ → q ≠ d₀ →
        ¬SepComp (hullOf (segsVerts C)) q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ ∧
        q ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts (L₂ ++ L₁))
    (hpos : ∀ σ ∈ C, 0 < σ.s.length ∧ 0 < σ.t.length) {u : A} (hu : u ∈ segsVerts C) :
    Reaches u d₀ := by
  obtain ⟨M₁, M₂, π, hsplit, hup, hmax⟩ := exists_max_peak hcf hint h hc hne hu
  by_cases hπ : π.d = d₀
  · exact hπ ▸ hup
  exfalso
  -- `π` is not the last segment
  obtain ⟨π₂, R, rfl⟩ : ∃ (π₂ : ZSeg A) (R : List (ZSeg A)), M₂ = π₂ :: R := by
    rcases M₂ with _ | ⟨π₂, R⟩
    · exfalso
      apply hπ
      rw [hsplit, zLast_append] at hc
      exact hc
    · exact ⟨π₂, R, rfl⟩
  -- destructure the front pair
  obtain ⟨c, dl, q, t, s⟩ := π
  obtain ⟨c', q', d', t', s'⟩ := π₂
  have hlink := h
  rw [hsplit, zLinked_append] at hlink
  obtain ⟨-, -, hq', hlR⟩ := hlink
  change q' = q at hq'
  subst hq'
  have hπmem : (⟨c, dl, q', t, s⟩ : ZSeg A) ∈ C := by rw [hsplit]; simp
  have hπ₂mem : (⟨c', q', d', t', s'⟩ : ZSeg A) ∈ C := by rw [hsplit]; simp
  obtain ⟨x₁, s₀, e₁, rfl⟩ : ∃ (x₁ : RayVert A) (s₀ : Quiver.Path (RayVert.mk c) x₁) (e₁ : x₁ ⟶ RayVert.mk q'),
      s = s₀.cons e₁ := by
    rcases s with _ | ⟨s₀, e₁⟩
    · exact absurd (hpos _ hπmem).1 (lt_irrefl 0)
    · exact ⟨_, s₀, e₁, rfl⟩
  obtain ⟨x₂, t₀, e₂, rfl⟩ : ∃ (x₂ : RayVert A) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q'),
      t' = t₀.cons e₂ := by
    rcases t' with _ | ⟨t₀, e₂⟩
    · exact absurd (hpos _ hπ₂mem).2 (lt_irrefl 0)
    · exact ⟨_, t₀, e₂, rfl⟩
  obtain ⟨hns, hav⟩ := hsep M₁ R c dl q' c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit hπ
  -- rotate to the front
  obtain ⟨hl', hc'⟩ := zCyc_rotate d₀ M₁ (_ :: _ :: R) (hsplit ▸ h) (hsplit ▸ hc)
  have hdl : ZLast d₀ M₁ = dl := by
    have := h
    rw [hsplit, zLinked_append] at this
    exact this.2.1.symm
  rw [hdl] at hl' hc'
  obtain ⟨-, -, hlR'⟩ := hl'
  change ZLast d' (R ++ M₁) = dl at hc'
  have hfin : (segsVerts C).Finite :=
    C.finite_toSet.biUnion fun σ _ ↦ (pathVerts_finite σ.t).union (pathVerts_finite σ.s)
  -- vertices of the rotated list
  have hsub : segsVerts (⟨c, dl, q', t, s₀.cons e₁⟩ :: ⟨c', q', d', t₀.cons e₂, s'⟩ :: (R ++ M₁))
      ⊆ hullOf (segsVerts C) := by
    intro x hx
    apply subset_hullOf
    obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
    refine mem_segsVerts (σ := σ) ?_ hxσ
    rw [hsplit]
    simp only [List.mem_cons, List.mem_append] at hσ ⊢
    tauto
  have hav' : q' ∉ pathVerts t ∪ pathVerts s' ∪ segsVerts (R ++ M₁) ∪ pathVerts s₀ ∪
      pathVerts t₀ := by
    intro hq
    rcases hq with (hq | hq) | hq
    · exact hav hq
    · obtain ⟨p₁⟩ := (reaches_of_mem_pathVerts s₀ hq).2
      have := hcf q' (p₁.cons e₁)
      simp at this
    · obtain ⟨p₂⟩ := (reaches_of_mem_pathVerts t₀ hq).2
      have := hcf q' (p₂.cons e₂)
      simp at this
  exact hns (sepComp_front2 (finite_hullOf hint hfin) (convexR_hullOf _)
    (hsc _ (finite_hullOf hint hfin) (convexR_hullOf _)) hlR' hc' hsub hav' hmax)

/-- **A one-segment cyclic walk: its peak is not separating.** -/
lemma sepComp_front1 {H : Set A} (hHfin : H.Finite) (hHconv : ConvexR H)
    (hsc : ∀ c : ArrowWeight A, IsCocycleOn H c → IsCoboundaryOn H c)
    {c q : A} {x₁ x₂ : RayVert A} {s₀ : Quiver.Path (RayVert.mk c) x₁}
    {e₁ : x₁ ⟶ RayVert.mk q} {t₀ : Quiver.Path (RayVert.mk c) x₂} {e₂ : x₂ ⟶ RayVert.mk q}
    (hV : ZSeg.verts ⟨c, q, q, t₀.cons e₂, s₀.cons e₁⟩ ⊆ H)
    (hav : q ∉ pathVerts s₀ ∪ pathVerts t₀)
    (hmax : ∀ {y : RayVert A} (_ : RayVert.mk q ⟶ y), y.out ∉ H) :
    SepComp H q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  have hin : ∀ {X : Set A}, X ⊆ H → q ∉ X → X ⊆ H \ {q} := fun hX hq _ hx ↦
    ⟨hX hx, fun h ↦ hq (by rw [Set.mem_singleton_iff] at h; exact h ▸ hx)⟩
  have qs₀ : q ∉ pathVerts s₀ := fun h ↦ hav (Or.inl h)
  have qt₀ : q ∉ pathVerts t₀ := fun h ↦ hav (Or.inr h)
  have h1 := eqvGen_of_path (D := H) (q := q) s₀
    (hin (fun _ hx ↦ hV (Or.inr (Set.mem_insert_of_mem _ hx))) qs₀)
  have h5 := eqvGen_of_path (D := H) (q := q) t₀
    (hin (fun _ hx ↦ hV (Or.inl (Set.mem_insert_of_mem _ hx))) qt₀)
  have hx₁ : x₁.out ∈ H \ {q} :=
    hin (fun _ hx ↦ hV (Or.inr (Set.mem_insert_of_mem _ hx))) qs₀ (mem_pathVerts_end s₀)
  have hx₂ : x₂.out ∈ H \ {q} :=
    hin (fun _ hx ↦ hV (Or.inl (Set.mem_insert_of_mem _ hx))) qt₀ (mem_pathVerts_end t₀)
  exact sepComp_of_coboundary (hV (Or.inr (Set.mem_insert _ _))) hmax hsc e₁ e₂
    hx₁.1 hx₂.1 hx₁.2 hx₂.2 (h1.symm.trans _ _ _ h5)

end LargeIndecomposable.RayCat
