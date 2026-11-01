module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma53B

/-!
# Fischbacher §5.3–5.4: replacing the end of a good walk

`ZWalk.Good.replace`: in a good walk with a segment `σ` of valley `c`, replace `σ` and all
later segments by a new linked list `M` from the left peak of `σ` (with a new final path along
`w`). If the new pieces are nontrivial with nonzero `s`-values, consecutive peaks of `M` are
incomparable, `M` is separating (also at its junction with the kept part) in every convex subset
of the old hull avoiding `c`, and no new vertex lies below `c`, then the new walk is good, has
the same first peak and a strictly smaller hull (by the key fact (K), `c` leaves the hull).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- The peak between two consecutive segments is separating in `H`. -/
def SepPair (H : Set A) (ρ₁ ρ₂ : ZSeg A) : Prop :=
  ∀ (c dl q c' d' : A) (x₁ x₂ : RayVert A)
    (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
    (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
    (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
    ρ₁ = ⟨c, dl, q, t, s₀.cons e₁⟩ → ρ₂ = ⟨c', q, d', t₀.cons e₂, s'⟩ →
      ¬SepComp H q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩

lemma sepAll_iff {H : Set A} {L : List (ZSeg A)} : SepAll H L ↔ L.IsChain (SepPair H) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  constructor
  · intro h a b l₁ l₂ heq c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' h₁ h₂
    subst h₁ h₂
    exact h l₁ l₂ _ _ _ _ _ _ _ _ _ _ _ _ _ heq
  · intro h L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
    exact h hsplit _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl

lemma SepPair.mono {H H' : Set A} (hHH : H ⊆ H') {ρ₁ ρ₂ : ZSeg A} (h : SepPair H' ρ₁ ρ₂) :
    SepPair H ρ₁ ρ₂ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ hs ↦
  h _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ (SepComp.mono hHH hs)

lemma sepAll_mono {H H' : Set A} (hHH : H ⊆ H') {L : List (ZSeg A)} (h : SepAll H' L) :
    SepAll H L := by
  rw [sepAll_iff] at h ⊢
  exact h.imp fun _ _ ↦ SepPair.mono hHH

lemma pathVerts_cast {x x' y : A} (h : x = x') (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) :
    pathVerts (h ▸ p : Quiver.Path (RayVert.mk x') (RayVert.mk y)) = pathVerts p := by
  subst h; rfl

lemma comp_cast {a₀ x x' y : A} (h : x = x') (p : Quiver.Path (RayVert.mk a₀) (RayVert.mk x))
    (q : Quiver.Path (RayVert.mk x) (RayVert.mk y)) :
    (h ▸ p : Quiver.Path (RayVert.mk a₀) (RayVert.mk x')).comp
      (h ▸ q : Quiver.Path (RayVert.mk x') (RayVert.mk y)) = p.comp q := by
  subst h; rfl

/-- **Replacing the end of a good walk.** -/
theorem ZWalk.Good.replace
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w)
    {L₁ L₂ : List (ZSeg A)} {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂)
    (M : List (ZSeg A)) (hMne : M ≠ []) (hMl : ZLinked σ.dl M)
    (w'' : Quiver.Path (RayVert.mk (ZLast σ.dl M)) (RayVert.mk b))
    (halong : ∃ w₁ : Quiver.Path (RayVert.mk a₀) (RayVert.mk (ZLast σ.dl M)), w = w₁.comp w'')
    (hpos : ∀ ρ ∈ M, 0 < ρ.t.length ∧ 0 < ρ.s.length ∧ pathVal ρ.s ≠ 0)
    (hinc : ∀ ρ ∈ M, Incomp ρ.dl ρ.d)
    (hV : segsVerts M ∪ pathVerts w'' ⊆ z.hull)
    (hbelow : ∀ u ∈ segsVerts M ∪ pathVerts w'', ¬Reaches u σ.c)
    (hsep : ∀ H : Set A, ConvexR H → σ.c ∉ H → H ⊆ z.hull → segsVerts M ⊆ H →
      SepAll H M ∧ ∀ ρ₁ ∈ L₁.getLast?, ∀ ρ₂ ∈ M.head?, SepPair H ρ₁ ρ₂) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  have hl := z.linked
  rw [hsplit, zLinked_append] at hl
  obtain ⟨hl₁, hσdl, -⟩ := hl
  have hlin : ZLinked z.d₀ (L₁ ++ M) := (zLinked_append _ _ _).2 ⟨hl₁, hσdl ▸ hMl⟩
  have hlast : ZLast σ.dl M = ZLast z.d₀ (L₁ ++ M) := by rw [zLast_append, ← hσdl]
  let z' : ZWalk b := ⟨z.d₀, L₁ ++ M, hlin, z.v', hlast ▸ w''⟩
  have hw'v : pathVerts z'.w' = pathVerts w'' := pathVerts_cast hlast w''
  have hL₁ : ∀ ρ ∈ L₁, ρ ∈ z.segs := fun ρ h ↦ by rw [hsplit]; exact List.mem_append_left _ h
  have hverts : z'.verts ⊆ z.hull := by
    rintro u ((hu | hu) | hu)
    · exact z.verts_subset_hull (Or.inl (Or.inl hu))
    · rw [hw'v] at hu; exact hV (Or.inr hu)
    · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact z.verts_subset_hull (z.seg_verts_subset (hL₁ ρ hρ) hu)
      · exact hV (Or.inl (mem_segsVerts hρ hu))
  have hsub : z'.hull ⊆ z.hull := hullOf_subset z.convexR_hull hverts
  have hσmem : σ ∈ z.segs := by rw [hsplit]; simp
  have hcz : σ.c ∈ z.hull :=
    z.verts_subset_hull (z.seg_verts_subset hσmem (Or.inl (mem_pathVerts_start _)))
  have hcz' : σ.c ∉ z'.hull := by
    rintro ⟨u, hu, -, -, h1, -⟩
    rcases hu with (hu | hu) | hu
    · exact hz.key hcf hint hsc hsplit (Or.inl (Or.inl hu)) h1
    · rw [hw'v] at hu; exact hbelow u (Or.inr hu) h1
    · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hz.key hcf hint hsc hsplit
          (Or.inr (mem_segsVerts (List.mem_append_left _ hρ) hu)) h1
      · exact hbelow u (Or.inl (mem_segsVerts hρ hu)) h1
  refine ⟨z', rfl, ?_, hsub, fun h ↦ hcz' (h hcz)⟩
  have hM : ∀ ρ ∈ M, ρ ∈ z'.segs := fun ρ h ↦ List.mem_append_right _ h
  refine ⟨by simp [z', hMne], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w₁, hw⟩ := halong
    exact ⟨hlast ▸ w₁, by rw [comp_cast]; exact hw⟩
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hz.sne ρ (hL₁ ρ hρ)
    · exact (hpos ρ hρ).2.2
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hz.tpos ρ (hL₁ ρ hρ)
    · exact (hpos ρ hρ).1
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hz.spos ρ (hL₁ ρ hρ)
    · exact (hpos ρ hρ).2.1
  · have hold : SepAll z.hull z.segs := hz.sep
    rw [sepAll_iff, hsplit, List.isChain_append] at hold
    have hMs := hsep z'.hull (convexR_hullOf _) hcz' hsub
      (fun u hu ↦ subset_hullOf _ (Or.inr (by
        obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        exact Set.mem_iUnion₂.2 ⟨ρ, List.mem_append_right _ hρ, hu⟩)))
    change SepAll z'.hull (L₁ ++ M)
    rw [sepAll_iff, List.isChain_append]
    refine ⟨hold.1.imp fun _ _ ↦ SepPair.mono hsub, sepAll_iff.1 hMs.1, hMs.2⟩
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hz.incomp ρ (hL₁ ρ hρ)
    · exact hinc ρ hρ

/-- A junction peak stays separating when its new right arrow is joined to the old one. -/
lemma sepPair_left {H H₀ : Set A} (hHH : H ⊆ H₀) {ρ : ZSeg A} {c c' dl d d' : A}
    {y₁ y₂ : RayVert A} {t₁ : Quiver.Path (RayVert.mk c) y₁} {a₁ : y₁ ⟶ RayVert.mk dl}
    {s : Quiver.Path (RayVert.mk c) (RayVert.mk d)} {t₂ : Quiver.Path (RayVert.mk c') y₂}
    {a₂ : y₂ ⟶ RayVert.mk dl} {s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')}
    (hjoin : SepComp H₀ dl ⟨y₁.out, a₁.1⟩ ⟨y₂.out, a₂.1⟩)
    (hold : SepPair H₀ ρ ⟨c, dl, d, t₁.cons a₁, s⟩) :
    SepPair H ρ ⟨c', dl, d', t₂.cons a₂, s'⟩ := by
  intro c₀ dl₀ q c'' d'' x₁ x₂ t s₀ e₁ t₀ e₂ s'' h₁ h₂ hsc
  simp only [ZSeg.mk.injEq] at h₂
  obtain ⟨rfl, rfl, rfl, ht, -⟩ := h₂
  have ht' := eq_of_heq ht
  simp only [Quiver.Path.cons.injEq] at ht'
  obtain ⟨rfl, -, he⟩ := ht'
  obtain rfl := eq_of_heq he
  exact hold _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ rfl
    (Relation.EqvGen.trans _ _ _ (SepComp.mono hHH hsc) (Relation.EqvGen.symm _ _ hjoin))

/-- A junction peak stays separating when its new left arrow is joined to the old one. -/
lemma sepPair_right {H H₀ : Set A} (hHH : H ⊆ H₀) {ρ : ZSeg A} {c c' dl dl' d : A}
    {y₁ y₂ : RayVert A} {t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)}
    {s₁ : Quiver.Path (RayVert.mk c) y₁} {b₁ : y₁ ⟶ RayVert.mk d}
    {t' : Quiver.Path (RayVert.mk c') (RayVert.mk dl')} {s₂ : Quiver.Path (RayVert.mk c') y₂}
    {b₂ : y₂ ⟶ RayVert.mk d} (hjoin : SepComp H₀ d ⟨y₁.out, b₁.1⟩ ⟨y₂.out, b₂.1⟩)
    (hold : SepPair H₀ ⟨c, dl, d, t, s₁.cons b₁⟩ ρ) :
    SepPair H ⟨c', dl', d, t', s₂.cons b₂⟩ ρ := by
  intro c₀ dl₀ q c'' d'' x₁ x₂ t₀' s₀ e₁ t₀ e₂ s'' h₁ h₂ hsc
  simp only [ZSeg.mk.injEq] at h₁
  obtain ⟨rfl, rfl, rfl, -, hs⟩ := h₁
  have hs' := eq_of_heq hs
  simp only [Quiver.Path.cons.injEq] at hs'
  obtain ⟨rfl, -, he⟩ := hs'
  obtain rfl := eq_of_heq he
  exact hold _ _ _ _ _ _ _ _ _ _ _ _ _ rfl h₂
    (Relation.EqvGen.trans _ _ _ hjoin (SepComp.mono hHH hsc))

section Mid

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
  (hint : ∀ a b : A, (interval a b).Finite)
  (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
    IsCoboundaryOn D c)
include hcf hint hsc

/-- The separation conditions of a good walk around a split. -/
lemma ZWalk.Good.sepPairs {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)}
    (hz : z.Good w) {L₁ L₂ : List (ZSeg A)} {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) :
    L₁.IsChain (SepPair z.hull) ∧ L₂.IsChain (SepPair z.hull) ∧
      (∀ ρ ∈ L₁.getLast?, SepPair z.hull ρ σ) ∧ (∀ ρ ∈ L₂.head?, SepPair z.hull σ ρ) := by
  have h : SepAll z.hull z.segs := hz.sep
  rw [sepAll_iff, hsplit, List.isChain_append, List.isChain_cons] at h
  exact ⟨h.1, h.2.1.2, fun ρ hρ ↦ h.2.2 ρ hρ σ (by simp), h.2.1.1⟩

omit hcf hint hsc in
lemma zLast_eq_of_split {b : A} {z : ZWalk b} {L₁ L₂ : List (ZSeg A)} {σ : ZSeg A}
    (hsplit : z.segs = L₁ ++ σ :: L₂) : ZLast z.d₀ z.segs = ZLast σ.d L₂ := by
  rw [hsplit, zLast_append]; rfl

/-- **Replacing one segment of a good walk** by a list with the same end peaks. -/
theorem ZWalk.Good.replace_mid {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) (N : List (ZSeg A)) (hNne : N ≠ [])
    (hNl : ZLinked σ.dl N) (hNlast : ZLast σ.dl N = σ.d)
    (hpos : ∀ ρ ∈ N, 0 < ρ.t.length ∧ 0 < ρ.s.length ∧ pathVal ρ.s ≠ 0)
    (hinc : ∀ ρ ∈ N, Incomp ρ.dl ρ.d) (hV : segsVerts N ⊆ z.hull)
    (hbelow : ∀ u ∈ segsVerts N, ¬Reaches u σ.c)
    (hsep : ∀ H : Set A, ConvexR H → σ.c ∉ H → H ⊆ z.hull → segsVerts N ⊆ H →
      SepAll H N ∧ (∀ ρ₁ ∈ L₁.getLast?, ∀ ρ₂ ∈ N.head?, SepPair H ρ₁ ρ₂) ∧
        ∀ ρ₁ ∈ N.getLast?, ∀ ρ₂ ∈ L₂.head?, SepPair H ρ₁ ρ₂) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  have hlast : ZLast z.d₀ z.segs = ZLast σ.dl (N ++ L₂) := by
    rw [zLast_eq_of_split hsplit, zLast_append, hNlast]
  have hl := z.linked
  rw [hsplit, zLinked_append] at hl
  obtain ⟨-, -, hl₂⟩ := hl
  have hL₂ : ∀ ρ ∈ L₂, ρ ∈ z.segs := fun ρ h ↦ by rw [hsplit]; simp [h]
  obtain ⟨-, hc₂, -, -⟩ := hz.sepPairs hcf hint hsc hsplit
  refine hz.replace hcf hint hsc hsplit (N ++ L₂) (by simp [hNne])
    ((zLinked_append _ _ _).2 ⟨hNl, hNlast ▸ hl₂⟩) (hlast ▸ z.w') ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨w₁, hw⟩ := hz.along
    exact ⟨hlast ▸ w₁, by rw [comp_cast]; exact hw⟩
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hpos ρ hρ
    · exact ⟨hz.tpos ρ (hL₂ ρ hρ), hz.spos ρ (hL₂ ρ hρ), hz.sne ρ (hL₂ ρ hρ)⟩
  · intro ρ hρ
    rcases List.mem_append.1 hρ with hρ | hρ
    · exact hinc ρ hρ
    · exact hz.incomp ρ (hL₂ ρ hρ)
  · rintro u (hu | hu)
    · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hV (mem_segsVerts hρ hu)
      · exact z.verts_subset_hull (z.seg_verts_subset (hL₂ ρ hρ) hu)
    · rw [pathVerts_cast] at hu
      exact z.verts_subset_hull (Or.inl (Or.inr hu))
  · rintro u (hu | hu)
    · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hbelow u (mem_segsVerts hρ hu)
      · exact hz.key hcf hint hsc hsplit
          (Or.inr (mem_segsVerts (List.mem_append_right _ hρ) hu))
    · rw [pathVerts_cast] at hu
      exact hz.key hcf hint hsc hsplit (Or.inl (Or.inr hu))
  · intro H hH hcH hHz hMH
    have hNH : segsVerts N ⊆ H := fun u hu ↦ by
      obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      exact hMH (mem_segsVerts (List.mem_append_left _ hρ) hu)
    obtain ⟨h1, h2, h3⟩ := hsep H hH hcH hHz hNH
    refine ⟨?_, ?_⟩
    · rw [sepAll_iff, List.isChain_append]
      exact ⟨sepAll_iff.1 h1, hc₂.imp fun _ _ ↦ SepPair.mono hHz, h3⟩
    · intro ρ₁ hρ₁ ρ₂ hρ₂
      rw [List.head?_append, Option.mem_def] at hρ₂
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (by simpa using hNne : N.head? ≠ none)
      rw [hx] at hρ₂
      simp only [Option.some_or, Option.some.injEq] at hρ₂
      subst hρ₂
      exact h2 ρ₁ hρ₁ x hx

/-- **Fischbacher §5.3, Case A**: if the zero `t`-path and the `s`-path of a segment start with
the same arrow, dropping it shrinks the hull. -/
theorem ZWalk.Good.caseA {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {c c' dl d : A} {γ : RayVert.mk c ⟶ RayVert.mk c'}
    {t'' : Quiver.Path (RayVert.mk c') (RayVert.mk dl)}
    {s'' : Quiver.Path (RayVert.mk c') (RayVert.mk d)}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, d, γ.toPath.comp t'', γ.toPath.comp s''⟩ :: L₂)
    (ht0 : pathVal (γ.toPath.comp t'') = 0) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  have hσ : (⟨c, dl, d, γ.toPath.comp t'', γ.toPath.comp s''⟩ : ZSeg A) ∈ z.segs := by
    rw [hsplit]; simp
  have hinc := hz.incomp _ hσ
  obtain ⟨y₁, t₀, a, rfl⟩ : ∃ (y₁ : RayVert A) (t₀ : Quiver.Path (RayVert.mk c') y₁)
      (a : y₁ ⟶ RayVert.mk dl), t'' = t₀.cons a := by
    rcases t'' with _ | ⟨t₀, a⟩
    · exfalso
      apply γ.2.1
      rw [← ht0]
      change γ.1 = 𝟙 _ ≫ γ.1
      rw [Category.id_comp]
    · exact ⟨_, t₀, a, rfl⟩
  obtain ⟨y₂, s₀, b', rfl⟩ : ∃ (y₂ : RayVert A) (s₀ : Quiver.Path (RayVert.mk c') y₂)
      (b' : y₂ ⟶ RayVert.mk d), s'' = s₀.cons b' := by
    rcases s'' with _ | ⟨s₀, b'⟩
    · exact absurd ⟨t₀.cons a⟩ hinc.2
    · exact ⟨_, s₀, b', rfl⟩
  have hsne : pathVal (s₀.cons b') ≠ 0 := by
    intro h0
    apply hz.sne _ hσ
    change pathVal (γ.toPath.comp (s₀.cons b')) = 0
    rw [pathVal_toPath_comp, h0, comp_zero]
  have hσV : ZSeg.verts (⟨c, dl, d, γ.toPath.comp (t₀.cons a), γ.toPath.comp (s₀.cons b')⟩ :
      ZSeg A) ⊆ z.hull := fun u hu ↦ z.verts_subset_hull (z.seg_verts_subset hσ hu)
  have hsub : ZSeg.verts (⟨c', dl, d, t₀.cons a, s₀.cons b'⟩ : ZSeg A) ⊆
      ZSeg.verts (⟨c, dl, d, γ.toPath.comp (t₀.cons a), γ.toPath.comp (s₀.cons b')⟩ :
        ZSeg A) := by
    rintro u (hu | hu)
    · exact Or.inl (by rw [pathVerts_comp]; exact Or.inr hu)
    · exact Or.inr (by rw [pathVerts_comp]; exact Or.inr hu)
  have hsV : ∀ u ∈ segsVerts [(⟨c', dl, d, t₀.cons a, s₀.cons b'⟩ : ZSeg A)],
      u ∈ ZSeg.verts (⟨c', dl, d, t₀.cons a, s₀.cons b'⟩ : ZSeg A) := by
    intro u hu
    obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rw [List.mem_singleton] at hρ
    subst hρ; exact hu
  obtain ⟨-, -, hjl, hjr⟩ := hz.sepPairs hcf hint hsc hsplit
  refine hz.replace_mid hcf hint hsc hsplit [⟨c', dl, d, t₀.cons a, s₀.cons b'⟩] (by simp)
    ⟨rfl, trivial⟩ rfl ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [List.mem_singleton] at hρ
    subst hρ
    exact ⟨by simp, by simp, hsne⟩
  · intro ρ hρ
    rw [List.mem_singleton] at hρ
    subst hρ
    exact hinc
  · exact fun u hu ↦ hσV (hsub (hsV u hu))
  · intro u hu hr
    have hu' := hsV u hu
    have := ZSeg.eq_of_reaches_c hcf (hsub hu') hr
    subst this
    obtain ⟨p⟩ : Reaches c' u := ZSeg.reaches_of_mem_verts hu'
    exact no_pos_cycle hcf (γ.toPath.comp p) (by simp [Quiver.Path.length_comp]) (Reaches.refl _)
  · intro H _ _ hHz _
    refine ⟨?_, ?_, ?_⟩
    · intro L₁' L₂' _ _ _ _ _ _ _ _ _ _ _ _ _ h
      have := congrArg List.length h
      simp at this
      omega
    · intro ρ₁ hρ₁ ρ₂ hρ₂
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hρ₂
      subst hρ₂
      exact sepPair_left (t₁ := γ.toPath.comp t₀) hHz (Relation.EqvGen.refl _) (hjl ρ₁ hρ₁)
    · intro ρ₁ hρ₁ ρ₂ hρ₂
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hρ₁
      subst hρ₁
      exact sepPair_right (s₁ := γ.toPath.comp s₀) hHz (Relation.EqvGen.refl _) (hjr ρ₂ hρ₂)

end Mid

end LargeIndecomposable.RayCat
