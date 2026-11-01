module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma54

/-!
# Fischbacher §5.3, Case B: the minimal chain at the valley

If the zero `t`-path and the `s`-path of a segment of a good walk start with different arrows
`γ_t, γ_s` out of the valley `c`, then `c` is minimal in the hull, the rest of the closed walk
joins the targets of `γ_t` and `γ_s` away from `c`, and the separation criterion at `c` gives a
chain of links from `γ_t` to `γ_s` with bounds in the hull; we take a minimal one
(`ZWalk.Good.exists_minChain`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
  (hint : ∀ a b : A, (interval a b).Finite)
  (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
    IsCoboundaryOn D c)
include hcf hint hsc

/-- The vertices of a walk around a split. -/
lemma ZWalk.mem_verts_split {b : A} {z : ZWalk b} {L₁ L₂ : List (ZSeg A)} {σ : ZSeg A}
    (hsplit : z.segs = L₁ ++ σ :: L₂) {u : A} (hu : u ∈ z.verts) :
    u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂) ∨ u ∈ σ.verts := by
  rcases hu with (hu | hu) | hu
  · exact Or.inl (Or.inl (Or.inl hu))
  · exact Or.inl (Or.inl (Or.inr hu))
  · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rw [hsplit] at hρ
    simp only [List.mem_append, List.mem_cons] at hρ
    rcases hρ with hρ | rfl | hρ
    · exact Or.inl (Or.inr (mem_segsVerts (List.mem_append_left _ hρ) hu))
    · exact Or.inr hu
    · exact Or.inl (Or.inr (mem_segsVerts (List.mem_append_right _ hρ) hu))

/-- **Case B: a minimal chain from `γ_t` to `γ_s`.** -/
theorem ZWalk.Good.exists_minChain {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {c ct cs dl d : A} {γt : RayVert.mk c ⟶ RayVert.mk ct} {γs : RayVert.mk c ⟶ RayVert.mk cs}
    {t'' : Quiver.Path (RayVert.mk ct) (RayVert.mk dl)}
    {s'' : Quiver.Path (RayVert.mk cs) (RayVert.mk d)}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, d, γt.toPath.comp t'', γs.toPath.comp s''⟩ :: L₂) :
    ∃ W : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) ⟨ct, γt⟩ ⟨cs, γs⟩, IsMinC W := by
  set σ : ZSeg A := ⟨c, dl, d, γt.toPath.comp t'', γs.toPath.comp s''⟩ with hσdef
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hσV : σ.verts ⊆ z.hull := fun u hu ↦ z.verts_subset_hull (z.seg_verts_subset hσ hu)
  have hcH : c ∈ z.hull := hσV (Or.inl (mem_pathVerts_start _))
  have hkey : ∀ {u : A}, u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂) →
      Reaches u c → False := fun hu hr ↦ hz.key hcf hint hsc hsplit hu hr
  -- `c` is minimal in the hull
  have hmin : ∀ {y : RayVert A} (_ : y ⟶ RayVert.mk c), y.out ∉ z.hull := by
    intro y e hy
    obtain ⟨u, hu, -, -, h1, -⟩ := hy
    have huc : Reaches u c := h1.trans ⟨e.toPath⟩
    rcases ZWalk.mem_verts_split hcf hint hsc hsplit hu with hu | hu
    · exact hkey hu huc
    · have := ZSeg.eq_of_reaches_c hcf hu huc
      change u = c at this
      subst this
      exact no_pos_cycle hcf e.toPath (by simp) h1
  have hcob := hsc z.hull (finite_hullOf hint z.verts_finite) z.convexR_hull
  have hloop : ∀ {x : A} (e : RayVert.mk c ⟶ RayVert.mk x), x ≠ c := by
    intro x e hx
    subst hx
    have := hcf _ e.toPath
    simp at this
  have hctH : ct ∈ z.hull := by
    refine hσV (Or.inl ?_)
    rw [pathVerts_comp]; exact Or.inr (mem_pathVerts_start _)
  have hcsH : cs ∈ z.hull := by
    refine hσV (Or.inr ?_)
    rw [pathVerts_comp]; exact Or.inr (mem_pathVerts_start _)
  -- the rest of the walk avoids `c`
  have hoff : ∀ u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂), u ∈ z.hull \ {c} :=
    fun u hu ↦ ⟨z.verts_subset_hull (by
      rcases hu with (hu | hu) | hu
      · exact Or.inl (Or.inl hu)
      · exact Or.inl (Or.inr hu)
      · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        refine z.seg_verts_subset ?_ hu
        rw [hsplit]
        rcases List.mem_append.1 hρ with h | h <;> simp [h]),
      fun h ↦ hkey hu (by rw [Set.mem_singleton_iff.1 h]; exact Reaches.refl _)⟩
  have ht'' : pathVerts t'' ⊆ z.hull \ {c} := fun u hu ↦
    ⟨hσV (Or.inl (by rw [pathVerts_comp]; exact Or.inr hu)), fun h ↦ by
      rw [Set.mem_singleton_iff.1 h] at hu
      exact no_pos_cycle hcf γt.toPath (by simp) (reaches_of_mem_pathVerts t'' hu).1⟩
  have hs'' : pathVerts s'' ⊆ z.hull \ {c} := fun u hu ↦
    ⟨hσV (Or.inr (by rw [pathVerts_comp]; exact Or.inr hu)), fun h ↦ by
      rw [Set.mem_singleton_iff.1 h] at hu
      exact no_pos_cycle hcf γs.toPath (by simp) (reaches_of_mem_pathVerts s'' hu).1⟩
  have hl := z.linked
  rw [hsplit, zLinked_append] at hl
  obtain ⟨hl₁, hdl, hl₂⟩ := hl
  change dl = ZLast z.d₀ L₁ at hdl
  have h1 : Relation.EqvGen (AdjOff z.hull c) ct dl := eqvGen_of_path t'' ht''
  have h2 : Relation.EqvGen (AdjOff z.hull c) z.d₀ dl := by
    rw [hdl]
    exact eqvGen_of_linked z.d₀ L₁ hl₁
      (fun ρ hρ u hu ↦ hoff u (Or.inr (mem_segsVerts (List.mem_append_left _ hρ) hu)))
      (hoff _ (Or.inl (Or.inl (mem_pathVerts_start _))))
  have h3 : Relation.EqvGen (AdjOff z.hull c) z.d₀ b :=
    eqvGen_of_path z.v' fun u hu ↦ hoff u (Or.inl (Or.inl hu))
  have h4 : Relation.EqvGen (AdjOff z.hull c) (ZLast z.d₀ z.segs) b :=
    eqvGen_of_path z.w' fun u hu ↦ hoff u (Or.inl (Or.inr hu))
  have h5 : Relation.EqvGen (AdjOff z.hull c) d (ZLast z.d₀ z.segs) := by
    rw [zLast_eq_of_split hsplit]
    exact eqvGen_of_linked d L₂ hl₂
      (fun ρ hρ u hu ↦ hoff u (Or.inr (mem_segsVerts (List.mem_append_right _ hρ) hu)))
      (hs'' (mem_pathVerts_end _))
  have h6 : Relation.EqvGen (AdjOff z.hull c) cs d := eqvGen_of_path s'' hs''
  have hconn : Relation.EqvGen (AdjOff z.hull c) ct cs :=
    h1.trans _ _ _ (h2.symm.trans _ _ _ (h3.trans _ _ _ (h4.symm.trans _ _ _
      (h5.symm.trans _ _ _ h6.symm))))
  have hout := outComp_of_coboundary hcH hmin hcob γt γs hctH hcsH (hloop γt) (hloop γs) hconn
  obtain ⟨L, hL⟩ := exists_bwalk_of_outComp γt γs hctH hcsH (hloop γt) (hloop γs) hout
  exact exists_minC (nonempty_bchain L hL)

/-- **Fischbacher's (II)**: no path from the end of a zero path out of `c` reaches a bound of a
chain out of `c` (Lemma 4.2). -/
lemma not_reaches_bound {P : A → Prop} {c dl : A} (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl))
    (ht0 : pathVal t = 0) {α β : OutA c} (W : BChain c P α β) {e : A} (he : e ∈ W.bounds) :
    ¬Reaches dl e := by
  rintro ⟨q⟩
  obtain ⟨α'', γ', -, l, -, -, rfl⟩ := W.exists_of_mem_bounds he
  have := par hcf hint hsc (t.comp q) (α''.2.toPath.comp (pathOf l.x l.x_ne))
  rw [pathVal_comp, ht0, zero_comp, pathVal_toPath_comp, pathVal_pathOf] at this
  exact l.ne this.symm

omit hint hsc in
/-- Vertices of a path from the target of an arrow out of `c` are not below `c`. -/
lemma not_below_of_arrow {c x y : A} (α : RayVert.mk c ⟶ RayVert.mk x)
    (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) {u : A} (hu : u ∈ pathVerts p) :
    ¬Reaches u c := fun hr ↦ by
  obtain ⟨q⟩ := (reaches_of_mem_pathVerts p hu).1
  exact no_pos_cycle hcf (α.toPath.comp q) (by simp [Quiver.Path.length_comp]) hr

omit hcf hint hsc in
/-- Vertices of a path between two points of a convex set lie in it. -/
lemma pathVerts_subset_convex {H : Set A} (hH : ConvexR H) {x y : A}
    (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) (hx : x ∈ H) (hy : y ∈ H) :
    pathVerts p ⊆ H := fun u hu ↦ by
  obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p hu
  exact hH _ hx _ hy u h1 h2

omit hint hsc in
/-- **A one-segment cycle joins its two arrows** in any convex set containing it. -/
lemma join_cycle1 {H : Set A} (hH : ConvexR H) {c q : A} {x₁ x₂ : RayVert A}
    {s₀ : Quiver.Path (RayVert.mk c) x₁} {e₁ : x₁ ⟶ RayVert.mk q}
    {t₀ : Quiver.Path (RayVert.mk c) x₂} {e₂ : x₂ ⟶ RayVert.mk q}
    (hV : pathVerts (s₀.cons e₁) ∪ pathVerts (t₀.cons e₂) ⊆ H)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c) :
    SepComp H q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  by_contra h
  refine cyc_contra1 hcf hint hsc (s₀ := s₀) (t₀ := t₀) fun h' ↦ h (SepComp.mono ?_ h')
  refine hullOf_subset hH fun u hu ↦ ?_
  obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
  rw [List.mem_singleton] at hρ
  subst hρ
  rcases hu with hu | hu
  · exact hV (Or.inr hu)
  · exact hV (Or.inl hu)

/-- **Case B assembly**: replacing `σ` by the segments of a piece of the minimal chain, with a
left path into `dl` and a right path into `d` whose last arrows are joined to those of `t` and
`s`, shrinks the hull. -/
theorem ZWalk.Good.caseB_mid (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {c dl d : A} {y₁ y₂ : RayVert A} {t₁ : Quiver.Path (RayVert.mk c) y₁}
    {a₁ : y₁ ⟶ RayVert.mk dl} {s₁ : Quiver.Path (RayVert.mk c) y₂} {b₁ : y₂ ⟶ RayVert.mk d}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, d, t₁.cons a₁, s₁.cons b₁⟩ :: L₂)
    {α' β' : OutA c} {K : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) α' β'} (hK : IsMinC K)
    {y₃ y₄ : RayVert A} {vL₀ : Quiver.Path (RayVert.mk α'.1) y₃} {a₂ : y₃ ⟶ RayVert.mk dl}
    {wR₀ : Quiver.Path (RayVert.mk β'.1) y₄} {b₂ : y₄ ⟶ RayVert.mk d}
    (hjL : SepComp z.hull dl ⟨y₁.out, a₁.1⟩ ⟨y₃.out, a₂.1⟩)
    (hjR : SepComp z.hull d ⟨y₂.out, b₁.1⟩ ⟨y₄.out, b₂.1⟩)
    (hwR0 : pathVal (wR₀.cons b₂) ≠ 0)
    (hvV : pathVerts (vL₀.cons a₂) ⊆ z.hull) (hwV : pathVerts (wR₀.cons b₂) ⊆ z.hull)
    (hvb : ∀ u ∈ pathVerts (vL₀.cons a₂), ¬Reaches u c)
    (hwb : ∀ u ∈ pathVerts (wR₀.cons b₂), ¬Reaches u c)
    (hiL : Incomp dl (K.firstE d)) (hiR : Incomp (K.lastE dl) d) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  set σ : ZSeg A := ⟨c, dl, d, t₁.cons a₁, s₁.cons b₁⟩ with hσdef
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hcH : c ∈ z.hull :=
    z.verts_subset_hull (z.seg_verts_subset hσ (Or.inl (mem_pathVerts_start _)))
  have hP : ∀ e b' : A, (e ∈ z.hull ∧ e ≠ c) → Reaches c b' → Reaches b' e → b' ≠ c →
      (b' ∈ z.hull ∧ b' ≠ c) := fun e b' he h1 h2 h3 ↦
    ⟨z.convexR_hull _ hcH _ he.1 b' h1 h2, h3⟩
  obtain ⟨-, -, hjl, hjr⟩ := hz.sepPairs hcf hint hsc hsplit
  obtain ⟨hNl, hNlast⟩ := segsOf_linked K (vL₀.cons a₂) (wR₀.cons b₂)
  refine hz.replace_mid hcf hint hsc hsplit (segsOf K (vL₀.cons a₂) (wR₀.cons b₂))
    (segsOf_ne_nil _ _ _) hNl hNlast
    (segsOf_pos hK _ _ (by simp) (by simp) hwR0)
    (segsOf_incomp hcf hint hsc hK _ _ hiL hiR)
    (segsOf_verts z.convexR_hull hcH (fun e he ↦ he.1) K _ _ hvV hwV) ?_ ?_
  · intro u hu hr
    rcases segsOf_below hcf K _ _ hu hr with hu | hu
    · exact hvb u hu hr
    · exact hwb u hu hr
  · intro H hH hcH' hHz hNH
    refine ⟨segsOf_sep hL hR hCB hcf hP (fun e he ↦ he.2) hH hcH' hK _ _ hNH, ?_, ?_⟩
    · intro ρ₁ hρ₁ ρ₂ hρ₂
      obtain ⟨s₀, R, hR'⟩ := segsOf_head K (vL₀.cons a₂) (wR₀.cons b₂)
      rw [hR', List.head?_cons, Option.mem_def, Option.some.injEq] at hρ₂
      subst hρ₂
      exact sepPair_left hHz hjL (hjl ρ₁ hρ₁)
    · intro ρ₁ hρ₁ ρ₂ hρ₂
      obtain ⟨R, tl, hR'⟩ := segsOf_last K (vL₀.cons a₂) (wR₀.cons b₂)
      rw [hR', List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hρ₁
      subst hρ₁
      exact sepPair_right hHz hjR (hjr ρ₂ hρ₂)

omit hcf hint hsc in
lemma exists_cons_of_pos {x y : RayVert A} (p : Quiver.Path x y) (hp : 0 < p.length) :
    ∃ (y' : RayVert A) (p₀ : Quiver.Path x y') (e : y' ⟶ y), p = p₀.cons e := by
  rcases p with _ | ⟨p₀, e⟩
  · simp at hp
  · exact ⟨_, p₀, e, rfl⟩

/-- **Case B, all cases but the end case.** The end case (the last kept bound lies above `d`) is
the hypothesis `hend`. -/
theorem ZWalk.Good.caseB_core (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {c ct cs dl d : A} {γt : RayVert.mk c ⟶ RayVert.mk ct} {γs : RayVert.mk c ⟶ RayVert.mk cs}
    {y₁ : RayVert A} {t₀ : Quiver.Path (RayVert.mk ct) y₁} {a₁ : y₁ ⟶ RayVert.mk dl}
    {s'' : Quiver.Path (RayVert.mk cs) (RayVert.mk d)}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, d, γt.toPath.comp (t₀.cons a₁), γs.toPath.comp s''⟩ :: L₂)
    (ht0 : pathVal (γt.toPath.comp (t₀.cons a₁)) = 0)
    {W : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) ⟨ct, γt⟩ ⟨cs, γs⟩} (hW : IsMinC W)
    (hend : ∀ (α' : OutA c) (K₀ : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) α' ⟨cs, γs⟩),
      IsMinC K₀ → (∀ e ∈ K₀.bounds, ¬Reaches e dl ∧ ¬Reaches e d ∧ ¬Reaches dl e) →
      K₀.bounds ≠ [] →
      Reaches d (K₀.lastE dl) → ∀ {y₃ : RayVert A} (vL₀ : Quiver.Path (RayVert.mk α'.1) y₃)
      (a₂ : y₃ ⟶ RayVert.mk dl), SepComp z.hull dl ⟨y₁.out, a₁.1⟩ ⟨y₃.out, a₂.1⟩ →
      pathVerts (vL₀.cons a₂) ⊆ z.hull → (∀ u ∈ pathVerts (vL₀.cons a₂), ¬Reaches u c) →
      ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  set σ : ZSeg A := ⟨c, dl, d, γt.toPath.comp (t₀.cons a₁), γs.toPath.comp s''⟩ with hσdef
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hσV : σ.verts ⊆ z.hull := fun u hu ↦ z.verts_subset_hull (z.seg_verts_subset hσ hu)
  have hcH : c ∈ z.hull := hσV (Or.inl (mem_pathVerts_start _))
  have hdH : d ∈ z.hull := hσV (Or.inr (mem_pathVerts_end _))
  have hdlH : dl ∈ z.hull := hσV (Or.inl (mem_pathVerts_end _))
  have hσinc := hz.incomp σ hσ
  have hsne : pathVal (γs.toPath.comp s'') ≠ 0 := hz.sne σ hσ
  obtain ⟨y₂, s₁, b₁, hs₁⟩ := exists_cons_of_pos (γs.toPath.comp s'')
    (by simp [Quiver.Path.length_comp])
  -- `dl` reaches no bound of `W`
  have hII : ∀ e ∈ W.bounds, ¬Reaches dl e := fun e he ↦
    not_reaches_bound hcf hint hsc _ ht0 W he
  -- the hull minus `c` part of the bounds
  -- the main step, after the left cut
  have main : ∀ (α' : OutA c) (K₀ : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) α' ⟨cs, γs⟩),
      IsMinC K₀ →
      (∀ e ∈ K₀.bounds, ¬Reaches e dl) → (∀ e ∈ K₀.bounds, ¬Reaches dl e) →
      ∀ {y₃ : RayVert A} (vL₀ : Quiver.Path (RayVert.mk α'.1) y₃) (a₂ : y₃ ⟶ RayVert.mk dl),
      SepComp z.hull dl ⟨y₁.out, a₁.1⟩ ⟨y₃.out, a₂.1⟩ → pathVerts (vL₀.cons a₂) ⊆ z.hull →
      (∀ u ∈ pathVerts (vL₀.cons a₂), ¬Reaches u c) →
      ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
    intro α' K₀ hK₀ hK₀dl hdlK₀ y₃ vL₀ a₂ hjL hvV hvb
    have hiL : ∀ {β' : OutA c} (K : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) α' β'),
        (∀ e ∈ K.bounds, e ∈ K₀.bounds) →
        Incomp dl (K.firstE d) := by
      intro β' K hKK
      by_cases hKb : K.bounds = []
      · rw [BChain.firstE_of_bounds K hKb]; exact hσinc
      · have hm := hKK _ (BChain.firstE_mem K hKb d)
        exact ⟨hdlK₀ _ hm, hK₀dl _ hm⟩
    have hsplit' : z.segs = L₁ ++ ⟨c, dl, d, (γt.toPath.comp t₀).cons a₁, s₁.cons b₁⟩ :: L₂ := by
      rw [hsplit, hσdef, hs₁]; rfl
    have hsV : pathVerts (s₁.cons b₁) ⊆ z.hull := fun u hu ↦ hσV (Or.inr (by rw [hσdef, hs₁]; exact hu))
    rcases K₀.split_first (fun e ↦ Reaches e d) with hR0 | ⟨β'', β', K, l', K₂, hK₀eq, hl'd, hKd⟩
    · -- no right cut
      by_cases hb : K₀.bounds ≠ [] ∧ Reaches d (K₀.lastE dl)
      · exact hend α' K₀ hK₀ (fun e he ↦ ⟨hK₀dl e he, hR0 e he, hdlK₀ e he⟩) hb.1 hb.2 vL₀ a₂
          hjL hvV hvb
      have hs''pos : 0 < s''.length := by
        by_contra h0
        have hcsd : RayVert.mk cs = RayVert.mk d := Quiver.Path.eq_of_length_zero s'' (by omega)
        change cs = d at hcsd
        subst hcsd
        rcases K₀.eq_snoc with hKb | ⟨α₁, K', l, hKeq⟩
        · cases K₀ with
          | nil => exact hσinc.2 ⟨vL₀.cons a₂⟩
          | cons l _ => simp [BChain.bounds] at hKb
        · apply hb
          refine ⟨by rw [hKeq, BChain.bounds_append]; simp [BChain.bounds], ?_⟩
          rw [hKeq, BChain.lastE_snoc]
          exact reaches_of_ne_zero l.y l.y_ne
      obtain ⟨y', s₀', b', rfl⟩ := exists_cons_of_pos s'' hs''pos
      have hjR : SepComp z.hull d ⟨y₂.out, b₁.1⟩ ⟨y'.out, b'.1⟩ := by
        have h := hs₁
        change (γs.toPath.comp s₀').cons b' = s₁.cons b₁ at h
        simp only [Quiver.Path.cons.injEq] at h
        obtain ⟨rfl, -, hb'⟩ := h
        obtain rfl := eq_of_heq hb'
        exact Relation.EqvGen.refl _
      refine hz.caseB_mid hcf hint hsc hL hR hCB hsplit' hK₀ (wR₀ := s₀') hjL hjR ?_ hvV ?_ hvb
        (fun u hu ↦ not_below_of_arrow hcf γs (s₀'.cons b') hu) (hiL K₀ fun e he ↦ he) ?_
      · intro h0
        apply hsne
        rw [pathVal_toPath_comp, h0, comp_zero]
      · exact fun u hu ↦ hσV (Or.inr (by rw [pathVerts_comp]; exact Or.inr hu))
      · by_cases hKb : K₀.bounds = []
        · rw [BChain.lastE_of_bounds K₀ hKb]; exact hσinc
        · rcases K₀.eq_snoc with hKb' | ⟨α₁, K', l, hKeq⟩
          · exact absurd hKb' hKb
          · have hm : l.e ∈ K₀.bounds := by
              rw [hKeq, BChain.bounds_append]; simp [BChain.bounds]
            rw [hKeq, BChain.lastE_snoc]
            rw [hKeq, BChain.lastE_snoc] at hb
            exact ⟨hR0 _ hm, fun h ↦ hb ⟨by rw [← hKeq]; exact hKb, h⟩⟩
    · -- right cut at the first bound below `d`
      obtain ⟨pR⟩ := hl'd
      have hK₀' : IsMinC (K.append (BChain.cons l' K₂)) := hK₀eq ▸ hK₀
      have hK : IsMinC K := hK₀'.left
      have hl' : IsMinC (BChain.cons l' (BChain.nil β')) := hK₀'.right.head
      have hwpos : 0 < ((pathOf l'.x l'.x_ne).comp pR).length := by
        rw [Quiver.Path.length_comp]; have := hl'.pos.1; omega
      obtain ⟨y₄, wR₀, b₂, hwR⟩ := exists_cons_of_pos _ hwpos
      have hβH : β''.1 ∈ z.hull :=
        z.convexR_hull _ hcH _ l'.he.1 _ ⟨β''.2.toPath⟩ (reaches_of_ne_zero l'.x l'.x_ne)
      have hwV : pathVerts (wR₀.cons b₂) ⊆ z.hull := by
        rw [← hwR, pathVerts_comp]
        rintro u (hu | hu)
        · exact pathVerts_subset_convex z.convexR_hull _ hβH l'.he.1 hu
        · exact pathVerts_subset_convex z.convexR_hull _ l'.he.1 hdH hu
      have hjR : SepComp z.hull d ⟨y₂.out, b₁.1⟩ ⟨y₄.out, b₂.1⟩ := by
        refine Relation.EqvGen.symm _ _ (join_cycle1 hcf z.convexR_hull
          (s₀ := β''.2.toPath.comp wR₀) (t₀ := s₁) ?_ hint hsc)
        rintro u (hu | hu)
        · change u ∈ pathVerts (β''.2.toPath.comp (wR₀.cons b₂)) at hu
          rw [pathVerts_comp] at hu
          rcases hu with hu | hu
          · exact pathVerts_subset_convex z.convexR_hull _ hcH hβH hu
          · exact hwV hu
        · exact hsV hu
      have hwR0 : pathVal (wR₀.cons b₂) ≠ 0 := by
        intro h0
        apply hsne
        rw [← par hcf hint hsc (β''.2.toPath.comp (wR₀.cons b₂)) _, pathVal_toPath_comp, h0,
          comp_zero]
      have hKK₀ : ∀ e ∈ K.bounds, e ∈ K₀.bounds := fun e he ↦ by
        rw [hK₀eq, BChain.bounds_append]; exact List.mem_append_left _ he
      refine hz.caseB_mid hcf hint hsc hL hR hCB hsplit' hK hjL hjR hwR0 hvV hwV hvb
        (fun u hu ↦ not_below_of_arrow hcf β''.2 _ hu) (hiL K hKK₀) ?_
      by_cases hKb : K.bounds = []
      · rw [BChain.lastE_of_bounds K hKb]; exact hσinc
      · rcases K.eq_snoc with hKb' | ⟨α₁, K', l, hKeq⟩
        · exact absurd hKb' hKb
        · have hm : l.e ∈ K.bounds := by rw [hKeq, BChain.bounds_append]; simp [BChain.bounds]
          rw [hKeq, BChain.lastE_snoc]
          refine ⟨hKd _ hm, fun h ↦ ?_⟩
          have h3 : IsMinC (K'.append (BChain.cons l (BChain.cons l' K₂))) := by
            have := hK₀'
            rw [hKeq, BChain.append_assoc] at this
            exact this
          exact (bound_incomp hcf hint hsc (IsMinC.left
            (W := BChain.cons l (BChain.cons l' (BChain.nil _))) (W' := K₂) h3.right)).2
            (Reaches.trans ⟨pR⟩ h)
  -- the left cut
  have htV : pathVerts (t₀.cons a₁) ⊆ z.hull := fun u hu ↦
    hσV (Or.inl (by rw [pathVerts_comp]; exact Or.inr hu))
  rcases W.split_last (fun e ↦ Reaches e dl) with hL0 | ⟨α'', α', W₀, l, K₀, hWeq, hlQ, hK₀⟩
  · exact main _ W hW hL0 hII t₀ a₁ (Relation.EqvGen.refl _) htV
      (fun u hu ↦ not_below_of_arrow hcf γt _ hu)
  · obtain ⟨pL⟩ := hlQ
    have hW' : IsMinC (W₀.append (BChain.cons l K₀)) := hWeq ▸ hW
    have hl : IsMinC (BChain.cons l (BChain.nil α')) := hW'.right.head
    have hvpos : 0 < ((pathOf l.y l.y_ne).comp pL).length := by
      rw [Quiver.Path.length_comp]; have := hl.pos.2; omega
    obtain ⟨y₃, vL₀, a₂, hvL⟩ := exists_cons_of_pos _ hvpos
    have hαH : α'.1 ∈ z.hull :=
      z.convexR_hull _ hcH _ l.he.1 _ ⟨α'.2.toPath⟩ (reaches_of_ne_zero l.y l.y_ne)
    have hvV : pathVerts (vL₀.cons a₂) ⊆ z.hull := by
      rw [← hvL, pathVerts_comp]
      rintro u (hu | hu)
      · exact pathVerts_subset_convex z.convexR_hull _ hαH l.he.1 hu
      · exact pathVerts_subset_convex z.convexR_hull _ l.he.1 hdlH hu
    have hjL : SepComp z.hull dl ⟨y₁.out, a₁.1⟩ ⟨y₃.out, a₂.1⟩ := by
      refine Relation.EqvGen.symm _ _ (join_cycle1 hcf z.convexR_hull
        (s₀ := α'.2.toPath.comp vL₀) (t₀ := γt.toPath.comp t₀) ?_ hint hsc)
      rintro u (hu | hu)
      · change u ∈ pathVerts (α'.2.toPath.comp (vL₀.cons a₂)) at hu
        rw [pathVerts_comp] at hu
        rcases hu with hu | hu
        · exact pathVerts_subset_convex z.convexR_hull _ hcH hαH hu
        · exact hvV hu
      · exact hσV (Or.inl hu)
    have hK₀W : ∀ e ∈ K₀.bounds, e ∈ W.bounds := fun e he ↦ by
      rw [hWeq, BChain.bounds_append]; simp [BChain.bounds, he]
    exact main α' K₀ hW'.right.tail hK₀ (fun e he ↦ hII e (hK₀W e he)) vL₀ a₂ hjL hvV
      (fun u hu ↦ not_below_of_arrow hcf α'.2 _ hu)

end LargeIndecomposable.RayCat
