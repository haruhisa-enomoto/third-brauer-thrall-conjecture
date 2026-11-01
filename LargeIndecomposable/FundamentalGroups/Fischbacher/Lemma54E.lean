module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma53C

/-!
# Fischbacher §5.4: the end case of Case B

The last kept bound `e` of the chain lies above the right peak `d` of the replaced segment. Then
the new peak `e` is joined to the later old peaks one at a time: while the next old peak lies
below `e`, its segment is dropped, and a one-segment cycle avoiding `c` moves the separation at
`e` along (Lemma 4.4); at the last old peak the end of the walk is rebuilt along `w` as for the
initial walk. Separation at `e` starts from Lemma 4.3 for the last link.
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

/-- No point of the hull of a good walk lies strictly below a valley. -/
lemma ZWalk.Good.eq_of_hull_below {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) {y : A} (hy : y ∈ z.hull)
    (hr : Reaches y σ.c) : y = σ.c := by
  obtain ⟨u, hu, -, -, h1, -⟩ := hy
  rcases ZWalk.mem_verts_split hcf hint hsc hsplit hu with hu | hu
  · exact (hz.key hcf hint hsc hsplit hu (h1.trans hr)).elim
  · have := ZSeg.eq_of_reaches_c hcf hu (h1.trans hr)
    subst this
    exact eq_of_reaches_both hcf hr h1

/-- The hull of a good walk without a valley is convex. -/
lemma ZWalk.Good.convexR_hull_diff {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) : ConvexR (z.hull \ {σ.c}) := by
  intro y₁ hy₁ y₂ hy₂ y h1 h2
  refine ⟨z.convexR_hull _ hy₁.1 _ hy₂.1 y h1 h2, fun hyc ↦ hy₁.2 ?_⟩
  rw [Set.mem_singleton_iff] at hyc ⊢
  subst hyc
  exact hz.eq_of_hull_below hcf hint hsc hsplit hy₁.1 h1

omit hint hsc in
/-- **Lemma 4.3 for a minimal link.** -/
lemma link_not_sepComp (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {c : A} {P : A → Prop} (hP : ∀ e b' : A, P e → Reaches c b' → Reaches b' e → b' ≠ c → P b')
    (hPc : ∀ e, P e → e ≠ c) {α β : OutA c} {l : BLink c P α β}
    (hl : IsMinC (BChain.cons l (BChain.nil β))) {H : Set A} (hH : ConvexR H) (hcH : c ∉ H)
    (heH : l.e ∈ H) {x₁ x₂ : RayVert A} {s₀ : Quiver.Path (RayVert.mk α.1) x₁}
    {e₁ : x₁ ⟶ RayVert.mk l.e} {t₀ : Quiver.Path (RayVert.mk β.1) x₂}
    {e₂ : x₂ ⟶ RayVert.mk l.e} (hx : pathOf l.x l.x_ne = s₀.cons e₁)
    (hy : pathOf l.y l.y_ne = t₀.cons e₂) (hx₁ : x₁.out ∈ H) (hx₂ : x₂.out ∈ H) :
    ¬SepComp H l.e ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  let C : EssCfg (α.2.1 ≫ l.x) :=
    { x := x₁.out, y := x₂.out, α := e₁, β := e₂,
      v := α.2.toPath.comp s₀, w := β.2.toPath.comp t₀,
      hv := by
        change pathVal (α.2.toPath.comp (s₀.cons e₁)) = _
        rw [← hx, pathVal_toPath_comp, pathVal_pathOf]
      hw := by
        change pathVal (β.2.toPath.comp (t₀.cons e₂)) = _
        rw [← hy, pathVal_toPath_comp, pathVal_pathOf, l.eq]
      hess := by
        change ¬Interlaced (α.2.toPath.comp (s₀.cons e₁)) (β.2.toPath.comp (t₀.cons e₂))
        rw [← hx, ← hy]
        exact hl.essential hcf (fun b' h1 h2 h3 ↦ hP _ b' l.he h1 h2 h3) (hPc _ l.he) }
  have hD : ∀ g : Σ y : A, y ⟶ l.e, g.1 ∈ H → g.2 ≠ 0 → ¬Thr (α.2.1 ≫ l.x) g.2 := by
    rintro g hg hg0 ⟨p, hp⟩
    have hp0 : p ≠ 0 := fun h0 ↦ hg0 (by rw [hp, h0, zero_comp])
    exact hcH (hH _ hg _ heH c (reaches_of_ne_zero p hp0) (reaches_of_ne_zero _ l.ne))
  have hloop : ∀ (z : RayVert A) (e' : z ⟶ RayVert.mk l.e), z.out ≠ l.e := by
    intro z e' hz
    have hz' : z = RayVert.mk l.e := hz
    subst hz'
    have := hcf _ e'.toPath
    simp at this
  exact not_sepComp_of_essCfg hL hR hCB l.ne C hD hx₁ hx₂ (hloop _ e₁) (hloop _ e₂)

/-- **Joining the new peak `e` to the later old peaks.** Starting from a path `p` from an old
peak `Q` (with the old segments `R` after it) up to `e`, whose last arrow is separated from the
left arrow `e₁` at `e`, the end of the walk is rebuilt (`hfinish`). -/
theorem ZWalk.Good.end_loop {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) {e : A} (hde : Reaches σ.d e)
    (heH : e ∈ z.hull) (hb : ¬Reaches b e) {x₁ : RayVert A} (e₁ : x₁ ⟶ RayVert.mk e)
    (hd4 : ∀ ρ ∈ L₂, Incomp σ.d ρ.d)
    (hfinish : ∀ (Tail : List (ZSeg A)) (w'' : Quiver.Path (RayVert.mk (ZLast e Tail))
        (RayVert.mk b)), ZLinked e Tail →
      (∃ w₁ : Quiver.Path (RayVert.mk a₀) (RayVert.mk (ZLast e Tail)), w = w₁.comp w'') →
      (∀ ρ ∈ Tail, 0 < ρ.t.length ∧ 0 < ρ.s.length ∧ pathVal ρ.s ≠ 0) →
      (∀ ρ ∈ Tail, Incomp ρ.dl ρ.d) → segsVerts Tail ∪ pathVerts w'' ⊆ z.hull →
      (∀ u ∈ segsVerts Tail ∪ pathVerts w'', ¬Reaches u σ.c) →
      (∀ H : Set A, ConvexR H → σ.c ∉ H → H ⊆ z.hull → segsVerts Tail ⊆ H →
        SepAll H Tail ∧ ∀ ρ ∈ Tail.head?, ∀ (c' d' : A) (x₂ : RayVert A)
          (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk e)
          (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
          ρ = ⟨c', e, d', t₀.cons e₂, s'⟩ → ¬SepComp H e ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩) →
      ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull) :
    ∀ (R : List (ZSeg A)) (Q : A), (∃ R₀, L₂ = R₀ ++ R ∧ ZLast σ.d R₀ = Q) →
      ∀ (p : Quiver.Path (RayVert.mk Q) (RayVert.mk e)), 0 < p.length →
      (∀ (x₂ : RayVert A) (p₀ : Quiver.Path (RayVert.mk Q) x₂) (e₂ : x₂ ⟶ RayVert.mk e),
        p = p₀.cons e₂ → ¬SepComp (z.hull \ {σ.c}) e ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩) →
      ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  have hH' := hz.convexR_hull_diff hcf hint hsc hsplit
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hcH : σ.c ∈ z.hull :=
    z.verts_subset_hull (z.seg_verts_subset hσ (Or.inl (mem_pathVerts_start _)))
  have hkey : ∀ {u : A}, u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂) →
      ¬Reaches u σ.c := fun hu hr ↦ hz.key hcf hint hsc hsplit hu hr
  have hL₂ : ∀ ρ ∈ L₂, ρ ∈ z.segs := fun ρ h ↦ by rw [hsplit]; simp [h]
  have hL₂V : ∀ ρ ∈ L₂, ∀ u ∈ ρ.verts, u ∈ z.hull ∧ ¬Reaches u σ.c := fun ρ hρ u hu ↦
    ⟨z.verts_subset_hull (z.seg_verts_subset (hL₂ ρ hρ) hu),
      hkey (Or.inr (mem_segsVerts (List.mem_append_right _ hρ) hu))⟩
  have hw'V : ∀ u ∈ pathVerts z.w', u ∈ z.hull ∧ ¬Reaches u σ.c := fun u hu ↦
    ⟨z.verts_subset_hull (Or.inl (Or.inr hu)), hkey (Or.inl (Or.inr hu))⟩
  -- vertices of a path from a point not below `c` up to `e`
  have hup : ∀ {Q : A} (p : Quiver.Path (RayVert.mk Q) (RayVert.mk e)), Q ∈ z.hull →
      ¬Reaches Q σ.c → ∀ u ∈ pathVerts p, u ∈ z.hull \ {σ.c} ∧ ¬Reaches u σ.c := by
    intro Q p hQ hQc u hu
    obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p hu
    refine ⟨⟨z.convexR_hull _ hQ _ heH u h1 h2, fun h ↦ hQc ?_⟩, fun h ↦ hQc (h1.trans h)⟩
    rw [Set.mem_singleton_iff.1 h] at h1; exact h1
  have hdiff : ∀ {u : A}, u ∈ z.hull → ¬Reaches u σ.c → u ∈ z.hull \ {σ.c} := fun hu hr ↦
    ⟨hu, fun h ↦ hr (by rw [Set.mem_singleton_iff.1 h]; exact Reaches.refl _)⟩
  have hl := z.linked
  rw [hsplit, zLinked_append] at hl
  obtain ⟨-, -, hl₂⟩ := hl
  obtain ⟨-, hc₂, -, -⟩ := hz.sepPairs hcf hint hsc hsplit
  intro R
  induction R with
  | nil =>
    intro Q ⟨R₀, hR₀, hQ⟩ p hp inv
    rw [List.append_nil] at hR₀
    subst hR₀
    have hQl : Q = ZLast z.d₀ z.segs := by rw [zLast_eq_of_split hsplit, hQ]
    subst hQl
    obtain ⟨w₁, hw⟩ := hz.along
    have hQV := hw'V _ (mem_pathVerts_start z.w')
    obtain ⟨c'', y, w₃, α, w₄, heq, hc''e, hye⟩ := find_end _ z.w' rfl ⟨p⟩ hb
    have hw₃V : ∀ u ∈ pathVerts w₃, u ∈ z.hull ∧ ¬Reaches u σ.c := fun u hu ↦
      hw'V u (by rw [heq, pathVerts_comp]; exact Or.inl hu)
    have hαw₄V : ∀ u ∈ pathVerts (α.toPath.comp w₄), u ∈ z.hull ∧ ¬Reaches u σ.c :=
      fun u hu ↦ hw'V u (by rw [heq, pathVerts_comp]; exact Or.inr hu)
    have hc''V := hw₃V _ (mem_pathVerts_end w₃)
    by_cases hce : c'' = e
    · subst hce
      refine hfinish [] (α.toPath.comp w₄) trivial ⟨w₁.comp w₃, ?_⟩ (by simp) (by simp)
        ?_ ?_ ?_
      · show w = (w₁.comp w₃).comp (α.toPath.comp w₄)
        rw [hw, heq, Quiver.Path.comp_assoc]
      · rintro u (hu | hu)
        · simp [segsVerts] at hu
        · exact (hαw₄V u hu).1
      · rintro u (hu | hu)
        · simp [segsVerts] at hu
        · exact (hαw₄V u hu).2
      · intro H _ _ _ _
        refine ⟨fun L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ _ h ↦ ?_, by simp⟩
        have := congrArg List.length h
        simp at this
    · obtain ⟨tn⟩ := hc''e
      have htn : 0 < tn.length := by
        by_contra h0
        exact hce (show RayVert.mk c'' = RayVert.mk e from
          Quiver.Path.eq_of_length_zero tn (by omega))
      obtain ⟨x₃, tn₀, e₃, rfl⟩ := exists_cons_of_pos tn htn
      have htnV : ∀ u ∈ pathVerts (tn₀.cons e₃), u ∈ z.hull \ {σ.c} ∧ ¬Reaches u σ.c :=
        hup _ hc''V.1 hc''V.2
      have hyV := hαw₄V y (by rw [pathVerts_comp]; exact Or.inr (mem_pathVerts_start _))
      refine hfinish [⟨c'', e, y, tn₀.cons e₃, α.toPath⟩] w₄ ⟨rfl, trivial⟩
        ⟨(w₁.comp w₃).comp α.toPath, ?_⟩ ?_ ?_ ?_ ?_ ?_
      · show w = ((w₁.comp w₃).comp α.toPath).comp w₄
        rw [hw, heq, Quiver.Path.comp_assoc, Quiver.Path.comp_assoc]
      · intro ρ hρ
        rw [List.mem_singleton] at hρ
        subst hρ
        refine ⟨by simp, by simp, ?_⟩
        change 𝟙 _ ≫ α.1 ≠ 0
        rw [Category.id_comp]; exact α.2.1
      · intro ρ hρ
        rw [List.mem_singleton] at hρ
        subst hρ
        exact incomp_end hcf hint hsc α _ htn hye
      · rintro u (hu | hu)
        · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
          rw [List.mem_singleton] at hρ
          subst hρ
          rcases hu with hu | hu
          · exact (htnV u hu).1.1
          · exact (hαw₄V u (by rw [pathVerts_comp]; exact Or.inl hu)).1
        · exact (hαw₄V u (by rw [pathVerts_comp]; exact Or.inr hu)).1
      · rintro u (hu | hu)
        · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
          rw [List.mem_singleton] at hρ
          subst hρ
          rcases hu with hu | hu
          · exact (htnV u hu).2
          · exact (hαw₄V u (by rw [pathVerts_comp]; exact Or.inl hu)).2
        · exact (hαw₄V u (by rw [pathVerts_comp]; exact Or.inr hu)).2
      · intro H hH hcH' hHz _
        have hHH' : H ⊆ z.hull \ {σ.c} := fun u hu ↦
          ⟨hHz hu, fun h ↦ hcH' (by rw [Set.mem_singleton_iff.1 h] at hu; exact hu)⟩
        refine ⟨fun L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ _ h ↦ ?_, ?_⟩
        · have := congrArg List.length h
          simp at this
          omega
        intro ρ hρ c' d' x₂ t₀ e₂ s' hρeq hS
        rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hρ
        subst hρ
        simp only [ZSeg.mk.injEq] at hρeq
        obtain ⟨rfl, -, rfl, ht, -⟩ := hρeq
        have ht' := eq_of_heq ht
        simp only [Quiver.Path.cons.injEq] at ht'
        obtain ⟨rfl, -, he⟩ := ht'
        obtain rfl := eq_of_heq he
        obtain ⟨xp, p₀, ep, rfl⟩ := exists_cons_of_pos p hp
        have hj := join_cycle1 hcf hH' (s₀ := w₃.comp tn₀) (e₁ := e₃) (t₀ := p₀) (e₂ := ep)
          (by
            rintro u (hu | hu)
            · change u ∈ pathVerts (w₃.comp (tn₀.cons e₃)) at hu
              rw [pathVerts_comp] at hu
              rcases hu with hu | hu
              · exact hdiff (hw₃V u hu).1 (hw₃V u hu).2
              · exact (htnV u hu).1
            · exact (hup _ hQV.1 hQV.2 u hu).1) hint hsc
        exact inv xp p₀ ep rfl ((SepComp.mono hHH' hS).trans _ _ _ hj)
  | cons ρ R ih =>
    intro Q ⟨R₀, hR₀, hQ⟩ p hp inv
    have hρL : ρ ∈ L₂ := by rw [hR₀]; simp
    have hl' := hl₂
    rw [hR₀, zLinked_append, hQ] at hl'
    obtain ⟨-, hρdl, hlR⟩ := hl'
    obtain ⟨c', Q', Q'', t', s'⟩ := ρ
    change Q' = Q at hρdl
    subst hρdl
    have hρV := hL₂V _ hρL
    have hQ'V := hρV Q' (Or.inl (mem_pathVerts_end _))
    have hQ''V := hρV Q'' (Or.inr (mem_pathVerts_end _))
    have hρmem := hL₂ _ hρL
    by_cases hq : Reaches Q'' e
    · obtain ⟨q⟩ := hq
      have hqpos : 0 < q.length := by
        by_contra h0
        have hQe : RayVert.mk Q'' = RayVert.mk e := Quiver.Path.eq_of_length_zero q (by omega)
        change Q'' = e at hQe
        subst hQe
        exact (hd4 _ hρL).1 hde
      refine ih Q'' ⟨R₀ ++ [⟨c', Q', Q'', t', s'⟩], by simp [hR₀], ?_⟩ q hqpos ?_
      · rw [zLast_append, hQ]; rfl
      · intro x₂ q₀ e₂' hq₀ hS
        subst hq₀
        obtain ⟨xp, p₀, ep, rfl⟩ := exists_cons_of_pos p hp
        have hj := join_cycle1 hcf hH' (s₀ := s'.comp q₀) (e₁ := e₂') (t₀ := t'.comp p₀)
          (e₂ := ep) (by
            rintro u (hu | hu)
            · change u ∈ pathVerts (s'.comp (q₀.cons e₂')) at hu
              rw [pathVerts_comp] at hu
              rcases hu with hu | hu
              · exact hdiff (hρV u (Or.inr hu)).1 (hρV u (Or.inr hu)).2
              · exact (hup _ hQ''V.1 hQ''V.2 u hu).1
            · change u ∈ pathVerts (t'.comp (p₀.cons ep)) at hu
              rw [pathVerts_comp] at hu
              rcases hu with hu | hu
              · exact hdiff (hρV u (Or.inl hu)).1 (hρV u (Or.inl hu)).2
              · exact (hup _ hQ'V.1 hQ'V.2 u hu).1) hint hsc
        exact inv xp p₀ ep rfl (hS.trans _ _ _ hj)
    · have hlast : ZLast z.d₀ z.segs = ZLast e (⟨c', e, Q'', t'.comp p, s'⟩ :: R) := by
        rw [zLast_eq_of_split hsplit, hR₀, zLast_append, hQ]; rfl
      have hR : ∀ ρ ∈ R, ρ ∈ L₂ := fun ρ h ↦ by rw [hR₀]; simp [h]
      obtain ⟨-, -, hcR⟩ : _ ∧ _ ∧ (⟨c', Q', Q'', t', s'⟩ :: R).IsChain (SepPair z.hull) := by
        have := hc₂
        rw [hR₀, List.isChain_append] at this
        exact ⟨trivial, trivial, this.2.1⟩
      have hspos := hz.spos _ hρmem
      obtain ⟨xs, s₀', bs, hs'⟩ := exists_cons_of_pos s' hspos
      refine hfinish (⟨c', e, Q'', t'.comp p, s'⟩ :: R) (hlast ▸ z.w') ⟨rfl, hlR⟩ ?_ ?_ ?_ ?_
        ?_ ?_
      · obtain ⟨w₁, hw⟩ := hz.along
        exact ⟨hlast ▸ w₁, by rw [comp_cast]; exact hw⟩
      · intro ρ hρ
        rcases List.mem_cons.1 hρ with rfl | hρ
        · exact ⟨by simp [Quiver.Path.length_comp, hp], hspos, hz.sne ⟨c', Q', Q'', t', s'⟩ hρmem⟩
        · exact ⟨hz.tpos ρ (hL₂ ρ (hR ρ hρ)), hz.spos ρ (hL₂ ρ (hR ρ hρ)),
            hz.sne ρ (hL₂ ρ (hR ρ hρ))⟩
      · intro ρ hρ
        rcases List.mem_cons.1 hρ with rfl | hρ
        · exact ⟨fun h ↦ (hd4 _ hρL).1 (hde.trans h), hq⟩
        · exact hz.incomp ρ (hL₂ ρ (hR ρ hρ))
      · rintro u (hu | hu)
        · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
          rcases List.mem_cons.1 hρ with rfl | hρ
          · rcases hu with hu | hu
            · change u ∈ pathVerts (t'.comp p) at hu
              rw [pathVerts_comp] at hu
              rcases hu with hu | hu
              · exact (hρV u (Or.inl hu)).1
              · exact (hup _ hQ'V.1 hQ'V.2 u hu).1.1
            · exact (hρV u (Or.inr hu)).1
          · exact (hL₂V ρ (hR ρ hρ) u hu).1
        · rw [pathVerts_cast] at hu
          exact (hw'V u hu).1
      · rintro u (hu | hu)
        · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
          rcases List.mem_cons.1 hρ with rfl | hρ
          · rcases hu with hu | hu
            · change u ∈ pathVerts (t'.comp p) at hu
              rw [pathVerts_comp] at hu
              rcases hu with hu | hu
              · exact (hρV u (Or.inl hu)).2
              · exact (hup _ hQ'V.1 hQ'V.2 u hu).2
            · exact (hρV u (Or.inr hu)).2
          · exact (hL₂V ρ (hR ρ hρ) u hu).2
        · rw [pathVerts_cast] at hu
          exact (hw'V u hu).2
      · intro H hH hcH' hHz _
        have hHH' : H ⊆ z.hull \ {σ.c} := fun u hu ↦
          ⟨hHz hu, fun h ↦ hcH' (by rw [Set.mem_singleton_iff.1 h] at hu; exact hu)⟩
        refine ⟨?_, ?_⟩
        · rw [sepAll_iff, List.isChain_cons]
          rw [List.isChain_cons] at hcR
          refine ⟨fun ρ hρ ↦ ?_, hcR.2.imp fun _ _ ↦ SepPair.mono hHz⟩
          have := hcR.1 ρ hρ
          subst hs'
          exact sepPair_right hHz (Relation.EqvGen.refl _) this
        · intro ρ hρ c'' d' x₂ t₀ e₂ s'' hρeq hS
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hρ
          subst hρ
          simp only [ZSeg.mk.injEq] at hρeq
          obtain ⟨rfl, -, rfl, ht, -⟩ := hρeq
          obtain ⟨xp, p₀, ep, rfl⟩ := exists_cons_of_pos p hp
          have ht' := eq_of_heq ht
          change (t'.comp p₀).cons ep = t₀.cons e₂ at ht'
          simp only [Quiver.Path.cons.injEq] at ht'
          obtain ⟨rfl, -, he⟩ := ht'
          obtain rfl := eq_of_heq he
          exact inv xp p₀ ep rfl (SepComp.mono hHH' hS)

/-- Later old peaks are incomparable with the right peak of a split segment. -/
lemma ZWalk.Good.incomp_later {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {σ : ZSeg A} (hsplit : z.segs = L₁ ++ σ :: L₂) : ∀ ρ ∈ L₂, Incomp σ.d ρ.d := by
  intro ρ hρ
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hρ
  have hlen : z.segs.length = L₁.length + 1 + L₂.length := by rw [hsplit]; simp; omega
  have hpk := zPeak_seg z.d₀ z.segs z.linked
  have h1 : z.segs[L₁.length]'(by omega) = σ := by simp [hsplit]
  have h2 : z.segs[L₁.length + 1 + r]'(by omega) = L₂[r] := by
    simp only [hsplit, List.getElem_append_right (show L₁.length ≤ L₁.length + 1 + r by omega)]
    simp [show L₁.length + 1 + r - L₁.length = r + 1 by omega]
  have e1 := (hpk L₁.length (by omega)).2
  have e2 := (hpk (L₁.length + 1 + r) (by omega)).2
  rw [h1] at e1
  rw [h2] at e2
  rw [e1, e2]
  exact hz.zPeak_incomp hcf hint hsc (by omega) (by omega)

/-- **The end case of Case B** (Fischbacher §5.4, steps 3–4). -/
theorem ZWalk.Good.caseB_end (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {b a₀ : A} {z : ZWalk b}
    {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w) {L₁ L₂ : List (ZSeg A)}
    {c ct cs dl d : A} {γt : RayVert.mk c ⟶ RayVert.mk ct} {γs : RayVert.mk c ⟶ RayVert.mk cs}
    {y₁ : RayVert A} {t₀ : Quiver.Path (RayVert.mk ct) y₁} {a₁ : y₁ ⟶ RayVert.mk dl}
    {s'' : Quiver.Path (RayVert.mk cs) (RayVert.mk d)}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, d, γt.toPath.comp (t₀.cons a₁), γs.toPath.comp s''⟩ :: L₂)
    (α' : OutA c) (K₀ : BChain c (fun e ↦ e ∈ z.hull ∧ e ≠ c) α' ⟨cs, γs⟩) (hK₀ : IsMinC K₀)
    (hKb : ∀ e ∈ K₀.bounds, ¬Reaches e dl ∧ ¬Reaches e d ∧ ¬Reaches dl e)
    (hne : K₀.bounds ≠ []) (hde : Reaches d (K₀.lastE dl)) {y₃ : RayVert A}
    (vL₀ : Quiver.Path (RayVert.mk α'.1) y₃) (a₂ : y₃ ⟶ RayVert.mk dl)
    (hjL : SepComp z.hull dl ⟨y₁.out, a₁.1⟩ ⟨y₃.out, a₂.1⟩)
    (hvV : pathVerts (vL₀.cons a₂) ⊆ z.hull) (hvb : ∀ u ∈ pathVerts (vL₀.cons a₂), ¬Reaches u c) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  set σ : ZSeg A := ⟨c, dl, d, γt.toPath.comp (t₀.cons a₁), γs.toPath.comp s''⟩ with hσdef
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hσV : σ.verts ⊆ z.hull := fun u hu ↦ z.verts_subset_hull (z.seg_verts_subset hσ hu)
  have hcH : c ∈ z.hull := hσV (Or.inl (mem_pathVerts_start _))
  have hH' : ConvexR (z.hull \ {c}) := hz.convexR_hull_diff hcf hint hsc hsplit
  have hcH' : c ∉ z.hull \ {c} := fun h ↦ h.2 rfl
  have hdiff : ∀ {u : A}, u ∈ z.hull → ¬Reaches u c → u ∈ z.hull \ {c} := fun hu hr ↦
    ⟨hu, fun h ↦ hr (by rw [Set.mem_singleton_iff.1 h]; exact Reaches.refl _)⟩
  have hHd : z.hull \ {c} ⊆ z.hull := Set.diff_subset
  have hP : ∀ e b' : A, (e ∈ z.hull ∧ e ≠ c) → Reaches c b' → Reaches b' e → b' ≠ c →
      (b' ∈ z.hull ∧ b' ≠ c) := fun e b' he h1 h2 h3 ↦
    ⟨z.convexR_hull _ hcH _ he.1 b' h1 h2, h3⟩
  obtain ⟨hc₁, -, hjl, -⟩ := hz.sepPairs hcf hint hsc hsplit
  -- the last link
  obtain ⟨β'', K', l, rfl⟩ := K₀.eq_snoc.resolve_left hne
  rw [BChain.lastE_snoc] at hde
  have hK' : IsMinC K' := hK₀.left
  have hl : IsMinC (BChain.cons l (BChain.nil _)) := hK₀.right
  have hKK : ∀ e ∈ K'.bounds, e ∈ (K'.append (BChain.cons l (BChain.nil _))).bounds :=
    fun e he ↦ by rw [BChain.bounds_append]; exact List.mem_append_left _ he
  have hlb : l.e ∈ (K'.append (BChain.cons l (BChain.nil _))).bounds := by
    rw [BChain.bounds_append]; simp [BChain.bounds]
  obtain ⟨hedl, hed, hdle⟩ := hKb _ hlb
  obtain ⟨x₁, sx, e₁, hx⟩ := exists_cons_of_pos _ hl.pos.1
  obtain ⟨x₂, ty, e₂, hy⟩ := exists_cons_of_pos _ hl.pos.2
  have heH : l.e ∈ z.hull := l.he.1
  have hβH : β''.1 ∈ z.hull :=
    z.convexR_hull _ hcH _ heH _ ⟨β''.2.toPath⟩ (reaches_of_ne_zero l.x l.x_ne)
  have hcsH : cs ∈ z.hull := by
    refine hσV (Or.inr ?_)
    rw [pathVerts_comp]; exact Or.inr (mem_pathVerts_start _)
  have hxV : pathVerts (pathOf l.x l.x_ne) ⊆ z.hull \ {c} := fun u hu ↦
    hdiff (pathVerts_subset_convex z.convexR_hull _ hβH heH hu)
      (not_below_of_arrow hcf β''.2 _ hu)
  have hyV : pathVerts (pathOf l.y l.y_ne) ⊆ z.hull \ {c} := fun u hu ↦
    hdiff (pathVerts_subset_convex z.convexR_hull _ hcsH heH hu)
      (not_below_of_arrow hcf γs _ hu)
  -- the new segments up to `e`
  obtain ⟨hN'l, hN'last⟩ := segsOf_linked K' (vL₀.cons a₂) (pathOf l.x l.x_ne)
  have hN'V : segsVerts (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) ⊆ z.hull :=
    segsOf_verts z.convexR_hull hcH (fun e he ↦ he.1) K' _ _ hvV fun u hu ↦ (hxV hu).1
  have hN'b : ∀ u ∈ segsVerts (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)), ¬Reaches u c := by
    intro u hu hr
    rcases segsOf_below hcf K' _ _ hu hr with hu | hu
    · exact hvb u hu hr
    · exact not_below_of_arrow hcf β''.2 _ hu hr
  have hN'pos := segsOf_pos hK' (vL₀.cons a₂) (pathOf l.x l.x_ne) (by simp) hl.pos.1
    (by rw [pathVal_pathOf]; exact l.x_ne)
  have hiL : Incomp dl (K'.firstE l.e) := by
    by_cases hKb' : K'.bounds = []
    · rw [BChain.firstE_of_bounds K' hKb']; exact ⟨hdle, hedl⟩
    · obtain ⟨h1, -, h3⟩ := hKb _ (hKK _ (BChain.firstE_mem K' hKb' _))
      exact ⟨h3, h1⟩
  have hiR : Incomp (K'.lastE dl) l.e := by
    by_cases hKb' : K'.bounds = []
    · rw [BChain.lastE_of_bounds K' hKb']; exact ⟨hdle, hedl⟩
    · obtain ⟨α₁, K'', l₀, rfl⟩ := K'.eq_snoc.resolve_left hKb'
      rw [BChain.lastE_snoc]
      have h3 : IsMinC (K''.append (BChain.cons l₀ (BChain.cons l (BChain.nil _)))) := by
        have := hK₀
        rw [BChain.append_assoc] at this
        exact this
      exact bound_incomp hcf hint hsc h3.right
  have hN'inc := segsOf_incomp hcf hint hsc hK' (vL₀.cons a₂) (pathOf l.x l.x_ne) hiL hiR
  have hN'sep : ∀ H : Set A, ConvexR H → c ∉ H →
      segsVerts (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) ⊆ H →
      SepAll H (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) := fun H hH hcH'' hNH ↦
    segsOf_sep hL hR hCB hcf hP (fun e he ↦ he.2) hH hcH'' hK' _ _ hNH
  have hjunL : ∀ H : Set A, H ⊆ z.hull → ∀ ρ₁ ∈ L₁.getLast?,
      ∀ ρ₂ ∈ (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)).head?, SepPair H ρ₁ ρ₂ := by
    intro H hHz ρ₁ hρ₁ ρ₂ hρ₂
    obtain ⟨s₀, R, hR'⟩ := segsOf_head K' (vL₀.cons a₂) (pathOf l.x l.x_ne)
    rw [hR', List.head?_cons, Option.mem_def, Option.some.injEq] at hρ₂
    subst hρ₂
    exact sepPair_left hHz hjL (hjl ρ₁ hρ₁)
  have hL₁ : ∀ ρ ∈ L₁, ρ ∈ z.segs := fun ρ h ↦ by rw [hsplit]; exact List.mem_append_left _ h
  have hkey : ∀ {u : A}, u ∈ pathVerts z.v' ∪ pathVerts z.w' ∪ segsVerts (L₁ ++ L₂) →
      ¬Reaches u c := fun hu hr ↦ hz.key hcf hint hsc hsplit hu hr
  have hl := z.linked
  rw [hsplit, zLinked_append] at hl
  obtain ⟨hl₁, hdl, -⟩ := hl
  change dl = ZLast z.d₀ L₁ at hdl
  -- `b` is not below `e`, by (4) for the walk ending at `e`
  have hb : ¬Reaches b l.e := by
    intro hbe
    have hlin : ZLinked z.d₀ (L₁ ++ segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) :=
      (zLinked_append _ _ _).2 ⟨hl₁, hdl ▸ hN'l⟩
    have hlast : ZLast z.d₀ (L₁ ++ segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) = l.e := by
      rw [zLast_append, ← hdl, hN'last]
    have hV : segsVerts (L₁ ++ segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) ⊆ z.hull \ {c} := by
      intro u hu
      obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hdiff (z.verts_subset_hull (z.seg_verts_subset (hL₁ ρ hρ) hu))
          (hkey (Or.inr (mem_segsVerts (List.mem_append_left _ hρ) hu)))
      · exact hdiff (hN'V (mem_segsVerts hρ hu)) (hN'b u (mem_segsVerts hρ hu))
    have hd₀ : z.d₀ ∈ z.hull \ {c} :=
      hdiff (z.verts_subset_hull (Or.inl (Or.inl (mem_pathVerts_start _))))
        (hkey (Or.inl (Or.inl (mem_pathVerts_start _))))
    have hNsub : segsVerts (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) ⊆ z.hull \ {c} :=
      fun u hu ↦ hdiff (hN'V hu) (hN'b u hu)
    have hsepLN : SepAll (z.hull \ {c}) (L₁ ++ segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) := by
      rw [sepAll_iff, List.isChain_append]
      exact ⟨hc₁.imp fun _ _ ↦ SepPair.mono hHd,
        sepAll_iff.1 (hN'sep _ hH' hcH' hNsub), hjunL _ hHd⟩
    have := RayCat.zPeak_incomp hcf hint hsc hH' hlin hV hd₀
      (fun ρ hρ ↦ by
        rcases List.mem_append.1 hρ with hρ | hρ
        · exact hz.incomp ρ (hL₁ ρ hρ)
        · exact hN'inc ρ hρ) hsepLN
      (fun ρ hρ ↦ by
        rcases List.mem_append.1 hρ with hρ | hρ
        · exact ⟨hz.spos ρ (hL₁ ρ hρ), hz.tpos ρ (hL₁ ρ hρ)⟩
        · exact ⟨(hN'pos ρ hρ).2.1, (hN'pos ρ hρ).1⟩)
      0 _ (by
        have := segsOf_ne_nil K' (vL₀.cons a₂) (pathOf l.x l.x_ne)
        simp only [List.length_append]
        have := List.length_pos_of_ne_nil this
        omega) le_rfl
    rw [zPeak_zero, zPeak_length, hlast] at this
    exact this.1 (Reaches.trans (⟨z.v'⟩ : Reaches z.d₀ b) hbe)
  -- the path from `d` up to `e`
  obtain ⟨p⟩ := hde
  have hdH : d ∈ z.hull := hσV (Or.inr (mem_pathVerts_end _))
  have hdc : ¬Reaches d c := fun h ↦ by
    have := hz.eq_of_hull_below hcf hint hsc hsplit hdH h
    change d = c at this
    subst this
    exact no_pos_cycle hcf (γs.toPath.comp s'') (by simp [Quiver.Path.length_comp])
      (Reaches.refl _)
  have hp : 0 < p.length := by
    by_contra h0
    have hde' : RayVert.mk d = RayVert.mk l.e := Quiver.Path.eq_of_length_zero p (by omega)
    exact hed (by rw [← show d = l.e from hde']; exact Reaches.refl _)
  have hpV : pathVerts p ⊆ z.hull \ {c} := fun u hu ↦ by
    obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p hu
    exact hdiff (z.convexR_hull _ hdH _ heH u h1 h2) (fun h ↦ hdc (h1.trans h))
  refine hz.end_loop hcf hint hsc hsplit (e := l.e) ⟨p⟩ heH hb e₁
    (hz.incomp_later hcf hint hsc hsplit) ?_ L₂ d ⟨[], by simp, rfl⟩ p hp ?_
  · -- the final assembly
    intro Tail w'' hTl hTalong hTpos hTinc hTV hTb hTsep
    have hMl : ZLinked dl (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne) ++ Tail) :=
      (zLinked_append _ _ _).2 ⟨hN'l, by rw [hN'last]; exact hTl⟩
    have hMlast : ZLast dl (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne) ++ Tail) =
        ZLast l.e Tail := by rw [zLast_append, hN'last]
    refine hz.replace hcf hint hsc hsplit _ (by simp [segsOf_ne_nil]) hMl (hMlast.symm ▸ w'')
      ?_ ?_ ?_ ?_ ?_ ?_
    · obtain ⟨w₁, hw⟩ := hTalong
      exact ⟨hMlast.symm ▸ w₁, by rw [comp_cast]; exact hw⟩
    · intro ρ hρ
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hN'pos ρ hρ
      · exact hTpos ρ hρ
    · intro ρ hρ
      rcases List.mem_append.1 hρ with hρ | hρ
      · exact hN'inc ρ hρ
      · exact hTinc ρ hρ
    · rintro u (hu | hu)
      · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        rcases List.mem_append.1 hρ with hρ | hρ
        · exact hN'V (mem_segsVerts hρ hu)
        · exact hTV (Or.inl (mem_segsVerts hρ hu))
      · rw [pathVerts_cast] at hu
        exact hTV (Or.inr hu)
    · rintro u (hu | hu)
      · obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        rcases List.mem_append.1 hρ with hρ | hρ
        · exact hN'b u (mem_segsVerts hρ hu)
        · exact hTb u (Or.inl (mem_segsVerts hρ hu))
      · rw [pathVerts_cast] at hu
        exact hTb u (Or.inr hu)
    · intro H hH hcH'' hHz hMH
      have hNH : segsVerts (segsOf K' (vL₀.cons a₂) (pathOf l.x l.x_ne)) ⊆ H := fun u hu ↦ by
        obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        exact hMH (mem_segsVerts (List.mem_append_left _ hρ) hu)
      have hTH : segsVerts Tail ⊆ H := fun u hu ↦ by
        obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
        exact hMH (mem_segsVerts (List.mem_append_right _ hρ) hu)
      obtain ⟨hT1, hT2⟩ := hTsep H hH hcH'' hHz hTH
      refine ⟨?_, ?_⟩
      · rw [sepAll_iff, List.isChain_append]
        refine ⟨sepAll_iff.1 (hN'sep H hH hcH'' hNH), sepAll_iff.1 hT1, ?_⟩
        intro ρ₁ hρ₁ ρ₂ hρ₂
        obtain ⟨R, tl, hR'⟩ := segsOf_last K' (vL₀.cons a₂) (pathOf l.x l.x_ne)
        rw [hR', List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton,
          Option.mem_def, Option.some.injEq] at hρ₁
        subst hρ₁
        intro c₀ dl₀ q c' d' x₁' x₂' t s₀ e₁' t₀' e₂' s' h1 h2 hS
        simp only [ZSeg.mk.injEq] at h1
        obtain ⟨rfl, -, rfl, -, hs⟩ := h1
        have hs' := (eq_of_heq hs).symm.trans hx
        simp only [Quiver.Path.cons.injEq] at hs'
        obtain ⟨rfl, -, he⟩ := hs'
        obtain rfl := eq_of_heq he
        exact hT2 ρ₂ hρ₂ c' d' x₂' t₀' e₂' s' h2 hS
      · intro ρ₁ hρ₁ ρ₂ hρ₂
        rw [List.head?_append, Option.mem_def] at hρ₂
        obtain ⟨s₀, R, hR'⟩ := segsOf_head K' (vL₀.cons a₂) (pathOf l.x l.x_ne)
        rw [hR', List.head?_cons, Option.some_or, Option.some.injEq] at hρ₂
        exact hjunL H hHz ρ₁ hρ₁ ρ₂ (by rw [hR', ← hρ₂]; rfl)
  · -- the initial separation at `e`
    intro x₂' p₀ e₂' hp₀ hS
    subst hp₀
    have hj := join_cycle1 hcf hH' (s₀ := s''.comp p₀) (e₁ := e₂') (t₀ := ty) (e₂ := e₂)
      (by
        rintro u (hu | hu)
        · change u ∈ pathVerts (s''.comp (p₀.cons e₂')) at hu
          rw [pathVerts_comp] at hu
          rcases hu with hu | hu
          · refine hdiff (hσV (Or.inr ?_)) (not_below_of_arrow hcf γs _ hu)
            rw [pathVerts_comp]; exact Or.inr hu
          · exact hpV hu
        · rw [← hy] at hu; exact hyV hu) hint hsc
    have hx₁ : x₁.out ∈ z.hull \ {c} := hxV (by rw [hx]; exact Or.inr (mem_pathVerts_end _))
    have hx₂ : x₂.out ∈ z.hull \ {c} := hyV (by rw [hy]; exact Or.inr (mem_pathVerts_end _))
    exact link_not_sepComp hcf hL hR hCB hP (fun e he ↦ he.2) hl hH' hcH' ⟨heH, l.he.2⟩ hx hy
      hx₁ hx₂ (hS.trans _ _ _ hj)

end LargeIndecomposable.RayCat
