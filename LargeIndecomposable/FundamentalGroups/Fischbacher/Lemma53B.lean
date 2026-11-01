module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.BChain
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Sep43

/-!
# Fischbacher §5.3: the new segments from a chain of arrows

A chain of links `ε₀ → ε₁ → ⋯ → ε_m` out of `c`, with bounds `ε_{i-1} x_i = ε_i y_i` at `e_i`,
together with a path `v : f₀ ⇝ dl` and a path `w : f_m ⇝ d`, gives the segment list
`(v, w₁), (v₁, w₂), …, (v_m, w)` from `dl` to `d` with peaks `e_i` (`segsOf`), where `w_i` and
`v_i` are paths with values `x_i` and `y_i`. This is the replacement of `t⁻¹ s` in §5.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]
variable {c : A} {P : A → Prop}

/-- The segments of a chain between a left path to `dl` and a right path to `d`. -/
def segsOf : ∀ {α β : OutA c}, BChain c P α β → ∀ {dl d : A},
    Quiver.Path (RayVert.mk α.1) (RayVert.mk dl) → Quiver.Path (RayVert.mk β.1) (RayVert.mk d) →
    List (ZSeg A)
  | α, _, .nil _, dl, d, v, w => [⟨α.1, dl, d, v, w⟩]
  | α, _, .cons s W, dl, _, v, w =>
    ⟨α.1, dl, s.e, v, pathOf s.x s.x_ne⟩ :: segsOf W (pathOf s.y s.y_ne) w

lemma segsOf_linked : ∀ {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)),
    ZLinked dl (segsOf W v w) ∧ ZLast dl (segsOf W v w) = d
  | _, _, .nil _, _, _, _, _ => ⟨⟨rfl, trivial⟩, rfl⟩
  | _, _, .cons s W, _, _, _, w => by
    obtain ⟨h1, h2⟩ := segsOf_linked W (pathOf s.y s.y_ne) w
    exact ⟨⟨rfl, h1⟩, h2⟩

lemma segsOf_ne_nil {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)) : segsOf W v w ≠ [] := by
  cases W <;> simp [segsOf]

/-- The paths of a minimal link are nontrivial. -/
lemma IsMinC.pos {α β : OutA c} {s : BLink c P α β}
    (h : IsMinC (BChain.cons s (BChain.nil β))) :
    0 < (pathOf s.x s.x_ne).length ∧ 0 < (pathOf s.y s.y_ne).length := by
  have hne := h.ne
  obtain ⟨a₁, α'⟩ := α
  obtain ⟨b₁, β'⟩ := β
  obtain ⟨e, x, y, heq, hne0, he⟩ := s
  change α'.1 ≫ x = β'.1 ≫ y at heq
  constructor
  · by_contra h0
    have h0' := Nat.eq_zero_of_not_pos h0
    have hae : RayVert.mk a₁ = RayVert.mk e := Quiver.Path.eq_of_length_zero _ h0'
    change a₁ = e at hae
    subst hae
    have hx : x = 𝟙 _ := by
      have := pathVal_pathOf x (fun h ↦ hne0 (by rw [h, comp_zero]))
      rw [Quiver.Path.eq_nil_of_length_zero _ h0'] at this
      exact this.symm
    subst hx
    rw [Category.comp_id] at heq
    rcases α'.2.2.2 _ _ _ heq with h1 | h1
    · exact β'.2.2.1 h1
    · obtain ⟨hba, hy⟩ := eq_eqToHom_of_isIso y
      subst hba
      simp only [eqToHom_refl] at hy
      subst hy
      rw [Category.comp_id] at heq
      exact hne (by rw [show α' = β' from Subtype.ext heq])
  · by_contra h0
    have h0' := Nat.eq_zero_of_not_pos h0
    have hbe : RayVert.mk b₁ = RayVert.mk e := Quiver.Path.eq_of_length_zero _ h0'
    change b₁ = e at hbe
    subst hbe
    have hy : y = 𝟙 _ := by
      have := pathVal_pathOf y (fun h ↦ hne0 (by rw [heq, h, comp_zero]))
      rw [Quiver.Path.eq_nil_of_length_zero _ h0'] at this
      exact this.symm
    subst hy
    rw [Category.comp_id] at heq
    rcases β'.2.2.2 _ _ _ heq.symm with h1 | h1
    · exact α'.2.2.1 h1
    · obtain ⟨hab, hx⟩ := eq_eqToHom_of_isIso x
      subst hab
      simp only [eqToHom_refl] at hx
      subst hx
      rw [Category.comp_id] at heq
      exact hne (by rw [show α' = β' from Subtype.ext heq])

/-- The segments of a minimal chain have nontrivial pieces and nonzero `s`-values. -/
lemma segsOf_pos : ∀ {α β : OutA c} {W : BChain c P α β}, IsMinC W → ∀ {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)), 0 < v.length → 0 < w.length →
    pathVal w ≠ 0 → ∀ ρ ∈ segsOf W v w, 0 < ρ.t.length ∧ 0 < ρ.s.length ∧ pathVal ρ.s ≠ 0
  | _, _, .nil _, _, _, _, _, _, hv, hw, hw0, ρ, hρ => by
    rw [segsOf, List.mem_singleton] at hρ
    subst hρ
    exact ⟨hv, hw, hw0⟩
  | _, _, .cons s W, h, _, _, _, w, hv, hw, hw0, ρ, hρ => by
    rcases List.mem_cons.1 hρ with rfl | hρ
    · refine ⟨hv, h.head.pos.1, ?_⟩
      change pathVal (pathOf s.x s.x_ne) ≠ 0
      rw [pathVal_pathOf]; exact s.x_ne
    · exact segsOf_pos h.tail _ w h.head.pos.2 hw hw0 ρ hρ

/-- The vertices of the segments of a chain lie in a convex set containing `c`, the bounds and
the end paths. -/
lemma segsOf_verts {H : Set A} (hH : ConvexR H) (hc : c ∈ H) (hP : ∀ e, P e → e ∈ H) :
    ∀ {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)), pathVerts v ⊆ H → pathVerts w ⊆ H →
    segsVerts (segsOf W v w) ⊆ H
  | _, _, .nil _, _, _, v, w, hv, hw => by
    intro u hu
    obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rw [segsOf, List.mem_singleton] at hρ
    subst hρ
    rcases hu with hu | hu
    · exact hv hu
    · exact hw hu
  | α, _, .cons (β := β) s W, _, _, v, w, hv, hw => by
    have hx : pathVerts (pathOf s.x s.x_ne) ⊆ H := by
      intro u hu
      obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts _ hu
      exact hH _ hc _ (hP _ s.he) u (Reaches.trans ⟨α.2.toPath⟩ h1) h2
    have hy : pathVerts (pathOf s.y s.y_ne) ⊆ H := by
      intro u hu
      obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts _ hu
      exact hH _ hc _ (hP _ s.he) u (Reaches.trans ⟨β.2.toPath⟩ h1) h2
    intro u hu
    obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rcases List.mem_cons.1 hρ with rfl | hρ
    · rcases hu with hu | hu
      · exact hv hu
      · exact hx hu
    · exact segsOf_verts hH hc hP W _ w hy hw (Set.mem_iUnion₂.2 ⟨ρ, hρ, hu⟩)

/-- Vertices of the segments of a chain below `c` lie on the end paths. -/
lemma segsOf_below (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0) :
    ∀ {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)) {u : A},
    u ∈ segsVerts (segsOf W v w) → Reaches u c → u ∈ pathVerts v ∪ pathVerts w
  | _, _, .nil _, _, _, v, w, u, hu, _ => by
    obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rw [segsOf, List.mem_singleton] at hρ
    subst hρ
    exact hu
  | α, _, .cons (β := β) s W, _, _, v, w, u, hu, hr => by
    have hno : ∀ (γ : OutA c) {e : A} (p : Quiver.Path (RayVert.mk γ.1) (RayVert.mk e)),
        u ∈ pathVerts p → False := by
      intro γ e p hp
      obtain ⟨q⟩ := (reaches_of_mem_pathVerts p hp).1
      exact no_pos_cycle hcf (γ.2.toPath.comp q) (by simp [Quiver.Path.length_comp]) hr
    obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
    rcases List.mem_cons.1 hρ with rfl | hρ
    · rcases hu with hu | hu
      · exact Or.inl hu
      · exact (hno α _ hu).elim
    · rcases segsOf_below hcf W _ w (Set.mem_iUnion₂.2 ⟨ρ, hρ, hu⟩) hr with hu | hu
      · exact (hno β _ hu).elim
      · exact Or.inr hu

namespace BChain

/-- The first bound, or `d` for the empty chain. -/
def firstE {α β : OutA c} (W : BChain c P α β) (d : A) : A :=
  match W with
  | nil _ => d
  | cons s _ => s.e

/-- The last bound, or `e₀` for the empty chain. -/
def lastE : ∀ {α β : OutA c}, BChain c P α β → A → A
  | _, _, nil _, e₀ => e₀
  | _, _, cons s W, _ => lastE W s.e

lemma lastE_snoc : ∀ {α α' β : OutA c} (W : BChain c P α α') (l : BLink c P α' β) (e₀ : A),
    (W.append (cons l (nil β))).lastE e₀ = l.e
  | _, _, _, nil _, _, _ => rfl
  | _, _, _, cons l' W, l, _ => lastE_snoc W l l'.e

lemma lastE_of_bounds : ∀ {α β : OutA c} (W : BChain c P α β), W.bounds = [] → ∀ e₀,
    W.lastE e₀ = e₀
  | _, _, nil _, _, _ => rfl
  | _, _, cons _ _, h, _ => by simp [bounds] at h

lemma firstE_of_bounds {α β : OutA c} (W : BChain c P α β) (h : W.bounds = []) (d : A) :
    W.firstE d = d := by
  cases W with
  | nil => rfl
  | cons _ _ => simp [bounds] at h

lemma firstE_mem {α β : OutA c} (W : BChain c P α β) (h : W.bounds ≠ []) (d : A) :
    W.firstE d ∈ W.bounds := by
  cases W with
  | nil => simp [bounds] at h
  | cons l _ => simp [firstE, bounds]

end BChain

/-- Two points are incomparable. -/
def Incomp (x y : A) : Prop := ¬Reaches x y ∧ ¬Reaches y x

section Par

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
  (hint : ∀ a b : A, (interval a b).Finite)
  (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
    IsCoboundaryOn D c)
include hcf hint hsc

/-- Consecutive bounds of a minimal chain are incomparable. -/
lemma bound_incomp {α β γ : OutA c} {s : BLink c P α β} {s' : BLink c P β γ}
    (h : IsMinC (BChain.cons s (BChain.cons s' (BChain.nil γ)))) : Incomp s.e s'.e := by
  refine ⟨fun ⟨q⟩ ↦ h.valley.1 ⟨pathVal q, ?_⟩, fun ⟨q⟩ ↦ h.valley.2 ⟨pathVal q, ?_⟩⟩
  · have := par hcf hint hsc ((pathOf s.y s.y_ne).comp q) (pathOf s'.x s'.x_ne)
    rwa [pathVal_comp, pathVal_pathOf, pathVal_pathOf] at this
  · have := par hcf hint hsc ((pathOf s'.x s'.x_ne).comp q) (pathOf s.y s.y_ne)
    rwa [pathVal_comp, pathVal_pathOf, pathVal_pathOf] at this

/-- Consecutive peaks of the segments of a minimal chain are incomparable, given the ends. -/
lemma segsOf_incomp : ∀ {α β : OutA c} {W : BChain c P α β}, IsMinC W → ∀ {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)),
    Incomp dl (W.firstE d) → Incomp (W.lastE dl) d → ∀ ρ ∈ segsOf W v w, Incomp ρ.dl ρ.d
  | _, _, .nil _, _, _, _, v, w, h₁, _, ρ, hρ => by
    rw [segsOf, List.mem_singleton] at hρ
    subst hρ
    exact h₁
  | _, _, .cons s W, h, _, _, v, w, h₁, h₂, ρ, hρ => by
    rcases List.mem_cons.1 hρ with rfl | hρ
    · exact h₁
    · refine segsOf_incomp h.tail _ w ?_ h₂ ρ hρ
      cases W with
      | nil => exact h₂
      | cons s' W' => exact bound_incomp hcf hint hsc (IsMinC.left (W' := W') h)

end Par

lemma segsOf_head : ∀ {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)),
    ∃ (s₁ : Quiver.Path (RayVert.mk α.1) (RayVert.mk (W.firstE d))) (R : List (ZSeg A)),
      segsOf W v w = ⟨α.1, dl, W.firstE d, v, s₁⟩ :: R
  | _, _, .nil _, _, _, _, w => ⟨w, [], rfl⟩
  | _, _, .cons s W, _, _, _, w => ⟨_, _, rfl⟩

lemma segsOf_last : ∀ {α β : OutA c} (W : BChain c P α β) {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)),
    ∃ (R : List (ZSeg A)) (tl : Quiver.Path (RayVert.mk β.1) (RayVert.mk (W.lastE dl))),
      segsOf W v w = R ++ [⟨β.1, W.lastE dl, d, tl, w⟩]
  | _, _, .nil _, _, _, v, _ => ⟨[], v, rfl⟩
  | _, _, .cons s W, _, _, _, w => by
    obtain ⟨R, tl, h⟩ := segsOf_last W (pathOf s.y s.y_ne) w
    exact ⟨_ :: R, tl, by rw [segsOf, h]; rfl⟩

/-- **The inner peaks of the segments of a minimal chain are separating** in any convex set
containing the segments but not `c` (Lemma 4.3). -/
theorem segsOf_sep (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hP : ∀ e b' : A, P e → Reaches c b' → Reaches b' e → b' ≠ c → P b')
    (hPc : ∀ e, P e → e ≠ c) {H : Set A} (hH : ConvexR H) (hcH : c ∉ H) :
    ∀ {α β : OutA c} {W : BChain c P α β}, IsMinC W → ∀ {dl d : A}
    (v : Quiver.Path (RayVert.mk α.1) (RayVert.mk dl))
    (w : Quiver.Path (RayVert.mk β.1) (RayVert.mk d)),
    segsVerts (segsOf W v w) ⊆ H → SepAll H (segsOf W v w)
  | _, _, .nil _, _, _, _, v, w, _ => by
    intro L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    have := congrArg List.length h
    simp [segsOf] at this
    omega
  | α, _, .cons (β := β) s W, h, dl, d, v, w, hV => by
    intro L₁ L₂ c' dl' q c'' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' hsplit
    rcases L₁ with _ | ⟨ρ₀, L₁⟩
    · obtain ⟨s₁, R, hR'⟩ := segsOf_head W (pathOf s.y s.y_ne) w
      change ZSeg.mk α.1 dl s.e v (pathOf s.x s.x_ne) :: segsOf W (pathOf s.y s.y_ne) w = _
        at hsplit
      rw [hR'] at hsplit
      simp only [List.nil_append, List.cons.injEq, ZSeg.mk.injEq] at hsplit
      obtain ⟨⟨rfl, rfl, rfl, -, hx⟩, ⟨rfl, -, rfl, hy, -⟩, -⟩ := hsplit
      have hx' := eq_of_heq hx
      have hy' := eq_of_heq hy
      have hρ₀ : (ZSeg.mk α.1 dl s.e v (pathOf s.x s.x_ne)) ∈ segsOf (BChain.cons s W) v w :=
        List.mem_cons_self
      have hsV : ∀ u ∈ pathVerts (pathOf s.x s.x_ne), u ∈ H := fun u hu ↦
        hV (mem_segsVerts hρ₀ (Or.inr hu))
      have hρ₁ : (⟨β.1, s.e, W.firstE d, pathOf s.y s.y_ne, s₁⟩ : ZSeg A) ∈
          segsOf (BChain.cons s W) v w := by
        change _ ∈ _ :: segsOf W (pathOf s.y s.y_ne) w
        rw [hR']; simp
      have htV : ∀ u ∈ pathVerts (pathOf s.y s.y_ne), u ∈ H := fun u hu ↦
        hV (mem_segsVerts hρ₁ (Or.inl hu))
      have heH : s.e ∈ H := hsV _ (mem_pathVerts_end _)
      let C : EssCfg (α.2.1 ≫ s.x) :=
        { x := x₁.out, y := x₂.out, α := e₁, β := e₂,
          v := α.2.toPath.comp s₀, w := β.2.toPath.comp t₀,
          hv := by
            change pathVal (α.2.toPath.comp (s₀.cons e₁)) = _
            rw [← hx', pathVal_toPath_comp, pathVal_pathOf]
          hw := by
            change pathVal (β.2.toPath.comp (t₀.cons e₂)) = _
            rw [← hy', pathVal_toPath_comp, pathVal_pathOf, s.eq]
          hess := by
            change ¬Interlaced (α.2.toPath.comp (s₀.cons e₁)) (β.2.toPath.comp (t₀.cons e₂))
            rw [← hx', ← hy']
            exact h.head.essential hcf (fun b' h1 h2 h3 ↦ hP _ b' s.he h1 h2 h3)
              (hPc _ s.he) }
      have hD : ∀ g : Σ y : A, y ⟶ s.e, g.1 ∈ H → g.2 ≠ 0 → ¬Thr (α.2.1 ≫ s.x) g.2 := by
        rintro g hg hg0 ⟨p, hp⟩
        have hp0 : p ≠ 0 := fun h0 ↦ hg0 (by rw [hp, h0, zero_comp])
        exact hcH (hH _ hg _ heH c (reaches_of_ne_zero p hp0)
          (reaches_of_ne_zero _ s.ne))
      have hloop : ∀ (z : RayVert A) (e' : z ⟶ RayVert.mk s.e), z.out ≠ s.e := by
        intro z e' hz
        have hz' : z = RayVert.mk s.e := hz
        subst hz'
        have := hcf _ e'.toPath
        simp at this
      have hx₁ : x₁.out ∈ H := hsV _ (by rw [hx']; exact Or.inr (mem_pathVerts_end s₀))
      have hx₂ : x₂.out ∈ H := htV _ (by rw [hy']; exact Or.inr (mem_pathVerts_end t₀))
      exact not_sepComp_of_essCfg hL hR hCB s.ne C hD hx₁ hx₂ (hloop _ e₁) (hloop _ e₂)
    · change ZSeg.mk α.1 dl s.e v (pathOf s.x s.x_ne) :: segsOf W (pathOf s.y s.y_ne) w = _
        at hsplit
      simp only [List.cons_append, List.cons.injEq] at hsplit
      refine segsOf_sep hL hR hCB hcf hP hPc hH hcH h.tail _ w ?_ L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ _
        hsplit.2
      intro u hu
      obtain ⟨ρ, hρ, hu⟩ := Set.mem_iUnion₂.1 hu
      exact hV (mem_segsVerts (List.mem_cons_of_mem _ hρ) hu)

end LargeIndecomposable.RayCat
