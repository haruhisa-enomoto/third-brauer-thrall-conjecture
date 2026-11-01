module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma53
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42

/-!
# The initial walk of Fischbacher's Lemma 5.2

Walking along `w` from a point below `e` to `b` (which is not below `e`) finds an arrow `α` of
`w` from a point below `e` to a point not below `e` (`find_end`). If `e` is not on `w`, the
segment `(path to e, α)` starts a good walk (`exists_init_walk`), and `e` and the target of `α`
are incomparable by Lemma 4.2 (`incomp_end`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- An arrow is not the value of a path of length at least two. -/
lemma not_arrow_of_long {x y : RayVert A} (α : x ⟶ y) (p : Quiver.Path x y)
    (hp : 2 ≤ p.length) (hval : pathVal p = α.1) : False := by
  rcases p with _ | ⟨p', e⟩
  · simp at hp
  · have hp' : 0 < p'.length := by simp at hp; omega
    change pathVal p' ≫ e.1 = α.1 at hval
    rcases α.2.2.2 _ _ _ hval.symm with h | h
    · exact not_isIso_pathVal p' hp' h
    · exact e.2.2.1 h

/-- Along a path to `b` from a point below `e`, with `b` not below `e`, some arrow leaves the set
of points below `e`. -/
lemma find_end {b e : A} : ∀ (n : ℕ) {x : A} (w₂ : Quiver.Path (RayVert.mk x) (RayVert.mk b)),
    w₂.length = n → Reaches x e → ¬Reaches b e →
    ∃ (c' y : A) (w₃ : Quiver.Path (RayVert.mk x) (RayVert.mk c'))
      (α : RayVert.mk c' ⟶ RayVert.mk y) (w₄ : Quiver.Path (RayVert.mk y) (RayVert.mk b)),
      w₂ = w₃.comp (α.toPath.comp w₄) ∧ Reaches c' e ∧ ¬Reaches y e
  | 0, x, w₂, h, hx, hb => by
    have hxb : RayVert.mk x = RayVert.mk b := Quiver.Path.eq_of_length_zero w₂ h
    subst hxb
    exact absurd hx hb
  | n + 1, x, w₂, h, hx, hb => by
    obtain ⟨x', β, w₂', hl, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ w₂ h
    by_cases hx' : Reaches x'.out e
    · obtain ⟨c', y, w₃, α, w₄, heq, h1, h2⟩ := find_end n (x := x'.out) w₂' hl hx' hb
      exact ⟨c', y, β.toPath.comp w₃, α, w₄, by rw [heq, Quiver.Path.comp_assoc], h1, h2⟩
    · exact ⟨x, x'.out, .nil, β, w₂', by simp, hx, hx'⟩

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
  (hint : ∀ a b : A, (interval a b).Finite)
  (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
    IsCoboundaryOn D c)
include hcf hint hsc

/-- Lemma 4.2: parallel paths have equal values. -/
lemma par {a b : A} (v w : Quiver.Path (RayVert.mk a) (RayVert.mk b)) : pathVal v = pathVal w :=
  pathVal_eq_of_parallel hcf hint hsc _ a b rfl v w

/-- A point strictly above the source of an arrow, and not below its target, is incomparable
with its target. -/
lemma incomp_end {c' e y : A} (α : RayVert.mk c' ⟶ RayVert.mk y)
    (t : Quiver.Path (RayVert.mk c') (RayVert.mk e)) (ht : 0 < t.length) (hy : ¬Reaches y e) :
    ¬Reaches e y ∧ ¬Reaches y e := by
  refine ⟨fun ⟨p⟩ ↦ ?_, hy⟩
  have hp : 0 < p.length := by
    by_contra h0
    have hey : RayVert.mk e = RayVert.mk y := Quiver.Path.eq_of_length_zero p (by omega)
    subst hey
    exact hy (Reaches.refl _)
  refine not_arrow_of_long α (t.comp p) (by rw [Quiver.Path.length_comp]; omega) ?_
  rw [par hcf hint hsc (t.comp p) α.toPath]
  change 𝟙 _ ≫ α.1 = α.1
  simp

/-- **The initial walk** of Fischbacher's proof of Lemma 5.2. -/
theorem exists_init_walk {a b : A} (v w : Quiver.Path (RayVert.mk a) (RayVert.mk b)) {d : A}
    (hd : d ∈ pathVerts v) (hdw : d ∉ pathVerts w) : ∃ z : ZWalk b, z.d₀ = d ∧ z.Good w := by
  obtain ⟨had, hdb⟩ := reaches_of_mem_pathVerts v hd
  have hb : ¬Reaches b d := fun h ↦
    hdw (eq_of_reaches_both hcf hdb h ▸ mem_pathVerts_end w)
  obtain ⟨c', y, w₃, α, w₄, hw, hc'd, hyd⟩ := find_end _ w rfl had hb
  have hc'w : c' ∈ pathVerts w := by
    rw [hw, pathVerts_comp]; exact Or.inl (mem_pathVerts_end w₃)
  obtain ⟨t⟩ := hc'd
  have ht : 0 < t.length := by
    by_contra h0
    have hcd : RayVert.mk c' = RayVert.mk d := Quiver.Path.eq_of_length_zero t (by omega)
    subst hcd
    exact hdw hc'w
  obtain ⟨v'⟩ := hdb
  let σ : ZSeg A := ⟨c', d, y, t, α.toPath⟩
  refine ⟨⟨d, [σ], ⟨rfl, trivial⟩, v', w₄⟩, rfl, ?_⟩
  refine ⟨by simp, ⟨w₃.comp α.toPath, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · change w = (w₃.comp α.toPath).comp w₄
    rw [Quiver.Path.comp_assoc]; exact hw
  · intro ρ hρ
    rw [List.mem_singleton.1 hρ]
    change 𝟙 _ ≫ α.1 ≠ 0
    rw [Category.id_comp]; exact α.2.1
  · intro ρ hρ
    rw [List.mem_singleton.1 hρ]
    exact ht
  · intro ρ hρ
    rw [List.mem_singleton.1 hρ]
    change 0 < (Quiver.Path.nil.cons α).length
    simp
  · intro L₁ L₂ c dl q c' d' x₁ x₂ t s₀ e₁ t₀ e₂ s' h
    have := congrArg List.length h
    simp at this
    omega
  · intro ρ hρ
    rw [List.mem_singleton.1 hρ]
    exact incomp_end hcf hint hsc α t ht hyd

/-- **Fischbacher's Lemma 5.2, assuming the hull-shrinking step** of §5.3–5.4: a good walk
with a zero `t`-path can be replaced by a good walk with the same first peak and a strictly smaller
hull. Then every point `d` on a path `v` parallel to `w` is joined by a chain to a point of `w`. -/
theorem lemma52_of_step {b : A}
    (hstep : ∀ {a₀ : A} (w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)) (z : ZWalk b),
      z.Good w → (∃ σ ∈ z.segs, pathVal σ.t = 0) →
      ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull)
    {a : A} (v w : Quiver.Path (RayVert.mk a) (RayVert.mk b)) {d : A} (hd : d ∈ pathVerts v) :
    ChainFromTo d (pathVerts w) := by
  by_cases hdw : d ∈ pathVerts w
  · exact ⟨[⟨d, d, 𝟙 d⟩], isChain_singleton (IsRayCategory.id_ne_zero d), by simp, rfl, hdw⟩
  obtain ⟨z₀, hz₀d, hz₀⟩ := exists_init_walk hcf hint hsc v w hd hdw
  suffices H : ∀ n (z : ZWalk b), z.Good w → z.d₀ = d → z.hull.ncard = n →
      ChainFromTo d (pathVerts w) from H _ z₀ hz₀ hz₀d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hz hzd hn
  by_cases h0 : ∃ σ ∈ z.segs, pathVal σ.t = 0
  · obtain ⟨z', hz'd, hz', hlt⟩ := hstep w z hz h0
    have hfin : z.hull.Finite := finite_hullOf hint z.verts_finite
    exact ih _ (hn ▸ Set.ncard_lt_ncard hlt hfin) z' hz' (hz'd.trans hzd) rfl
  · push_neg at h0
    exact hzd ▸ hz.chainFromTo hcf hint hsc h0

end LargeIndecomposable.RayCat
