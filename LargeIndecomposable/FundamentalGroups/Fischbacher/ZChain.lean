module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.ZIncomp
public import LargeIndecomposable.RayCategories.Opposite.Op
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# The chain of a good walk (Fischbacher, proof of Lemma 5.2, last step)

The morphisms `t₀, s₀, t₁, s₁, …` of a zigzag walk (`segMors`) form a chain starting with a
valley once all values are nonzero, consecutive peaks are incomparable and consecutive valleys
are incomparable (`isChain_segMors`). For a good walk whose `t`-paths have nonzero values this
is a chain from the first peak to a point of `w` (`ZWalk.Good.isChain`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- The morphisms `t₀, s₀, t₁, s₁, …` of a segment list. -/
def segMors : List (ZSeg A) → List (RayMor A)
  | [] => []
  | σ :: L => ⟨σ.c, σ.dl, pathVal σ.t⟩ :: ⟨σ.c, σ.d, pathVal σ.s⟩ :: segMors L

omit [IsRayCategory A] in
lemma isChain_cons_cons {o : ℕ} {a b : RayMor A} {l : List (RayMor A)} :
    IsChain o (a :: b :: l) ↔ a.2.2 ≠ 0 ∧ Link o a b ∧ IsChain (o + 1) (b :: l) := by
  constructor
  · rintro ⟨h0, hl⟩
    refine ⟨h0 a (by simp), by simpa using hl 0 (by simp), fun f hf ↦ h0 f (by simp_all), ?_⟩
    intro j hj
    have := hl (j + 1) (by simp at hj ⊢; omega)
    simpa [show j + 1 + o = j + (o + 1) by omega] using this
  · rintro ⟨ha, hab, h0, hl⟩
    refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
    · rcases List.mem_cons.1 hf with rfl | hf
      · exact ha
      · exact h0 f hf
    · rcases j with _ | j
      · simpa using hab
      · have := hl j (by simp at hj ⊢; omega)
        simpa [show j + 1 + o = j + (o + 1) by omega] using this

omit [IsRayCategory A] in
lemma isChain_singleton {o : ℕ} {a : RayMor A} (h : a.2.2 ≠ 0) : IsChain o [a] :=
  ⟨fun f hf ↦ by rw [List.mem_singleton.1 hf]; exact h, fun j hj ↦ by simp at hj⟩

lemma reaches_of_ne_zero {x y : A} (f : x ⟶ y) (hf : f ≠ 0) : Reaches x y := ⟨pathOf f hf⟩

/-- The valley `(t, s)` of a segment with incomparable peaks. -/
lemma valley_seg (σ : ZSeg A) (ht : pathVal σ.t ≠ 0) (hs : pathVal σ.s ≠ 0)
    (h : ¬Reaches σ.dl σ.d ∧ ¬Reaches σ.d σ.dl) :
    Valley (⟨σ.c, σ.dl, pathVal σ.t⟩ : RayMor A) ⟨σ.c, σ.d, pathVal σ.s⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    simp only [eqToHom_refl, Category.id_comp] at hc
    refine h.1 (reaches_of_ne_zero c fun h0 ↦ hs ?_)
    rw [← hc]
    change pathVal σ.t ≫ c = 0
    rw [h0, comp_zero]
  · rintro ⟨c, hc⟩
    simp only [eqToHom_refl, Category.id_comp] at hc
    refine h.2 (reaches_of_ne_zero c fun h0 ↦ ht ?_)
    rw [← hc]
    change pathVal σ.s ≫ c = 0
    rw [h0, comp_zero]

/-- The peak `(s, t')` at the junction of two linked segments with incomparable valleys. -/
lemma peak_segs (σ τ : ZSeg A) (hlink : τ.dl = σ.d) (hs : pathVal σ.s ≠ 0)
    (ht : pathVal τ.t ≠ 0) (h : ¬Reaches σ.c τ.c ∧ ¬Reaches τ.c σ.c) :
    Peak (⟨σ.c, σ.d, pathVal σ.s⟩ : RayMor A) ⟨τ.c, τ.dl, pathVal τ.t⟩ := by
  obtain ⟨c₁, dl₁, d₁, t₁, s₁⟩ := σ
  obtain ⟨c₂, dl₂, d₂, t₂, s₂⟩ := τ
  change dl₂ = d₁ at hlink
  subst hlink
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    simp only [eqToHom_refl, Category.comp_id] at hc
    refine h.1 (reaches_of_ne_zero c fun h0 ↦ hs ?_)
    rw [← hc]
    change c ≫ pathVal t₂ = 0
    rw [h0, zero_comp]
  · rintro ⟨c, hc⟩
    simp only [eqToHom_refl, Category.comp_id] at hc
    refine h.2 (reaches_of_ne_zero c fun h0 ↦ ht ?_)
    rw [← hc]
    change c ≫ pathVal s₁ = 0
    rw [h0, zero_comp]

/-- **The morphisms of a walk form a chain** starting with a valley. -/
theorem isChain_segMors : ∀ {e : A} (L : List (ZSeg A)), ZLinked e L →
    (∀ σ ∈ L, pathVal σ.t ≠ 0 ∧ pathVal σ.s ≠ 0) →
    (∀ σ ∈ L, ¬Reaches σ.dl σ.d ∧ ¬Reaches σ.d σ.dl) →
    (∀ i (h : i + 1 < L.length), ¬Reaches (L[i]'(by omega)).c L[i + 1].c ∧
      ¬Reaches L[i + 1].c (L[i]'(by omega)).c) →
    IsChain 1 (segMors L)
  | _, [], _, _, _, _ => ⟨fun f hf ↦ by simp [segMors] at hf, fun j hj ↦ by simp [segMors] at hj⟩
  | _, [σ], _, hnz, hpk, _ => by
    have h := hnz σ (by simp)
    refine isChain_cons_cons.2 ⟨h.1, ?_, isChain_singleton h.2⟩
    unfold Link; rw [if_neg (by norm_num)]
    exact valley_seg σ h.1 h.2 (hpk σ (by simp))
  | _, σ :: τ :: L, ⟨_, hl⟩, hnz, hpk, hval => by
    have h := hnz σ (by simp)
    have hτ := hnz τ (by simp)
    have ih := isChain_segMors (τ :: L) hl (fun ρ hρ ↦ hnz ρ (List.mem_cons_of_mem _ hρ))
      (fun ρ hρ ↦ hpk ρ (List.mem_cons_of_mem _ hρ))
      (fun i hi ↦ hval (i + 1) (by simp at hi ⊢; omega))
    change IsChain 1 (_ :: _ :: segMors (τ :: L))
    refine isChain_cons_cons.2 ⟨h.1, ?_, ?_⟩
    · unfold Link; rw [if_neg (by norm_num)]
      exact valley_seg σ h.1 h.2 (hpk σ (by simp))
    · change IsChain 2 (_ :: _ :: _ :: segMors L)
      refine isChain_cons_cons.2 ⟨h.2, ?_, ?_⟩
      · unfold Link; rw [if_pos (by norm_num)]
        exact peak_segs σ τ hl.1 h.2 hτ.1 (by simpa using hval 0 (by simp))
      · exact (isChain_add_two 1 _).2 ih

omit [IsRayCategory A] in
lemma segMors_append (L : List (ZSeg A)) (σ : ZSeg A) :
    segMors (L ++ [σ]) = segMors L ++ [⟨σ.c, σ.dl, pathVal σ.t⟩, ⟨σ.c, σ.d, pathVal σ.s⟩] := by
  induction L with
  | nil => rfl
  | cons τ L ih => simp [segMors, ih]

/-- A chain starting with a valley, from `d` (target of its first entry) to a point of `S`
(target of its last entry). -/
def ChainFromTo (d : A) (S : Set A) : Prop :=
  ∃ l : List (RayMor A), IsChain 1 l ∧ ∃ h : l ≠ [], (l.head h).2.1 = d ∧ (l.getLast h).2.1 ∈ S

/-- **A good walk whose `t`-paths have nonzero values gives a chain** from its first peak to a
point of `w` (Fischbacher, proof of Lemma 5.2). -/
theorem ZWalk.Good.chainFromTo
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c)
    {b a₀ : A} {z : ZWalk b} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)} (hz : z.Good w)
    (ht : ∀ σ ∈ z.segs, pathVal σ.t ≠ 0) : ChainFromTo z.d₀ (pathVerts w) := by
  have hch := isChain_segMors z.segs z.linked (fun σ h ↦ ⟨ht σ h, hz.sne σ h⟩) hz.incomp
    (fun i hi ↦ hz.valley_incomp hcf hint hsc (Nat.lt_succ_self i) hi)
  obtain ⟨σ₀, L₀, h₀⟩ := List.exists_cons_of_ne_nil hz.ne_nil
  obtain ⟨L₁, σ₁, h₁⟩ := (List.eq_nil_or_concat' z.segs).resolve_left hz.ne_nil
  have hne : segMors z.segs ≠ [] := by rw [h₀]; simp [segMors]
  refine ⟨_, hch, hne, ?_, ?_⟩
  · have hl := z.linked
    rw [h₀] at hl
    have : (segMors z.segs).head hne = ⟨σ₀.c, σ₀.dl, pathVal σ₀.t⟩ := by
      simp [h₀, segMors]
    rw [this]
    exact hl.1
  · have : (segMors z.segs).getLast hne = ⟨σ₁.c, σ₁.d, pathVal σ₁.s⟩ := by
      simp [h₁, segMors_append]
    rw [this]
    obtain ⟨w₁, hw⟩ := hz.along
    have hlast : σ₁.d = ZLast z.d₀ z.segs := by rw [h₁, zLast_concat]
    change σ₁.d ∈ pathVerts w
    rw [hw, pathVerts_comp, hlast]
    exact Or.inl (mem_pathVerts_end w₁)

end LargeIndecomposable.RayCat
