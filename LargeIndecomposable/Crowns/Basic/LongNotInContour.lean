module

public import LargeIndecomposable.BongartzTheorem.Reduction.TheoremSix
public import LargeIndecomposable.Crowns.Section225.SameDomain
public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf
public import LargeIndecomposable.Crowns.Basic.RepresentationInfiniteShapes

/-!
# BO13a Proposition 2: a long morphism in no contour

* `RayCat.ClosedChain.toCrown`: a closed chain as a periodic crown.
* `RayCat.RaySmall.chainBounded_of`: chain-boundedness descends from the small model.
* `longMorphismNotInContour_of`: `LongMorphismNotInContour` from `TwistedMulBasisExists` and the
  representation-infinite shapes of BO13a §2.2 (`MulBasis.s225_final`).
* `longMorphismNotInContour_of_mulBasis`: the shapes discharged (`Crowns/Basic/RepresentationInfiniteShapes.lean`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

universe w v u

namespace RayCat

section ToCrown

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] {m : ℕ}

/-- The index `i mod (m + 1)`. -/
def ClosedChain.idx (m i : ℕ) : Fin (m + 1) := ⟨i % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

lemma ClosedChain.idx_succ (m i : ℕ) : idx m (i + 1) = idx m i + 1 := by
  ext
  simp [idx, Fin.val_add, Nat.add_mod]

lemma ClosedChain.idx_add (m i : ℕ) : idx m (i + (m + 1)) = idx m i := by
  ext
  simp [idx]

/-- The entries of a closed chain as a periodic sequence. -/
def ClosedChain.seq (C : ClosedChain Q m) (t : ℕ) : RayMor Q :=
  if t % 2 = 0 then ⟨_, _, C.ρ (idx m (t / 2))⟩ else ⟨_, _, C.σ (idx m (t / 2))⟩

lemma ClosedChain.seq_even (C : ClosedChain Q m) (i : ℕ) :
    C.seq (2 * i) = ⟨_, _, C.ρ (idx m i)⟩ := by
  unfold ClosedChain.seq
  split_ifs with h
  · rw [show 2 * i / 2 = i by omega]
  · omega

lemma ClosedChain.seq_odd (C : ClosedChain Q m) (i : ℕ) :
    C.seq (2 * i + 1) = ⟨_, _, C.σ (idx m i)⟩ := by
  unfold ClosedChain.seq
  split_ifs with h
  · omega
  · rw [show (2 * i + 1) / 2 = i by omega]

/-- **A closed chain is a crown.** -/
def ClosedChain.toCrown (C : ClosedChain Q m) : Crown Q where
  n := m + 1
  hn := Nat.succ_pos m
  f := C.seq
  per t := by
    unfold ClosedChain.seq
    rw [show (t + 2 * (m + 1)) % 2 = t % 2 by omega,
      show (t + 2 * (m + 1)) / 2 = t / 2 + (m + 1) by omega, ClosedChain.idx_add]
  peak i := by
    rw [C.seq_even, C.seq_odd]
    exact (peak_mk_iff _ _).2 ⟨C.peak₁ _, C.peak₂ _⟩
  valley i := by
    rw [C.seq_odd, show 2 * i + 2 = 2 * (i + 1) by ring, C.seq_even, ClosedChain.idx_succ]
    exact (valley_mk_iff _ _).2 ⟨C.valley₁ _, C.valley₂ _⟩
  ne t := by
    show (C.seq t).2.2 ≠ 0
    rcases Nat.even_or_odd' t with ⟨i, rfl | rfl⟩
    · rw [C.seq_even]
      exact C.ρ_ne _
    · rw [C.seq_odd]
      exact C.σ_ne _

end ToCrown

namespace RaySmall

variable {P : Type u} [Category.{v} P] [LocallySmall.{w} P] [HasZeroMorphisms P]

/-- A morphism of `P` as a morphism of the small model. -/
def ofRM (F : RayMor P) : RayMor (RaySmall.{u} P) := ⟨⟨F.1⟩, ⟨F.2.1⟩, sh.{w} F.2.2⟩

omit [HasZeroMorphisms P] in
lemma peak_ofRM {F G : RayMor P} (h : Peak F G) : Peak (ofRM.{w} F) (ofRM.{w} G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hY, -⟩ := id h
  change Y = Y' at hY
  subst hY
  rw [peak_mk_iff] at h
  change Peak (⟨⟨X⟩, ⟨Y⟩, sh.{w} φ⟩ : RayMor (RaySmall.{u} P)) ⟨⟨X'⟩, ⟨Y⟩, sh.{w} ψ⟩
  rw [peak_mk_iff]
  refine ⟨fun ⟨c, hc⟩ ↦ h.1 ⟨(sh.{w}).symm c, ?_⟩, fun ⟨c, hc⟩ ↦ h.2 ⟨(sh.{w}).symm c, ?_⟩⟩
  · have := congrArg (sh.{w}).symm hc
    rwa [sh_symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · have := congrArg (sh.{w}).symm hc
    rwa [sh_symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this

omit [HasZeroMorphisms P] in
lemma valley_ofRM {F G : RayMor P} (h : Valley F G) : Valley (ofRM.{w} F) (ofRM.{w} G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hX, -⟩ := id h
  change X = X' at hX
  subst hX
  rw [valley_mk_iff] at h
  change Valley (⟨⟨X⟩, ⟨Y⟩, sh.{w} φ⟩ : RayMor (RaySmall.{u} P)) ⟨⟨X⟩, ⟨Y'⟩, sh.{w} ψ⟩
  rw [valley_mk_iff]
  refine ⟨fun ⟨c, hc⟩ ↦ h.1 ⟨(sh.{w}).symm c, ?_⟩, fun ⟨c, hc⟩ ↦ h.2 ⟨(sh.{w}).symm c, ?_⟩⟩
  · have := congrArg (sh.{w}).symm hc
    rwa [sh_symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · have := congrArg (sh.{w}).symm hc
    rwa [sh_symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this

/-- **Chain-boundedness descends from the small model.** -/
lemma chainBounded_of (hCB : ChainBounded (RaySmall.{u} P)) : ChainBounded P := by
  obtain ⟨N, hN⟩ := hCB
  refine ⟨N, fun L hL ↦ ?_⟩
  have : IsChain 0 (L.map ofRM.{w}) := by
    refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hf
      exact fun h0 ↦ hL.1 F hF ((sh_eq_zero_iff (X := ⟨F.1⟩) (Y := ⟨F.2.1⟩) F.2.2).1 h0)
    · have := hL.2 j (by simpa using hj)
      simp only [List.getElem_map]
      unfold Link at this ⊢
      split_ifs at this ⊢
      · exact peak_ofRM this
      · exact valley_ofRM this
  simpa using hN _ this

end RaySmall

end RayCat

open RayCat RayQuiver

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- **BO13a Proposition 2** from BGRS multiplicative bases and the
representation-infinite shapes of BO13a §2.2. -/
theorem longMorphismNotInContour_of (hM : TwistedMulBasisExists.{u})
    (hSh : ∀ (k : Type u) [Field k] [IsAlgClosed k], MulBasis.L6Shapes k ∧ MulBasis.L8Shapes k ∧
      ¬Statement.IsRepresentationFinite (Linearization (ThinCat F93.thin) k)) :
    LongMorphismNotInContour.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  intro hCB hL'
  let _ : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  let _ : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  obtain ⟨Bm⟩ := hM k B ι S hB hd
  obtain ⟨hS6, hS8, hD93⟩ := hSh k
  by_contra hno
  have hcont : ∀ {a b : RaySmall.{0} S.toIdempotents.RayCategory} (μ : a ⟶ b), IsLong μ →
      ¬NotInContour μ := fun μ hμ hnc ↦
    hno ⟨_, _, μ, hμ.2.1, hμ.2.2.1, hμ.1, hμ.2.2.2, hnc⟩
  obtain ⟨x, y, f, hf0, hfi, hfr⟩ := hL'
  obtain ⟨a₀, b₀, μ₀, hμ₀, -⟩ := exists_isLong_above hf0 hfi hfr
  have hCB' : ¬ChainBounded (RaySmall.{0} S.toIdempotents.RayCategory) := fun h ↦
    hCB (RaySmall.chainBounded_of h)
  obtain ⟨m, ⟨Cc⟩⟩ := exists_closedChain hCB'
  exact Bm.s225_final (fun I hI ↦ hB.2 I hI) (RaySmall.leftCancel (S.leftCancel hd))
    (RaySmall.rightCancel (S.rightCancel hd)) (RaySmall.oneSidedCyclic (ray_oneSided _))
    hcont hS6 hS8 hD93 Cc.toCrown μ₀ hμ₀

/-- **BO13a Proposition 2** from BGRS multiplicative bases. -/
theorem longMorphismNotInContour_of_mulBasis (hM : TwistedMulBasisExists.{u}) : LongMorphismNotInContour.{u} :=
  longMorphismNotInContour_of hM fun k _ _ ↦
    ⟨MulBasis.l6Shapes k, MulBasis.l8Shapes k, MulBasis.f93Shape k⟩

/-- **Bongartz's Theorem 6 (data form)** from BGRS multiplicative bases and the
dichotomy on the universal cover. -/
theorem bongartzDistributive_of_mulBasis_dichotomy (hM : TwistedMulBasisExists.{u})
    (hDich : CoverDichotomy.{u}) : BongartzDistributive.{u} :=
  bongartzDistributive_of_mulBasis hM (longMorphismNotInContour_of_mulBasis hM) hDich

end LargeIndecomposable
