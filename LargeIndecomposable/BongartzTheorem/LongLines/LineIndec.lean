module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineModule
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFitting

/-!
# The module of a line is indecomposable

For a map of the total space of the line representation satisfying the block equations of the
push-down, the diagonal blocks are multiplication by one scalar (`dsc_const`): the arrows of the
line are identities and the line is connected. A map with a zero column therefore has zero
diagonal, and the chain argument of Lemma 4.4 (`PushDown.Chain`, with the block classes of the
covering, Proposition 4.5) shows that every endomorphism of the push-down is a scalar plus a
nilpotent map. Hence the push-down is indecomposable (`isIndecomposable_lineMod`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver Classical PushDown Rep

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

namespace CLine

variable (L : CLine x₀) (k : Type u) [Field k]

/-- The inclusion of the summand at a vertex. -/
def ins (i : (pieceQuiver L.finset).V) : k →ₗ[k] (L.lineRep k).Tot :=
  LinearMap.single k (fun j ↦ (L.lineRep k).obj j) i

/-- The coordinate at a vertex. -/
def ev (i : (pieceQuiver L.finset).V) : (L.lineRep k).Tot →ₗ[k] k :=
  LinearMap.proj (R := k) (φ := fun j ↦ (L.lineRep k).obj j) i

lemma idm_eq (i : (pieceQuiver L.finset).V) : (L.lineRep k).idm i = L.ins k i ∘ₗ L.ev k i := rfl

lemma ev_ins (i : (pieceQuiver L.finset).V) : L.ev k i ∘ₗ L.ins k i = LinearMap.id :=
  LinearMap.proj_comp_single_same k (fun j ↦ (L.lineRep k).obj j) i

lemma ev_ins_apply (i : (pieceQuiver L.finset).V) (c : k) : L.ev k i (L.ins k i c) = c :=
  LinearMap.congr_fun (L.ev_ins k i) c

lemma idm_ins (i : (pieceQuiver L.finset).V) (c : k) :
    (L.lineRep k).idm i (L.ins k i c) = L.ins k i c := by
  rw [L.idm_eq k]
  change L.ins k i (L.ev k i (L.ins k i c)) = _
  rw [L.ev_ins_apply k]

lemma arrOp_ins (α : (pieceQuiver L.finset).A) (c : k) :
    (L.lineRep k).arrOp α (L.ins k ((pieceQuiver L.finset).src α) c) =
      L.ins k ((pieceQuiver L.finset).tgt α) c := by
  change L.ins k _ (((L.lineRep k).map α).hom (L.ev k _ (L.ins k _ c))) = _
  rw [L.ev_ins_apply k]
  rfl

/-- The diagonal scalar of a map of total spaces at a vertex. -/
def dsc (f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot) (i : (pieceQuiver L.finset).V) : k :=
  L.ev k i (f (L.ins k i 1))

lemma bl_diag (f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot) (i : (pieceQuiver L.finset).V) :
    bl f i i = L.dsc k f i • (L.lineRep k).idm i := by
  have h1 : (L.ev k i ∘ₗ f ∘ₗ L.ins k i : k →ₗ[k] k) = L.dsc k f i • LinearMap.id :=
    LinearMap.ext_ring (by simp [dsc])
  rw [bl, L.idm_eq k i]
  calc L.ins k i ∘ₗ L.ev k i ∘ₗ f ∘ₗ L.ins k i ∘ₗ L.ev k i
      = L.ins k i ∘ₗ (L.ev k i ∘ₗ f ∘ₗ L.ins k i) ∘ₗ L.ev k i := rfl
    _ = _ := by rw [h1, LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_smul]

variable {L k}

/-- The diagonal scalars agree along an arrow. -/
lemma dsc_arrow {f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot}
    (hf : BlockEqs (pieceProj L.finset) f) (α : (pieceQuiver L.finset).A) :
    L.dsc k f ((pieceQuiver L.finset).tgt α) = L.dsc k f ((pieceQuiver L.finset).src α) := by
  have hloc := pieceProj_locInj L.finset
  have E := hf.2 ((pieceProj L.finset).arr α) ((pieceQuiver L.finset).tgt α)
    ((pieceQuiver L.finset).src α)
  rw [outArr_eq hloc α, inArr_eq hloc α, Finset.sum_singleton, Finset.sum_singleton,
    L.bl_diag k, L.bl_diag k] at E
  have E' := congrArg (L.ev k ((pieceQuiver L.finset).tgt α))
    (LinearMap.congr_fun E (L.ins k ((pieceQuiver L.finset).src α) 1))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] at E'
  rw [L.arrOp_ins k, L.idm_ins k, L.idm_ins k, L.arrOp_ins k, L.ev_ins_apply k] at E'
  simpa using E'

variable (L) in
/-- The vertex of `D_{S_L}` at the `a`-th point. -/
def vtx (a : ℕ) (ha : a ≤ L.n) : (pieceQuiver L.finset).V := ⟨L.pt a, L.mem_finset.2 ⟨a, ha, rfl⟩⟩

lemma dsc_vtx {f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot}
    (hf : BlockEqs (pieceProj L.finset) f) :
    ∀ a (ha : a ≤ L.n), L.dsc k f (L.vtx a ha) = L.dsc k f (L.vtx 0 (Nat.zero_le _))
  | 0, _ => rfl
  | a + 1, ha => by
    rw [← dsc_vtx hf a (by omega)]
    by_cases h : L.fwd a = true
    · obtain ⟨g, hg⟩ := L.arrF a (by omega) h
      exact dsc_arrow hf ⟨L.vtx a (by omega), L.vtx (a + 1) ha, g, hg⟩
    · obtain ⟨g, hg⟩ := L.arrB a (by omega) (by simpa using h)
      exact (dsc_arrow hf ⟨L.vtx (a + 1) ha, L.vtx a (by omega), g, hg⟩).symm

/-- **The diagonal scalars are constant.** -/
lemma dsc_const {f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot}
    (hf : BlockEqs (pieceProj L.finset) f) (v w : (pieceQuiver L.finset).V) :
    L.dsc k f v = L.dsc k f w := by
  have key : ∀ v : (pieceQuiver L.finset).V,
      L.dsc k f v = L.dsc k f (L.vtx 0 (Nat.zero_le _)) := by
    intro v
    have hv := L.idx_spec (L.mem_of_V v)
    have : v = L.vtx (L.idx (L.vpt v)) hv.1 := Subtype.ext hv.2.symm
    rw [this, dsc_vtx hf]
  rw [key v, key w]

variable (L k) in
lemma diagZero : Chain.DiagZero (p := pieceProj L.finset) (fun _ : Unit ↦ L.lineRep k)
    (fun _ _ ↦ True) := by
  intro o o' h hh c _ hc i
  change (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot at h
  rw [L.bl_diag k, dsc_const hh i c]
  have h0 : L.dsc k h c = 0 := by
    unfold dsc
    have : h (L.ins k c 1) = (h ∘ₗ (L.lineRep k).idm c) (L.ins k c 1) := by
      rw [LinearMap.comp_apply, L.idm_ins k]
    rw [this, hc]
    simp
  rw [h0, zero_smul]

variable (L k) in
lemma colAdm (B : BlockClasses (pieceProj L.finset)) :
    Chain.ColAdm B (fun _ : Unit ↦ L.lineRep k) (fun _ _ ↦ True) := by
  intro o o' κ
  obtain ⟨c, hc⟩ := B.piece_zeroCol κ
  refine ⟨c, trivial, fun f _ ↦ ext_blocks fun j i ↦ ?_⟩
  have h0 : bl (restr (B.piece κ) f) j c = 0 := by rw [bl_restr, if_neg (hc j)]
  calc (L.lineRep k).idm j ∘ₗ (restr (B.piece κ) f ∘ₗ (L.lineRep k).idm c) ∘ₗ (L.lineRep k).idm i
      = bl (restr (B.piece κ) f) j c ∘ₗ (L.lineRep k).idm i := rfl
    _ = _ := by rw [h0]; simp

omit [Fintype P] [DecidableEq P] in
lemma isPdHom_sub_smul {D Q : FinQuiver} {p : FinQuiver.Hom D Q} {X : Rep k D}
    {f : X.Tot →ₗ[k] X.Tot} (hf : IsPdHom p f) (c : k) : IsPdHom p (f - c • LinearMap.id) := by
  refine ⟨fun q ↦ ?_, fun a ↦ ?_⟩
  · rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.id_comp, LinearMap.comp_id, hf.1 q]
  · rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.id_comp, LinearMap.comp_id, hf.2 a]

/-- **A map satisfying the block equations is a scalar plus a nilpotent map.** -/
theorem sub_dsc_pow_eq_zero (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    {f : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot} (hf : BlockEqs (pieceProj L.finset) f) :
    (f - L.dsc k f (L.vtx 0 (Nat.zero_le _)) • LinearMap.id) ^
      @Fintype.card (pieceQuiver L.finset).V (pieceQuiver L.finset).finV = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = L.dsc k f (L.vtx 0 (Nat.zero_le _)) := ⟨_, rfl⟩
  rw [← hc]
  have hloc := pieceProj_locInj L.finset
  have hZ := diagZero L k
  have hC := colAdm L k (coverPieceData (S := L.finset) htf).blockClasses
  have hg : BlockEqs (pieceProj L.finset) (f - c • LinearMap.id) :=
    (isPdHom_iff _ _).1 (isPdHom_sub_smul ((isPdHom_iff _ f).2 hf) c)
  have hdiag : ∀ i, bl (f - c • LinearMap.id) i i = 0 := by
    intro i
    rw [L.bl_diag k]
    have : L.dsc k (f - c • LinearMap.id) i = 0 := by
      have e1 : L.dsc k (f - c • LinearMap.id) i = L.dsc k f i - c := by
        unfold dsc
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
          L.ev_ins_apply k, smul_eq_mul, mul_one]
      rw [e1, dsc_const hf i (L.vtx 0 (Nat.zero_le _)), hc, sub_self]
    rw [this, zero_smul]
  have hmem : ∀ m, (f - c • LinearMap.id) ^ m ∈ AddSubmonoid.closure
      {h | Chain.Good (p := pieceProj L.finset) (fun _ : Unit ↦ L.lineRep k) (fun _ _ ↦ True) m
        (o := ()) (o' := ()) h} := by
    intro m
    induction m with
    | zero => exact AddSubmonoid.subset_closure (Chain.good_id hZ ())
    | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp]
      exact Chain.closure_good_comp _ hloc hZ hC ih hg hdiag
  have h := Chain.eq_zero_of_mem_closure_good (p := pieceProj L.finset)
    (Xf := fun _ : Unit ↦ L.lineRep k) (Adm := fun _ _ ↦ True) (o := ()) (o' := ())
    (hmem (@Fintype.card (pieceQuiver L.finset).V (pieceQuiver L.finset).finV))
  exact h

variable (L k)

/-- The module of the line. -/
abbrev lineMod : AR.FDMod k (Linearization P k) :=
  pdMod L.convex_finset (L.lineRep k) (L.respectsCover_lineRep k)

lemma isPdHom_of_end (e : Module.End (Linearization P k) (L.lineMod k)) :
    IsPdHom (pieceProj L.finset)
      (e.restrictScalars k : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot) := by
  refine ⟨fun q ↦ LinearMap.ext fun x ↦ ?_, fun a ↦ LinearMap.ext fun x ↦ ?_⟩
  · have hv : ∀ y : (L.lineRep k).Tot, (L.lineRep k).pdVert (pieceProj L.finset) q y =
        ((linPres P k (vertex k (quiver P) q) : Linearization P k) •
          (show L.lineMod k from y) : L.lineMod k) := by
      intro y
      rw [pdMod_smul, linAct_linPres, Rep.pdAct_vertex]
    change e ((L.lineRep k).pdVert (pieceProj L.finset) q x) =
      (L.lineRep k).pdVert (pieceProj L.finset) q (e x)
    rw [hv x, hv (e x), map_smul]
  · have hv : ∀ y : (L.lineRep k).Tot, (L.lineRep k).pdArr (pieceProj L.finset) a y =
        ((linPres P k (arrow k (quiver P) a) : Linearization P k) •
          (show L.lineMod k from y) : L.lineMod k) := by
      intro y
      rw [pdMod_smul, linAct_linPres, Rep.pdAct_arrow]
    change e ((L.lineRep k).pdArr (pieceProj L.finset) a x) =
      (L.lineRep k).pdArr (pieceProj L.finset) a (e x)
    rw [hv x, hv (e x), map_smul]

instance : Nontrivial (L.lineMod k) := by
  refine ⟨⟨L.ins k (L.vtx 0 (Nat.zero_le _)) 1, 0, fun h ↦ ?_⟩⟩
  have := congrArg (L.ev k (L.vtx 0 (Nat.zero_le _))) h
  rw [L.ev_ins_apply k] at this
  exact one_ne_zero (this.trans (map_zero (L.ev k _)))

/-- **The module of a line is indecomposable.** -/
theorem isIndecomposable_lineMod (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    Statement.IsIndecomposable (Linearization P k) (L.lineMod k) := by
  refine LargeIndecomposable.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
    fun e he ↦ ?_
  set f := (e.restrictScalars k : (L.lineRep k).Tot →ₗ[k] (L.lineRep k).Tot)
  have hf : BlockEqs (pieceProj L.finset) f := (isPdHom_iff _ f).1 (L.isPdHom_of_end k e)
  have hnil := sub_dsc_pow_eq_zero htf hf
  set c := L.dsc k f (L.vtx 0 (Nat.zero_le _))
  set N := @Fintype.card (pieceQuiver L.finset).V (pieceQuiver L.finset).finV
  have hN : N ≠ 0 := by
    haveI : Nonempty (pieceQuiver L.finset).V := ⟨L.vtx 0 (Nat.zero_le _)⟩
    exact Fintype.card_ne_zero
  set n := e - c • (1 : Module.End (Linearization P k) (L.lineMod k))
  have hpow : ∀ m (x : L.lineMod k),
      (n ^ m) x = ((f - c • LinearMap.id : Module.End k (L.lineRep k).Tot) ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih]
      erw [pow_succ, Module.End.mul_apply]
      rfl
  have hn : IsNilpotent n := ⟨N, LinearMap.ext fun x ↦ by rw [hpow]; erw [hnil]; rfl⟩
  by_cases hc : c = 0
  · left
    have : e = n := by simp [n, hc]
    obtain ⟨m, hm⟩ := hn
    rw [← he.pow_eq (show m + 1 ≠ 0 by omega), pow_succ, this, hm, zero_mul]
  · right
    have hu : IsUnit (c • (1 : Module.End (Linearization P k) (L.lineMod k))) :=
      ⟨⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul, mul_inv_cancel₀ hc, one_smul, one_mul],
        by rw [smul_mul_smul, inv_mul_cancel₀ hc, one_smul, one_mul]⟩, rfl⟩
    have he' : e = c • 1 + n := by simp [n]
    have hue : IsUnit e := he' ▸ hn.isUnit_add_left_of_commute hu
      ((Commute.one_right n).smul_right c)
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hue).1 he

end CLine

end LargeIndecomposable.RayCat
