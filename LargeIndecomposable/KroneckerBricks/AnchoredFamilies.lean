module

public import LargeIndecomposable.KroneckerBricks.Singular

/-!
# Anchored families of every infinite size

For every infinite cardinal `κ` there is an anchored family of Kronecker bricks
over an index type of cardinality `κ` whose anchor and constituents have
dimension at most `κ` (`Bricks.exists_anchored`). Gluing over subsets of the
index type then gives the rigid families of Göbel and Simson
(`KroneckerBricks/RigidFamily.lean`).

* `κ ≤ |k|`: the bricks `T_Λ` for pairwise disjoint countable sets `Λ ⊆ k`
  (`Bricks.setAnchored`).
* `κ > |k|` regular: the transport pool of a rigid map system on `κ`
  (`Bricks.transportPool`).
* `κ > |k|` singular: the marked transports of the rigid map systems on cofinal
  regular cardinals `κ_i < κ`, along disjoint countable parts of one pool, as in
  the proof of `Bricks.exists_brick_singular`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair
open _root_.Cardinal

universe u

variable {k : Type u} [Field k]

namespace Bricks

/-! ### Families of `T_Λ` over sets with infinite differences -/

section SetAnchored

variable {J : Type u} (Λ : J → Set k) (Λ0 : Set k)
  (hBB : ∀ i j, i ≠ j → (Λ i \ Λ j).Infinite) (hB0 : ∀ j, (Λ j \ Λ0).Infinite)
  (h0B : ∀ j, (Λ0 \ Λ j).Infinite) (hΛ0 : Λ0.Nonempty)

/-- The anchored family of the bricks `T_{Λ_j}` over the anchor `T_{Λ₀}`. -/
def setAnchored : Anchored k J where
  C := T Λ0
  B j := T (Λ j)
  α _ := 0
  β j := betaExt (Λ j) Λ0 (hB0 j).nonempty.some
  hC := isBrick _ hΛ0
  hB j := isBrick _ ((hB0 j).nonempty.mono Set.sdiff_subset)
  hCB j := hom_eq_zero (h0B j)
  hBC j := hom_eq_zero (hB0 j)
  hBB i j h := hom_eq_zero (hBB i j h)
  hns j := not_splits (hB0 j) (hB0 j).nonempty.some_mem
  c0 := Finsupp.single ⟨hΛ0.some, hΛ0.some_mem⟩ 1
  hc0 := Finsupp.single_ne_zero.2 one_ne_zero
  y j := Finsupp.single ⟨(hB0 j).nonempty.some, (hB0 j).nonempty.some_mem.1⟩ 1
  hy _ := Finsupp.single_ne_zero.2 one_ne_zero

end SetAnchored

/-- A countable set has a brick `T_Λ` of dimension `ℵ₀`. -/
lemma dim_T_countable {Λ : Set k} (h : #Λ = ℵ₀) : (T Λ).dim = ℵ₀ := by
  rw [dim_T, lift_id, h, add_assoc, aleph0_add_aleph0]
  exact add_eq_right le_rfl one_le_aleph0

/-- Anchored families of size `κ ≤ |k|` with constituents of dimension `ℵ₀`. -/
lemma exists_anchored_small (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hk : κ ≤ #k) :
    ∃ (J : Type u) (_ : DecidableEq J) (σ : Anchored k J), #J = κ ∧ σ.C.dim ≤ κ ∧
      (∀ j, (σ.B j).dim ≤ κ) ∧ Kron.ABInj σ.C ∧ ∀ j, Kron.ABInj (σ.B j) := by
  classical
  let J := κ.ord.ToType
  have hJ : #J = κ := mk_ord_toType κ
  have hNu : #Nu.{u} = ℵ₀ := by simp
  have hcode : #((J × Nu.{u}) ⊕ Nu.{u}) ≤ #k := by
    rw [mk_sum, mk_prod, lift_id, lift_id, hJ, hNu, lift_id]
    exact (add_le_of_le hκ (mul_le_of_le hκ le_rfl hκ) hκ).trans hk
  obtain ⟨f⟩ := (Cardinal.le_def _ _).1 hcode
  let gl : J → Nu.{u} → (J × Nu.{u}) ⊕ Nu.{u} := fun j n ↦ Sum.inl (j, n)
  let gr : Nu.{u} → (J × Nu.{u}) ⊕ Nu.{u} := Sum.inr
  let Λ : J → Set k := fun j ↦ Set.range fun n ↦ f (gl j n)
  let Λ0 : Set k := Set.range fun n ↦ f (gr n)
  have hinf : ∀ (g : Nu.{u} → (J × Nu.{u}) ⊕ Nu.{u}), Function.Injective g →
      (Set.range fun n ↦ f (g n)).Infinite :=
    fun g hg ↦ Set.infinite_range_of_injective (f.injective.comp hg)
  have hdisj : ∀ (g g' : Nu.{u} → (J × Nu.{u}) ⊕ Nu.{u}), (∀ m n, g m ≠ g' n) →
      (Set.range fun n ↦ f (g n)) \ (Set.range fun n ↦ f (g' n)) = Set.range fun n ↦ f (g n) := by
    intro g g' h
    refine Disjoint.sdiff_eq_left (Set.disjoint_left.2 ?_)
    rintro _ ⟨m, rfl⟩ ⟨n, hn⟩
    exact h m n (f.injective hn.symm)
  have hinl : ∀ j : J, Function.Injective (gl j) := fun j m n h ↦ by
    simpa [gl] using h
  have hinr : Function.Injective gr := Sum.inr_injective
  have hBB : ∀ i j, i ≠ j → (Λ i \ Λ j).Infinite := fun i j h ↦ by
    rw [hdisj _ _ fun m n e ↦ h (by simpa [gl] using congrArg (Sum.elim Prod.fst fun _ ↦ i) e)]
    exact hinf _ (hinl i)
  have hB0 : ∀ j, (Λ j \ Λ0).Infinite := fun j ↦ by
    rw [hdisj _ _ fun m n e ↦ by simp [gl, gr] at e]
    exact hinf _ (hinl j)
  have h0B : ∀ j, (Λ0 \ Λ j).Infinite := fun j ↦ by
    rw [hdisj _ _ fun m n e ↦ by simp [gl, gr] at e]
    exact hinf _ hinr
  have hcount : ∀ (g : Nu.{u} → (J × Nu.{u}) ⊕ Nu.{u}), Function.Injective g →
      #(Set.range fun n ↦ f (g n)) = ℵ₀ := fun g hg ↦ by
    rw [mk_range_eq (fun n ↦ f (g n)) (f.injective.comp hg), hNu]
  refine ⟨J, inferInstance, setAnchored Λ Λ0 hBB hB0 h0B ⟨_, ⟨0⟩, rfl⟩, hJ, ?_, fun j ↦ ?_,
    abInj_T _, fun j ↦ abInj_T _⟩
  · exact (dim_T_countable (hcount _ hinr)).le.trans hκ
  · exact (dim_T_countable (hcount _ (hinl j))).le.trans hκ

/-! ### Marked rigid structures -/

/-- For a regular uncountable `κ`, `κ` rigid `R_ω`-structures on one space of
dimension `κ`, all equal to the whole space at index `1`, such that only `0`
maps one to another. -/
lemma exists_marked_structures [Infinite k] (κ : Cardinal.{u}) (hreg : κ.IsRegular)
    (hκ : ℵ₀ < κ) :
    ∃ (X : Type u) (G : ModuleCat.{u} k) (Gs : X → Nu.{u} → Submodule k G), #X = κ ∧
      Module.rank k G = κ ∧ (∀ x, Gs x ⟨1⟩ = ⊤) ∧ (∀ x, IsRigidR (Gs x)) ∧
      (∀ x y, x ≠ y → ∀ Ψ : G →ₗ[k] G, (∀ j, ∀ g ∈ Gs x j, Ψ g ∈ Gs y j) → Ψ = 0) := by
  obtain ⟨_, _, _, hα, hmk⟩ := regular_order κ hreg hκ
  haveI := Rigid.infinite_of hα
  refine ⟨Rigid.Dec κ.ord.ToType, ModuleCat.of k ((Rigid.Dec κ.ord.ToType →₀ k) ×
      (Rigid.Dec κ.ord.ToType →₀ k)), marks k (Rigid.regSys hα), by rw [mk_dec_eq, hmk], ?_,
    fun x ↦ marks_one _ x, isRigidR_marks _ (Rigid.isRigidSys_regSys k hα),
    fun x y h ↦ marks_orth _ (Rigid.isRigidSys_regSys k hα) h⟩
  change Module.rank k ((Rigid.Dec κ.ord.ToType →₀ k) × (Rigid.Dec κ.ord.ToType →₀ k)) = κ
  rw [rank_prod', rank_finsupp_self', mk_dec_eq,
    add_eq_self (Cardinal.infinite_iff.1 inferInstance), hmk]

/-! ### Singular sizes -/

variable [Infinite k]

/-- Anchored families of every singular size `κ > |k|` with constituents of
dimension at most `κ`. -/
lemma exists_anchored_singular (κ : Cardinal.{u}) (hk : #k < κ) (hreg : ¬κ.IsRegular) :
    ∃ (J : Type u) (_ : DecidableEq J) (σ : Anchored k J), #J = κ ∧ σ.C.dim ≤ κ ∧
      (∀ j, (σ.B j).dim ≤ κ) ∧ Kron.ABInj σ.C ∧ ∀ j, Kron.ABInj (σ.B j) := by
  classical
  have hk0 : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  have hκ0 : ℵ₀ ≤ κ := hk0.trans hk.le
  have hμκ : κ.ord.cof < κ :=
    lt_of_le_of_ne (Ordinal.cof_ord_le κ) fun h ↦ hreg ⟨hκ0, h.ge⟩
  have hν0 : ℵ₀ ≤ max κ.ord.cof #k := le_max_of_le_right hk0
  set lam := Order.succ (max κ.ord.cof #k) with hlam
  have hlreg : lam.IsRegular := isRegular_succ hν0
  have hlk : #k < lam := (le_max_right _ _).trans_lt (Order.lt_succ _)
  have hlκ : lam < κ := lt_of_le_of_ne (Order.succ_le_of_lt (max_lt hμκ hk))
    fun h ↦ hreg (h ▸ hlreg)
  obtain ⟨J, _, σ, hJ, hCd, hBd, hiC, hiB, hoC, hoB, α0, β0, hns0⟩ := exists_pool lam hlreg hlk
  obtain ⟨ι, f, hf, hι⟩ := Ordinal.exists_lsub_cof κ.ord
  have hιNu : #(ι × Nu.{u}) ≤ #J := by
    rw [mk_prod, lift_id, lift_id, hι, hJ]
    have : #Nu.{u} = ℵ₀ := by simp
    rw [this]
    refine (mul_le_max_of_aleph0_le_right le_rfl).trans ?_
    refine (max_le (le_max_left _ _) (hk0.trans (le_max_right _ _))).trans (Order.le_succ _)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hιNu
  let σ' := σ.comap e
  -- cofinal regular cardinals
  let κi : ι → Cardinal.{u} := fun i ↦ Order.succ (max (f i).card lam)
  have hκi_reg : ∀ i, (κi i).IsRegular := fun i ↦
    isRegular_succ (le_max_of_le_right hlreg.aleph0_le)
  have hκi_lam : ∀ i, lam < κi i := fun i ↦ (le_max_right _ _).trans_lt (Order.lt_succ _)
  have hκi_le : ∀ i, κi i ≤ κ := fun i ↦
    Order.succ_le_of_lt (max_lt (lt_ord.1 (hf ▸ Ordinal.lt_lsub f i)) hlκ)
  have hsum : Cardinal.sum κi = κ := by
    refine le_antisymm ?_ ?_
    · refine (sum_le_sum _ (fun _ ↦ κ) hκi_le).trans ?_
      rw [sum_const', hι]
      exact (mul_le_mul_left (Ordinal.cof_ord_le κ) κ).trans (mul_eq_self hκ0).le
    · by_contra h
      rw [not_le] at h
      obtain ⟨i, hi⟩ := Ordinal.lt_lsub_iff.1 (hf.symm ▸ ord_lt_ord.2 h)
      exact (((ord_le.1 hi).trans_lt ((le_max_left _ _).trans_lt (Order.lt_succ _))).trans_le
        (le_sum κi i)).false
  -- the marked structures
  choose X G Gs hX hrank h1 hrig horth using fun i ↦
    exists_marked_structures (k := k) (κi i) (hκi_reg i) (hlreg.aleph0_le.trans_lt (hκi_lam i))
  let Gsi : ∀ i, X i → ι × Nu.{u} → Submodule k (G i) := fun i x p ↦
    if p.1 = i then Gs i x p.2 else ⊥
  have hGsi1 : ∀ i x, Gsi i x (i, ⟨1⟩) = ⊤ := fun i x ↦ by simp [Gsi, h1]
  have hrigi : ∀ i x, IsRigidR (Gsi i x) := fun i x ψ hψ ↦ hrig i x ψ fun n g hg ↦ by
    have := hψ (i, n) g (by simpa [Gsi] using hg)
    simpa [Gsi] using this
  have hnt : ∀ i, Nontrivial (G i) := fun i ↦ rank_pos_iff_nontrivial.1
    (by rw [hrank]; exact aleph0_pos.trans_le (hlreg.aleph0_le.trans (hκi_lam i).le))
  let H : (Σ i, X i) → Kron k := fun p ↦ σ'.transport (Gsi p.1 p.2)
  have hHb : ∀ p, IsBrickKron (H p) := fun p ↦
    haveI := hnt p.1
    σ'.isBrick_transport (Gsi p.1 p.2) (hGsi1 p.1 p.2) (hrigi p.1 p.2)
  have hSV : Module.rank k (σ'.SV Set.univ) ≤ lam :=
    σ'.rank_SV_le hlreg.aleph0_le (hιNu.trans hJ.le) ((rank_V_le_dim _).trans hCd)
      fun j ↦ (rank_V_le_dim _).trans (hBd (e j))
  have hSW : Module.rank k (σ'.SW Set.univ) ≤ lam :=
    σ'.rank_SW_le hlreg.aleph0_le (hιNu.trans hJ.le) ((rank_W_le_dim _).trans hCd)
      fun j ↦ (rank_W_le_dim _).trans (hBd (e j))
  have hHd : ∀ p, (H p).dim = κi p.1 := fun p ↦ by
    rw [σ'.dim_transport (Gsi p.1 p.2) (hGsi1 p.1 p.2) (by rw [hrank]; exact (hlreg.aleph0_le.trans
      (hκi_lam p.1).le)) (by rw [hrank]; exact hSV.trans (hκi_lam p.1).le)
      (by rw [hrank]; exact hSW.trans (hκi_lam p.1).le), hrank]
  have hHH : ∀ p q, p ≠ q → ∀ g : H p ⟶ H q, g = 0 := by
    rintro ⟨i, x⟩ ⟨i', x'⟩ hpq
    refine σ'.transport_hom_eq_zero (Gsi i x) (Gsi i' x') (hGsi1 i x) fun Ψ hΨ ↦ ?_
    by_cases hii : i = i'
    · subst hii
      have hxx : x ≠ x' := fun h ↦ hpq (by rw [h])
      refine horth i x x' hxx Ψ fun n g hg ↦ ?_
      have := hΨ (i, n) g (by simpa [Gsi] using hg)
      simpa [Gsi] using this
    · refine LinearMap.ext fun g ↦ ?_
      have := hΨ (i, ⟨1⟩) g (by rw [hGsi1]; trivial)
      simpa [Gsi, hii] using this
  have hHo : ∀ p, Orth (T (LamX (nE (k := k) 1))) (H p) := fun p ↦
    σ'.orth_transport (Gsi p.1 p.2) hoC fun j ↦ hoB (e j)
  have hcls : ∀ p, ∃ αc βc : (H p).V →ₗ[k] (T (LamX (nE (k := k) 1))).W,
      ¬Splits (T (LamX (nE 1))) (H p) αc βc := fun p ↦ by
    haveI := hnt p.1
    obtain ⟨g0, hg0⟩ := exists_ne (0 : G p.1)
    exact σ'.exists_not_splits_transport (Gsi p.1 p.2) hns0 (j0 := (p.1, ⟨1⟩))
      (by rw [hGsi1]; trivial) hg0
  choose αc βc hαβ using hcls
  have hy : ∀ p, ∃ y : (H p).V, y ≠ 0 := fun p ↦ by
    haveI := hnt p.1
    obtain ⟨g0, hg0⟩ := exists_ne (0 : G p.1)
    refine ⟨⟨g0 ⊗ₜ σ'.iV (p.1, ⟨1⟩) (σ'.c0, 0),
      σ'.genV_mem _ (n := (p.1, ⟨1⟩)) (by rw [hGsi1]; trivial) _⟩, fun h ↦ hg0 ?_⟩
    have := congrArg Subtype.val h
    change g0 ⊗ₜ σ'.iV (p.1, ⟨1⟩) (σ'.c0, 0) = 0 at this
    rw [Anchored.iV_anchor] at this
    exact eq_zero_of_tmul_right' σ'.anchor_ne_zero this
  choose y hy using hy
  have hC0 := lamX_nonempty (nE (k := k) 1)
  refine ⟨Σ i, X i, inferInstance,
    { C := T (LamX (nE 1))
      B := H
      α := αc
      β := βc
      hC := isBrick _ hC0
      hB := hHb
      hCB := fun p ↦ (hHo p).1
      hBC := fun p ↦ (hHo p).2
      hBB := hHH
      hns := hαβ
      c0 := Finsupp.single ⟨_, hC0.some_mem⟩ 1
      hc0 := Finsupp.single_ne_zero.2 one_ne_zero
      y := y
      hy := hy }, ?_, (dim_T_le _).trans hk.le, fun p ↦ (hHd p).le.trans (hκi_le p.1),
    abInj_T _, fun p ↦ σ'.abInj_transport _ hiC fun j ↦ hiB (e j)⟩
  rw [mk_sigma]
  simp only [hX]
  exact hsum

/-- Anchored families of every infinite size `κ` with anchor and constituents
of dimension at most `κ`. -/
theorem exists_anchored (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    ∃ (J : Type u) (_ : DecidableEq J) (σ : Anchored k J), #J = κ ∧ σ.C.dim ≤ κ ∧
      (∀ j, (σ.B j).dim ≤ κ) ∧ Kron.ABInj σ.C ∧ ∀ j, Kron.ABInj (σ.B j) := by
  rcases le_or_gt κ #k with hk | hk
  · exact exists_anchored_small κ hκ hk
  by_cases hreg : κ.IsRegular
  · obtain ⟨J, hd, σ, hJ, hC, hB, hiC, hiB, -⟩ := exists_pool κ hreg hk
    exact ⟨J, hd, σ, hJ, hC, hB, hiC, hiB⟩
  · exact exists_anchored_singular κ hk hreg

end Bricks

end LargeIndecomposable
