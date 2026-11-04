module

public import LargeIndecomposable.KroneckerBricks.AnchoredFamilies
public import LargeIndecomposable.BongartzTheorem.Reduction.Corollaries

/-!
# Göbel–Simson rigid families (Theorem 5.6)

For an infinite field `k` and an infinite type `X` of cardinality `κ` there are
Kronecker modules `T_β = (V_β, W_β; a_β, b_β)`, `β ⊆ X`, with
`dim V_β = dim W_β = κ`, `a_β, b_β` injective and `a_β(V_β) + b_β(V_β) = W_β`,
such that `Hom(T_β, T_γ) ≅ k` for `β ⊆ γ`, `Hom(T_β, T_γ) = 0` for `β ⊄ γ`,
and `End(T_β) ≅ k` as `k`-algebras (`Bricks.rigidFamily`). This is the form of
Göbel and Simson's Theorem 1.2 and Theorem 3.3 recorded as Theorem 5.6 of the
manuscript, here for infinite fields.

The proof glues: take an anchored family over `X ⊕ X` (`Bricks.exists_anchored`)
and let `T_β` be the module glued from the constituents indexed by
`inl '' β ∪ range inr`. Every map `T_β → T_γ` is a scalar multiple of the
inclusion for `β ⊆ γ` (`Bricks.hom_subExt_of_subset`) and vanishes otherwise
(`Bricks.hom_subExt_eq_zero`); the copies indexed by `range inr` give the
dimension `κ`.
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

section Glue

variable {ι : Type u} [DecidableEq ι] {C : Kron k} {B : ι → Kron k} {α β : ∀ i, (B i).V →ₗ[k] C.W}

lemma isBrick_subExt (hC : IsBrickKron C) (hB : ∀ i, IsBrickKron (B i))
    (hCB : ∀ i (f : C ⟶ B i), f = 0) (hBC : ∀ i (f : B i ⟶ C), f = 0)
    (hBB : ∀ i j, i ≠ j → ∀ f : B i ⟶ B j, f = 0) (hns : ∀ i, ¬Splits C (B i) (α i) (β i))
    (S : Set ι) : IsBrickKron (subExt C B α β S) :=
  isBrick_extFamily hC (fun i ↦ hB i) (fun i ↦ hCB i) (fun i ↦ hBC i)
    (fun i j h ↦ hBB i j fun e ↦ h (Subtype.ext e)) fun i ↦ hns i

lemma subIncl_app_zero (C : Kron k) (B : ι → Kron k) (α β : ∀ i, (B i).V →ₗ[k] C.W)
    {S S' : Set ι} (h : S ⊆ S') (v : C.V) :
    ((subIncl C B α β h).app zero).hom (v, 0) = (v, 0) := by
  change inclV C B h (v, 0) = (v, 0)
  simp [inclV]

end Glue

/-- Ranks of direct sums of nonzero spaces are at least the number of summands. -/
lemma le_rank_dfinsupp {S : Type u} {M : S → Type u} [∀ s, AddCommGroup (M s)]
    [∀ s, Module k (M s)] (hM : ∀ s, Nontrivial (M s)) : #S ≤ Module.rank k (Π₀ s, M s) := by
  change #S ≤ Module.rank k (DirectSum S fun s ↦ M s)
  rw [rank_directSum]
  have : ∀ s, (1 : Cardinal.{u}) ≤ Module.rank k (M s) := fun s ↦
    Cardinal.one_le_iff_pos.2 (rank_pos_iff_nontrivial.2 (hM s))
  calc #S = Cardinal.sum fun _ : S ↦ (1 : Cardinal.{u}) := by simp
    _ ≤ _ := sum_le_sum _ _ this

variable [Infinite k]

/-- **Theorem 5.6** (Göbel–Simson, Theorem 1.2(i),(iii) and Theorem 3.3), for
infinite fields: a family of Kronecker modules `T_β`, `β ⊆ X`, with
`Hom(T_β, T_γ) ≅ k` exactly when `β ⊆ γ`. -/
theorem rigidFamily (X : Type u) [Infinite X] :
    ∃ T : Set X → Kron k,
      (∀ b, Module.rank k (T b).V = #X ∧ Module.rank k (T b).W = #X ∧ Kron.ABInj (T b) ∧
        LinearMap.range (T b).a.hom ⊔ LinearMap.range (T b).b.hom = ⊤) ∧
      (∀ b c, b ⊆ c → Nonempty ((T b ⟶ T c) ≃ₗ[k] k)) ∧
      (∀ b c, ¬ b ⊆ c → ∀ f : T b ⟶ T c, f = 0) ∧
      (∀ b, Nonempty (End (T b) ≃ₐ[k] k)) ∧ ∀ b, IsBrickKron (T b) := by
  classical
  have hX0 : ℵ₀ ≤ #X := Cardinal.infinite_iff.1 inferInstance
  obtain ⟨J, _, σ, hJ, hCd, hBd, hiC, hiB⟩ := exists_anchored (k := k) #X hX0
  have hXX' : #(X ⊕ X) = #X := by
    rw [mk_sum, lift_id, add_eq_self hX0]
  have hXX : #(X ⊕ X) ≤ #J := by rw [hXX', hJ]
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hXX
  let σ2 := σ.comap e
  let S : Set X → Set (X ⊕ X) := fun b ↦ Sum.inl '' b ∪ Set.range Sum.inr
  have hS : ∀ b c, S b ⊆ S c ↔ b ⊆ c := fun b c ↦ by
    constructor
    · intro h x hx
      rcases h (Or.inl ⟨x, hx, rfl⟩) with ⟨y, hy, hyx⟩ | ⟨y, hy⟩
      · exact Sum.inl_injective hyx ▸ hy
      · exact absurd hy (by simp)
    · rintro h _ (⟨x, hx, rfl⟩ | hr)
      · exact Or.inl ⟨x, h hx, rfl⟩
      · exact Or.inr hr
  let T : Set X → Kron k := fun b ↦ σ2.F (S b)
  have hbrick : ∀ b, IsBrickKron (T b) := fun b ↦
    isBrick_subExt σ2.hC σ2.hB σ2.hCB σ2.hBC σ2.hBB σ2.hns (S b)
  have hinj : ∀ b, Kron.ABInj (T b) := fun b ↦
    abInj_subExt _ _ hiC (fun j ↦ hiB (e j)) (S b)
  -- dimensions
  have hrV : ∀ b, Module.rank k (T b).V = #X := fun b ↦ by
    change Module.rank k (σ2.C.V × Π₀ i : S b, (σ2.B i).V) = #X
    rw [rank_prod']
    refine le_antisymm ((add_le_add ((rank_V_le_dim _).trans hCd)
      (Anchored.rank_sum_le hX0 hXX'.le (fun j ↦ (rank_V_le_dim _).trans
        (hBd (e j))) (S b))).trans (add_eq_self hX0).le) ?_
    refine le_trans ?_ le_add_self
    have hsub : #(Set.range (Sum.inr : X → X ⊕ X)) ≤ #(S b) :=
      mk_le_mk_of_subset Set.subset_union_right
    rw [mk_range_eq _ Sum.inr_injective] at hsub
    exact hsub.trans (le_rank_dfinsupp fun i ↦ nontrivial_of_ne _ 0 (σ2.hy i))
  have hrW : ∀ b, Module.rank k (T b).W = #X := fun b ↦ by
    refine le_antisymm ?_ ((hrV b).symm.le.trans (LinearMap.rank_le_of_injective _ (hinj b).1))
    change Module.rank k (σ2.C.W × Π₀ i : S b, (σ2.B i).W) ≤ #X
    rw [rank_prod']
    refine (add_le_add ((rank_W_le_dim _).trans hCd)
      (Anchored.rank_sum_le hX0 hXX'.le
        (fun j ↦ (rank_W_le_dim _).trans (hBd (e j))) (S b))).trans (add_eq_self hX0).le
  have hC : ∀ b, InC (T b) := fun b ↦ (hbrick b).inC (by
    change ℵ₀ ≤ Module.rank k (T b).V + Module.rank k (T b).W
    rw [hrV]; exact hX0.trans le_self_add)
  refine ⟨T, fun b ↦ ⟨hrV b, hrW b, hinj b, (hC b).2⟩, fun b c hbc ↦ ?_, fun b c hbc f ↦ ?_,
    fun b ↦ ?_, hbrick⟩
  · -- `Hom(T_b, T_c) ≅ k`, spanned by the inclusion
    let ι0 := subIncl σ2.C σ2.B σ2.α σ2.β ((hS b c).2 hbc)
    have hι0 : ι0 ≠ 0 := fun h ↦ σ2.hc0 (by
      have e1 : (ι0.app zero).hom (σ2.c0, 0) = (σ2.c0, 0) := subIncl_app_zero _ _ _ _ _ _
      rw [h, NatTrans.app_zero, ModuleCat.hom_zero] at e1
      exact (congrArg Prod.fst e1).symm)
    let L : k →ₗ[k] (T b ⟶ T c) := LinearMap.toSpanSingleton k _ ι0
    have hL : Function.Bijective L := by
      refine ⟨fun x y hxy ↦ ?_, fun f ↦ ?_⟩
      · have : (x - y) • ι0 = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 hxy
        exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hι0)
      · obtain ⟨t, ht⟩ := hom_subExt_of_subset σ2.hC σ2.hB σ2.hCB σ2.hBC σ2.hBB σ2.hns
          ((hS b c).2 hbc) f
        exact ⟨t, ht.symm⟩
    exact ⟨(LinearEquiv.ofBijective L hL).symm⟩
  · -- `Hom(T_b, T_c) = 0` for `b ⊄ c`
    obtain ⟨x, hxb, hxc⟩ := Set.not_subset.1 hbc
    exact hom_subExt_eq_zero σ2.hC σ2.hB σ2.hCB σ2.hBC σ2.hBB σ2.hns
      (j := Sum.inl x) (Or.inl ⟨x, hxb, rfl⟩) (fun h ↦ by
        rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy⟩
        · exact hxc (Sum.inl_injective hyx ▸ hy)
        · exact absurd hy (by simp)) f
  · -- `End(T_b) ≅ k`
    have hid : (𝟙 (T b) : T b ⟶ T b) ≠ 0 := fun h ↦
      (hbrick b).1 ((IsZero.iff_id_eq_zero _).2 h)
    have hbij : Function.Bijective (algebraMap k (End (T b))) := by
      refine ⟨fun x y hxy ↦ ?_, fun f ↦ ?_⟩
      · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at hxy
        have : (x - y) • (𝟙 (T b) : T b ⟶ T b) = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 hxy
        exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hid)
      · obtain ⟨t, ht⟩ := (hbrick b).2 f
        exact ⟨t, by rw [Algebra.algebraMap_eq_smul_one, ht]; rfl⟩
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (End (T b))) hbij).symm⟩

end Bricks

end LargeIndecomposable
