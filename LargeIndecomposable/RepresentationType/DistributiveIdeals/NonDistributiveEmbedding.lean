module

public import LargeIndecomposable.RepresentationType.DistributiveIdeals.SoclePair
public import LargeIndecomposable.RepresentationEmbeddings.QuotientConstruction.QuotientEmbedding
public import LargeIndecomposable.Modules.Morita.Inflation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEnd

/-!
# The nondistributive case of Theorem 3.14

A split basic algebra `B` whose lattice of two-sided ideals is not
distributive has a quotient `Λ = B/K` with a socle pair (Bongartz,
Corollary 2); the quotient construction `F₁` over `Λ` gives the data of
Theorem 5.2 (Lemma 3.4, Proposition 4.1), and inflation along `B → Λ`
transports it to `B`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

variable {k : Type u} [Field k]

/-- In a split basic algebra every `Λ e_x / J e_x` is one-dimensional. -/
lemma SplitBasicData.topOneDim {Λ : Type u} [Ring Λ] [Algebra k Λ] {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : SplitBasicData k Λ ι) (x : ι) : TopOneDim k (S.e x) := by
  intro r
  obtain ⟨c, hc⟩ := S.corner_diag x r
  refine ⟨c, ?_⟩
  have hsum : r * S.e x = ∑ z, S.e z * r * S.e x := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, S.complete.complete, one_mul]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x), add_sub_right_comm]
  refine add_mem hc (Submodule.sum_mem _ fun z hz ↦ ?_)
  exact S.corner_offdiag z x (Finset.ne_of_mem_erase hz) r

/-- The Jacobson radical of a finite-dimensional algebra is nilpotent, in the
form of products of `n` radical elements. -/
lemma exists_jacobson_list_prod {Λ : Type u} [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    ∃ n : ℕ, ∀ l : List Λ, l.length = n → (∀ j ∈ l, j ∈ Ring.jacobson Λ) → l.prod = 0 := by
  have : IsArtinianRing Λ := IsArtinianRing.of_finite k Λ
  have : IsSemiprimaryRing Λ := inferInstance
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := Λ)
  clear this
  refine ⟨n, fun l hl hJ ↦ ?_⟩
  subst hl
  have hmem := prod_ofFn_mem_pow (Ring.jacobson Λ) (fun i : Fin l.length ↦ l.get i)
    (fun i ↦ hJ _ (List.get_mem l i))
  rw [List.ofFn_get, hn] at hmem
  simpa using hmem

/-- The Jacobson radical `J` of a finite-dimensional algebra satisfies `J ^ d = 0` for
`d = dim Λ`: the powers of `J` decrease strictly until they vanish. -/
lemma jacobson_pow_finrank {Λ : Type u} [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    Ring.jacobson Λ ^ Module.finrank k Λ = ⊥ := by
  set J := Ring.jacobson Λ
  have : IsArtinianRing Λ := IsArtinianRing.of_finite k Λ
  obtain ⟨n₀, hn₀⟩ := IsSemiprimaryRing.isNilpotent (R := Λ)
  have hdec : ∀ m, J ^ (m + 1) ≤ J ^ m := by
    intro m
    induction m with
    | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact le_top
    | succ m ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ (n := m)]; exact Ideal.mul_mono_left ih
  have hstab : ∀ m, J ^ (m + 1) = J ^ m → J ^ m = ⊥ := by
    intro m hm
    have : ∀ i, J ^ (m + i) = J ^ m := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [← add_assoc, Submodule.pow_succ, ih, ← Submodule.pow_succ, hm]
    have hanti : ∀ i j, i ≤ j → J ^ j ≤ J ^ i := fun i j hij ↦ by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hij
      induction c with
      | zero => exact le_rfl
      | succ c ih => exact (hdec _).trans (ih (by omega))
    have h0 : J ^ n₀ = ⊥ := hn₀
    rw [← this n₀]
    exact le_bot_iff.1 (h0 ▸ hanti n₀ (m + n₀) (by omega))
  have key : ∀ m, J ^ m = ⊥ ∨
      Module.finrank k ((J ^ m).restrictScalars k) + m ≤ Module.finrank k Λ := by
    intro m
    induction m with
    | zero =>
      right
      rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top, finrank_top]
      omega
    | succ m ih =>
      rcases ih with h | h
      · left; exact le_bot_iff.1 (h ▸ hdec m)
      · by_cases he : J ^ (m + 1) = J ^ m
        · left; rw [he]; exact hstab m he
        · right
          have hlt : (J ^ (m + 1)).restrictScalars k < (J ^ m).restrictScalars k :=
            lt_of_le_of_ne (Submodule.restrictScalars_mono k (hdec m)) fun h ↦ he
              (Submodule.restrictScalars_injective k _ _ h)
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
  rcases key (Module.finrank k Λ) with h | h
  · exact h
  · have h0 : Module.finrank k ((J ^ Module.finrank k Λ).restrictScalars k) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h0
    exact (Submodule.restrictScalars_eq_bot_iff k Λ Λ).1 h0

/-- Products of `dim Λ` radical elements vanish. -/
lemma jacobson_list_prod_finrank {Λ : Type u} [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]
    (l : List Λ) (hl : l.length = Module.finrank k Λ) (hJ : ∀ j ∈ l, j ∈ Ring.jacobson Λ) :
    l.prod = 0 := by
  have hmem := prod_ofFn_mem_pow (Ring.jacobson Λ) (fun i : Fin l.length ↦ l.get i)
    (fun i ↦ hJ _ (List.get_mem l i))
  rw [List.ofFn_get, hl, jacobson_pow_finrank (k := k)] at hmem
  simpa using hmem

namespace QuotientData

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]

/-- The quotient construction gives the data of Theorem 5.2, with the
nilpotence bound `n = dim Λ` (so that `J^n = 0`). -/
def embeddingDataOf (Q : QuotientData k Λ) (hx : TopOneDim k Q.ex) (hy : TopOneDim k Q.ey) :
    EmbeddingData k Λ :=
  embeddingData hx hy (jacobson_list_prod_finrank (k := k) (Λ := Λ))

lemma embeddingDataOf_n (Q : QuotientData k Λ) (hx : TopOneDim k Q.ex)
    (hy : TopOneDim k Q.ey) : (Q.embeddingDataOf hx hy).n = Module.finrank k Λ := rfl

end QuotientData

/-! ### Inflation along a quotient map -/

namespace Inflation

variable {B : Type u} [Ring B] [Algebra k B] (K : TwoSidedIdeal B)

/-- Inflation along `B → B/K`. -/
abbrev functor : ModuleCat.{u} (B ⧸ K.asIdeal) ⥤ ModuleCat.{u} B :=
  ModuleCat.restrictScalars.{u} (Ideal.Quotient.mkₐ k K.asIdeal).toRingHom

instance : (functor (k := k) K).Linear k := Reduction.restrictScalars_linear k _

def fullyFaithful : (functor (k := k) K).FullyFaithful :=
  haveI := Reduction.restrictScalars_full (π := (Ideal.Quotient.mkₐ k K.asIdeal).toRingHom)
    Ideal.Quotient.mk_surjective
  Functor.FullyFaithful.ofFullyFaithful _

lemma preservesSES : PreservesSES (functor (k := k) K) := by
  intro L M N f g h₁ h₂ h₃
  refine ⟨h₁, h₂, ?_⟩
  ext x
  have := Iff.of_eq (congrArg (x ∈ ·) h₃)
  simp only [LinearMap.mem_range, LinearMap.mem_ker] at this ⊢
  exact this

lemma finite (M : ModuleCat.{u} (B ⧸ K.asIdeal))
    (h : Module.Finite k (RestrictScalars k (B ⧸ K.asIdeal) M)) :
    Module.Finite k (RestrictScalars k B ((functor (k := k) K).obj M)) :=
  Module.Finite.equiv (Reduction.restrictScalarsLinearEquiv k _ M).symm

/-- Inflation commutes with filtered colimits: it is a left adjoint. -/
instance : PreservesFilteredColimitsOfSize.{u, u} (functor (k := k) K) :=
  haveI : PreservesColimitsOfSize.{u, u} (functor (k := k) K) :=
    Adjunction.leftAdjoint_preservesColimits
      (ModuleCat.restrictCoextendScalarsAdj (Ideal.Quotient.mkₐ k K.asIdeal).toRingHom)
  ⟨fun _ _ _ ↦ inferInstance⟩

end Inflation

/-- The nondistributive case of Theorem 3.14: a split basic algebra whose
ideal lattice is not distributive has the data of Theorem 5.2. -/
theorem SplitBasicData.nonempty_embeddingData {B : Type u} [Ring B] [Algebra k B]
    [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
    (hnd : ¬ IsDistribIdeals B) : Nonempty (EmbeddingData k B) := by
  obtain ⟨x, y, K, hK, Q, hQx, hQy⟩ := S.exists_quotientData hnd
  have hx : TopOneDim k Q.ex := hQx ▸ (S.quotient K hK).topOneDim x
  have hy : TopOneDim k Q.ey := hQy ▸ (S.quotient K hK).topOneDim y
  exact ⟨(Q.embeddingDataOf hx hy).transport (Inflation.functor K)
    (Inflation.fullyFaithful K) (Inflation.preservesSES K) (Inflation.finite K)⟩

/-- The nondistributive case with the nilpotence bound `n ≤ dim B`: the quotient
construction is over a quotient of `B`, whose radical satisfies `J ^ (dim B) = 0`. -/
theorem SplitBasicData.exists_embeddingData_le {B : Type u} [Ring B] [Algebra k B]
    [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
    (hnd : ¬ IsDistribIdeals B) : ∃ E : EmbeddingData k B, E.n ≤ Module.finrank k B := by
  obtain ⟨x, y, K, hK, Q, hQx, hQy⟩ := S.exists_quotientData hnd
  have hx : TopOneDim k Q.ex := hQx ▸ (S.quotient K hK).topOneDim x
  have hy : TopOneDim k Q.ey := hQy ▸ (S.quotient K hK).topOneDim y
  refine ⟨(Q.embeddingDataOf hx hy).transport (Inflation.functor K)
    (Inflation.fullyFaithful K) (Inflation.preservesSES K) (Inflation.finite K), ?_⟩
  change Module.finrank k (B ⧸ K.asIdeal) ≤ Module.finrank k B
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.mkₐ k K.asIdeal).toLinearMap) Ideal.Quotient.mk_surjective

end LargeIndecomposable
