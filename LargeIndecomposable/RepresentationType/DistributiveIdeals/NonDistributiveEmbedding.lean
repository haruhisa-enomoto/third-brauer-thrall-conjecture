module

public import LargeIndecomposable.RepresentationType.DistributiveIdeals.SoclePair
public import LargeIndecomposable.RepresentationEmbeddings.QuotientConstruction.QuotientEmbedding
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Controlled
public import LargeIndecomposable.Modules.Morita.Inflation
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEnd

/-!
# The nondistributive case of Theorem 3.10

A split basic algebra `B` whose lattice of two-sided ideals is not
distributive has a quotient `Λ = B/K` with a socle pair (Bongartz,
Corollary 2); the quotient construction `F₁` over `Λ` is a controlled
embedding (Proposition 4.1), and inflation along `B → Λ` transports it to `B`.
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

namespace QuotientData

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]

/-- The quotient construction as a controlled embedding. -/
def controlledEmbedding (Q : QuotientData k Λ) (hx : TopOneDim k Q.ex) (hy : TopOneDim k Q.ey) :
    ControlledEmbedding k Λ :=
  haveI : (Φfin Q).Faithful := ⟨fun h ↦ (retractions hx hy).map_injective h⟩
  { Φ := Φfin Q
    isRepEmbeddingFin := isRepEmbeddingFin hx hy (exists_jacobson_list_prod (k := k) (Λ := Λ)).choose_spec
    R := retractionsCfin hx hy
    n := (exists_jacobson_list_prod (k := k) (Λ := Λ)).choose
    bound := nilpotentBound_Cfin hx hy (exists_jacobson_list_prod (k := k) (Λ := Λ)).choose_spec }

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

lemma preservesSES : ControlledEmbedding.PreservesSES (functor (k := k) K) := by
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

end Inflation

/-- The nondistributive case of Theorem 3.10: a split basic algebra whose
ideal lattice is not distributive has a controlled embedding. -/
theorem SplitBasicData.nonempty_controlledEmbedding {B : Type u} [Ring B] [Algebra k B]
    [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
    (hnd : ¬ IsDistribIdeals B) : Nonempty (ControlledEmbedding k B) := by
  obtain ⟨x, y, K, hK, Q, hQx, hQy⟩ := S.exists_quotientData hnd
  have hx : TopOneDim k Q.ex := hQx ▸ (S.quotient K hK).topOneDim x
  have hy : TopOneDim k Q.ey := hQy ▸ (S.quotient K hK).topOneDim y
  exact ⟨(Q.controlledEmbedding hx hy).transport (Inflation.functor K)
    (Inflation.fullyFaithful K) (Inflation.preservesSES K) (Inflation.finite K)⟩

end LargeIndecomposable
