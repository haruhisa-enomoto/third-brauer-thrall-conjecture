module

public import LargeIndecomposable.RepresentationType.DistributiveIdeals.Layers
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A distributive ideal lattice of a finite-dimensional algebra is finite

For an ideal `K ≠ B` choose an ideal `J > K` of least dimension. For ideals
`I ≥ K` the meet `I ⊓ J` is `K` or `J`, and `I ↦ (I ⊓ J, I ⊔ J)` is injective
by distributivity, so the ideals above `K` are finite when those above `J` are
(`finite_twoSidedIdeal_of_isDistribIdeals`, induction on the codimension).
This replaces representation-finiteness as the input of the ported BGRS
comparability theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

universe u v

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B] [FiniteDimensional k B]

/-- An ideal as a `k`-subspace. -/
def _root_.TwoSidedIdeal.toSubk (I : TwoSidedIdeal B) : Submodule k B where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c b hb := by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ hb

omit [FiniteDimensional k B] in
lemma _root_.TwoSidedIdeal.toSubk_le {I J : TwoSidedIdeal B} :
    I.toSubk (k := k) ≤ J.toSubk ↔ I ≤ J := Iff.rfl

omit [FiniteDimensional k B] in
lemma _root_.TwoSidedIdeal.toSubk_injective : Function.Injective (TwoSidedIdeal.toSubk (k := k) (B := B)) :=
  fun _ _ h ↦ le_antisymm (TwoSidedIdeal.toSubk_le.1 h.le) (TwoSidedIdeal.toSubk_le.1 h.ge)

variable (k) in
/-- The dimension of an ideal. -/
noncomputable def _root_.TwoSidedIdeal.dimk (I : TwoSidedIdeal B) : ℕ := Module.finrank k (I.toSubk (k := k))

lemma _root_.TwoSidedIdeal.dimk_lt {I J : TwoSidedIdeal B} (h : I < J) : I.dimk k < J.dimk k :=
  Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (TwoSidedIdeal.toSubk_le.2 h.le)
    fun e ↦ h.ne (TwoSidedIdeal.toSubk_injective e))

lemma _root_.TwoSidedIdeal.dimk_le_top (I : TwoSidedIdeal B) : I.dimk k ≤ (⊤ : TwoSidedIdeal B).dimk k :=
  Submodule.finrank_mono (TwoSidedIdeal.toSubk_le.2 le_top)

lemma finite_ge_of_isDistribIdeals (hd : IsDistribIdeals B) :
    ∀ n (K : TwoSidedIdeal B), (⊤ : TwoSidedIdeal B).dimk k - K.dimk k = n →
      {I : TwoSidedIdeal B | K ≤ I}.Finite := by
  let _ : DistribLattice (TwoSidedIdeal B) :=
    DistribLattice.ofInfSupLe fun I J K ↦ (hd I J K).le
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn
    by_cases hK : K = ⊤
    · subst hK
      refine (Set.finite_singleton ⊤).subset fun I hI ↦ ?_
      exact Set.mem_singleton_iff.2 (top_le_iff.1 hI)
    have hex : ∃ m, ∃ J : TwoSidedIdeal B, K < J ∧ J.dimk k = m :=
      ⟨_, ⊤, lt_top_iff_ne_top.2 hK, rfl⟩
    classical
    obtain ⟨J, hKJ, hJm⟩ := Nat.find_spec hex
    have hmin : ∀ L : TwoSidedIdeal B, K < L → J.dimk k ≤ L.dimk k := fun L hL ↦
      hJm ▸ Nat.find_min' hex ⟨L, hL, rfl⟩
    have hmeet : ∀ I : TwoSidedIdeal B, K ≤ I → I ⊓ J = K ∨ I ⊓ J = J := by
      intro I hI
      by_cases h : I ⊓ J = K
      · exact Or.inl h
      · right
        have hlt : K < I ⊓ J := lt_of_le_of_ne (le_inf hI hKJ.le) (Ne.symm h)
        by_contra hne
        exact absurd (hmin _ hlt) (not_le.2 (TwoSidedIdeal.dimk_lt (lt_of_le_of_ne inf_le_right hne)))
    have hJfin : {I : TwoSidedIdeal B | J ≤ I}.Finite := by
      refine ih ((⊤ : TwoSidedIdeal B).dimk k - J.dimk k) ?_ J rfl
      have h1 := TwoSidedIdeal.dimk_lt (k := k) hKJ
      have h2 := TwoSidedIdeal.dimk_le_top (k := k) J
      omega
    let f : TwoSidedIdeal B → Bool × TwoSidedIdeal B := fun I ↦ (decide (J ≤ I), I ⊔ J)
    refine Set.Finite.of_finite_image (f := f) (((Set.finite_univ (α := Bool)).prod hJfin).subset ?_) ?_
    · rintro _ ⟨I, -, rfl⟩
      exact ⟨Set.mem_univ _, (le_sup_right : J ≤ I ⊔ J)⟩
    · intro I hI I' hI' he
      simp only [f, Prod.mk.injEq] at he
      refine eq_of_inf_eq_sup_eq ?_ he.2
      have hJ : ∀ L : TwoSidedIdeal B, K ≤ L → L ⊓ J = if J ≤ L then J else K := by
        intro L hL
        split_ifs with hJL
        · exact inf_eq_right.2 hJL
        · exact (hmeet L hL).resolve_right fun e ↦ hJL (e ▸ inf_le_left)
      rw [hJ I hI, hJ I' hI', show (J ≤ I) ↔ (J ≤ I') from by simpa using he.1]

omit [Algebra k B] [FiniteDimensional k B] in
/-- A distributive ideal lattice of a finite-dimensional algebra is finite. -/
theorem finite_twoSidedIdeal_of_isDistribIdeals (k : Type u) [Field k] [Algebra k B]
    [FiniteDimensional k B] (hd : IsDistribIdeals B) : Finite (TwoSidedIdeal B) := by
  have := finite_ge_of_isDistribIdeals (k := k) (B := B) hd _ ⊥ rfl
  rw [show {I : TwoSidedIdeal B | ⊥ ≤ I} = Set.univ from Set.eq_univ_of_forall fun I ↦ (bot_le : ⊥ ≤ I)]
    at this
  exact Set.finite_univ_iff.1 this

end LargeIndecomposable
