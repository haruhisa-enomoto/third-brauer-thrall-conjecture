module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.WalkCase

/-!
# Monomial presentations and bands

The data form (3′) of Theorem 3.10 for a monomial presentation. Let
`π : kQ → B` be surjective with kernel spanned by the words of a set `P` of
paths (for a monomial ideal `I`, the paths lying in `I`). Let `p : D_w → Q` be
the cycle of a primitive cyclically reduced closed walk such that no directed
path of `D_w` has its label word in `P` ("no directed segment of a power of the
walk lies in `I`"). Then every `p_*L(T)` is a `B`-module, so the walk gives
walk data (`Walk.MonomialBand.toWalkData`).

The key computation (`pdAct_word_blk`): a block `e_j · w · e_i` of the action of
a path `w` on a push-down is nonzero only if `w` lifts to a directed path of
`D` from `i` to `j`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

namespace FinQuiver

variable {D : FinQuiver}

/-- `PathFrom i l j`: the list `l` of arrows is a directed path from `i` to `j`. -/
def PathFrom : D.V → List D.A → D.V → Prop
  | i, [], j => i = j
  | i, e :: l, j => D.src e = i ∧ PathFrom (D.tgt e) l j

end FinQuiver

namespace Rep

variable {k : Type u} [Field k] {D Q : FinQuiver} (p : FinQuiver.Hom D Q) (X : Rep k D)

lemma word_cons (c : Q.A) (l : List Q.A) :
    FinQuiver.word k Q (c :: l) = FinQuiver.word k Q l * FinQuiver.arrow k Q c := rfl

/-- A nonzero block of the action of a path lifts to a directed path of `D`. -/
theorem pdAct_word_blk : ∀ (l : List Q.A) (i j : D.V),
    X.idm j ∘ₗ X.pdAct p (FinQuiver.word k Q l) ∘ₗ X.idm i ≠ 0 →
      ∃ le : List D.A, FinQuiver.PathFrom i le j ∧ le.map p.arr = l
  | [], i, j, h => by
    refine ⟨[], ?_, rfl⟩
    by_contra hij
    apply h
    simp only [FinQuiver.word, map_one, Module.End.one_eq_id, LinearMap.id_comp, idm_comp_idm]
    exact if_neg (Ne.symm hij)
  | c :: l, i, j, h => by
    rw [word_cons, map_mul, Module.End.mul_eq_comp, pdAct_arrow, LinearMap.comp_assoc,
      pdArr_comp_idm, comp_finsetSum, comp_finsetSum] at h
    obtain ⟨β, hβ, hβ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
    have h' : X.idm j ∘ₗ X.pdAct p (FinQuiver.word k Q l) ∘ₗ X.idm (D.tgt β) ≠ 0 := by
      intro h0
      apply hβ0
      rw [arrOp_eq_idm_comp β]
      calc X.idm j ∘ₗ X.pdAct p (FinQuiver.word k Q l) ∘ₗ X.idm (D.tgt β) ∘ₗ X.arrOp β
          = (X.idm j ∘ₗ X.pdAct p (FinQuiver.word k Q l) ∘ₗ X.idm (D.tgt β)) ∘ₗ X.arrOp β := rfl
        _ = 0 := by rw [h0, LinearMap.zero_comp]
    obtain ⟨le, hle, hmap⟩ := pdAct_word_blk l (D.tgt β) j h'
    exact ⟨β :: le, ⟨hβ.2, hle⟩, by simp [hβ.1, hmap]⟩

/-- A path that lifts to no directed path of `D` acts by zero on push-downs. -/
theorem pdAct_word_eq_zero {l : List Q.A}
    (h : ∀ (le : List D.A) (i j : D.V), FinQuiver.PathFrom i le j → le.map p.arr ≠ l) :
    X.pdAct p (FinQuiver.word k Q l) = 0 := by
  refine ext_blocks fun j i ↦ ?_
  simp only [LinearMap.zero_comp, LinearMap.comp_zero]
  by_contra hne
  obtain ⟨le, hle, hmap⟩ := X.pdAct_word_blk p l i j hne
  exact h le i j hle hmap

end Rep

namespace Walk

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

variable (k B) in
/-- Alternative (3′) of Theorem 3.10 for a monomial presentation: a presentation
`π : kQ → B` whose kernel is spanned by the words of a set `P` of paths, and the
cycle of a primitive cyclically reduced closed walk none of whose directed
paths has its label word in `P`. -/
structure MonomialBand where
  /-- The cycle has `n + 2` vertices. -/
  n : ℕ
  /-- The orientations of the middle arrows. -/
  ε : Fin n → Bool
  /-- The quiver of the presentation. -/
  Q : FinQuiver
  /-- The map from the cycle to `Q`. -/
  p : FinQuiver.Hom (cycleQuiver n ε) Q
  locInj : p.LocallyInjective
  primitive : Primitive p (cycleCoords n ε)
  /-- The presentation. -/
  π : Q.PathAlgebra k →ₐ[k] B
  surj : Function.Surjective π
  /-- The paths in the kernel. -/
  P : Set (List Q.A)
  ker_le : ∀ z, π z = 0 → z ∈ Submodule.span k (FinQuiver.word k Q '' P)
  band : ∀ (le : List (cycleQuiver n ε).A) (i j : (cycleQuiver n ε).V),
    FinQuiver.PathFrom i le j → le.map p.arr ∉ P

/-- Monomial band data give walk data. -/
def MonomialBand.toWalkData (M : MonomialBand k B) : WalkData k B where
  n := M.n
  ε := M.ε
  Q := M.Q
  p := M.p
  locInj := M.locInj
  primitive := M.primitive
  π := M.π
  surj := M.surj
  kills T z hz := by
    suffices key : ∀ z ∈ Submodule.span k (FinQuiver.word k M.Q '' M.P),
        (cycleRep (ε := M.ε) T.obj).pdAct M.p z = 0 from key z (M.ker_le z hz)
    intro z hz'
    induction hz' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact Rep.pdAct_word_eq_zero M.p _ fun le i j hle hmap ↦ M.band le i j hle (hmap ▸ hl)
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Walk

end LargeIndecomposable
