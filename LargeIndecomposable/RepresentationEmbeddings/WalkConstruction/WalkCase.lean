module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.PdEmbedding
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.CycleCoords

/-!
# The walk construction as a controlled embedding

Alternative (3) of Theorem 3.10 in data form. `Walk.WalkData k A` consists of a
presentation `π : kQ → A` (a surjective algebra homomorphism) and a primitive
walk, given by its cycle `D_w` with a source and the map `p : D_w → Q`
satisfying (3.4), such that `p_*L(T)` (Construction 3.9) is an `A`-module for
every `T ∈ D_fin`. It gives push-down data (`PushDown.PdData`): the classes of
block positions are the components of the matching quiver (Lemma 4.6), and a
morphism `φ` with `L(φ)` vanishing at a vertex is zero by Lemma 2.2(1).
With the sink convention, the facts about `S₋` used in Theorem 2.7
holds automatically (`WalkData.toPdDatum`), so walk data alone yield a
controlled embedding.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

namespace Walk

instance (n : ℕ) (ε : Fin n → Bool) : (cycleFunctor (k := k) n ε).Additive where
  map_add {_ _ _ _} := Rep.hom_ext fun i ↦ by rcases i <;> rfl

/-- The functor `L` of Construction 3.9 on `D_fin`. -/
abbrev LD (n : ℕ) (ε : Fin n → Bool) : Dfin k ⥤ Rep k (cycleQuiver n ε) :=
  (InDfin (k := k)).ι ⋙ cycleFunctor n ε

/-- `L` on `D_fin` is fully faithful. -/
def LDFullyFaithful (n : ℕ) (ε : Fin n → Bool) : (LD (k := k) n ε).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).comp cycleFunctorFullyFaithful

lemma zeroAtVertex (n : ℕ) (ε : Fin n → Bool) : PushDown.ZeroAtVertex (LD (k := k) n ε) := by
  intro T U hT φ c h
  ext1
  rcases c with _ | j
  · exact hom_eq_zero_of_app_one U.2.1 φ.hom h
  · exact hom_eq_zero_of_app_zero hT φ.hom h

variable {n : ℕ} {ε : Fin n → Bool} {Q : FinQuiver}

variable (p : FinQuiver.Hom (cycleQuiver n ε) Q) in
/-- Lying in one component of the matching quiver. -/
def connSetoid : Setoid ((cycleQuiver n ε).V × (cycleQuiver n ε).V) where
  r := Conn p
  iseqv := ⟨fun _ ↦ Relation.ReflTransGen.refl, conn_symm (cycleCoords n ε), conn_trans⟩

/-- The components of the matching quiver as classes of block positions
(Lemma 4.6). -/
def blockClasses {p : FinQuiver.Hom (cycleQuiver n ε) Q} (hloc : p.LocallyInjective)
    (hprim : Primitive p (cycleCoords n ε)) : PushDown.BlockClasses p :=
  letI := Classical.decRel (connSetoid p).r
  { ι := Quotient (connSetoid p)
    fin := Quotient.fintype _
    cls := Quotient.mk _
    sat := fun _ _ h ↦ Quotient.sound (Relation.ReflTransGen.single (adj_src_tgt p h))
    diag := fun _ _ h ha ↦ (diag_iff_of_conn (cycleCoords n ε) hloc (Quotient.exact h)).1 ha
    col := fun _ _ _ _ _ h ↦ congrArg Prod.fst
      (eq_of_conn_of_snd_eq (cycleCoords n ε) hloc Relation.ReflTransGen.refl (Quotient.exact h) rfl)
    zeroCol := fun κ ↦ by
      induction κ using Quotient.ind with
      | _ a₀ =>
        by_cases hd : a₀.1 = a₀.2
        · refine ⟨none, fun j hj ↦ ?_⟩
          exact ((diag_iff_of_conn (cycleCoords n ε) hloc (Quotient.exact hj.symm)).1 hd)
        · obtain ⟨i, hi⟩ := exists_col_not_conn (cycleCoords n ε) hloc hprim hd
          exact ⟨i, fun j hj ↦ absurd (Quotient.exact hj.symm) (hi j)⟩ }

variable (k A) in
/-- The data of alternative (3) of Theorem 3.10, apart from the
representation-embedding property. -/
structure WalkData where
  /-- The cycle has `n + 2` vertices. -/
  n : ℕ
  /-- The orientations of the middle arrows of the cycle. -/
  ε : Fin n → Bool
  /-- The quiver of the presentation. -/
  Q : FinQuiver
  /-- The map from the cycle to `Q`. -/
  p : FinQuiver.Hom (cycleQuiver n ε) Q
  locInj : p.LocallyInjective
  primitive : Primitive p (cycleCoords n ε)
  /-- The presentation `kQ → A`. -/
  π : Q.PathAlgebra k →ₐ[k] A
  surj : Function.Surjective π
  /-- `p_*L(T)` is an `A`-module for `T ∈ D_fin`. -/
  kills : ∀ (T : Dfin k) (z : Q.PathAlgebra k), π z = 0 → (cycleRep (ε := ε) T.obj).pdAct p z = 0

/-- Walk data as push-down data. -/
def WalkData.toPdData (W : WalkData k A) : PushDown.PdData k A where
  D := cycleQuiver W.n W.ε
  Q := W.Q
  p := W.p
  locInj := W.locInj
  B := blockClasses W.locInj W.primitive
  L := LD W.n W.ε
  hL := LDFullyFaithful W.n W.ε
  map_smul _ _ i := by rcases i <;> rfl
  zero := zeroAtVertex W.n W.ε
  exact _ _ _ _ _ h i := by
    rcases i with _ | j
    · exact h one
    · exact h zero
  fin T i := by
    rcases i with _ | j
    · exact T.2.2.2
    · exact T.2.2.1
  π := W.π
  surj := W.surj
  kills := W.kills

lemma finrank_tot (X : Dfin k) :
    Module.finrank k ((LD (k := k) n ε).obj X).Tot =
      Module.finrank k X.obj.W + (n + 1) * Module.finrank k X.obj.V := by
  have hX := X.2.2
  have : ∀ i : (cycleQuiver n ε).V, Module.Finite k (((LD (k := k) n ε).obj X).obj i) := by
    intro i; rcases i with _ | j
    · exact hX.2
    · exact hX.1
  rw [Module.finrank_pi_fintype, Fintype.sum_option]
  change Module.finrank k X.obj.W + ∑ _j : Fin (n + 1), Module.finrank k X.obj.V = _
  simp [Finset.sum_const]

/-- With the sink convention `L(S₋)` is the simple
representation at the sink, so `F₃(S₋)` has dimension one, while `F₃(T)` for
`T ∈ C` has dimension `0` or at least `n + 2`. -/
def WalkData.toPdDatum (W : WalkData k A) : PushDown.PdDatum k A where
  toPdData := W.toPdData
  indecS := W.toPdData.isIndecomposable_of_finrank_eq_one (by
    change Module.finrank k ((LD (k := k) W.n W.ε).obj Extension.SminusFin).Tot = 1
    rw [finrank_tot]
    change Module.finrank k k + (W.n + 1) * Module.finrank k PUnit = 1
    rw [Module.finrank_self, Module.finrank_zero_of_subsingleton, mul_zero, add_zero])
  notIsoS X hX := ⟨fun e ↦ by
    have h := W.toPdData.finrank_eq_of_iso e
    change Module.finrank k ((LD (k := k) W.n W.ε).obj Extension.SminusFin).Tot =
      Module.finrank k ((LD (k := k) W.n W.ε).obj X).Tot at h
    rw [finrank_tot, finrank_tot] at h
    change Module.finrank k k + (W.n + 1) * Module.finrank k PUnit = _ at h
    rw [Module.finrank_self, Module.finrank_zero_of_subsingleton, mul_zero, add_zero] at h
    have hX' := X.2.2
    have : Module.Finite k X.obj.V := hX'.1
    have : Module.Finite k X.obj.W := hX'.2
    have hV : Module.finrank k X.obj.V = 0 → Module.finrank k X.obj.W = 0 := by
      intro h0
      have : Subsingleton X.obj.V := Module.finrank_zero_iff.1 h0
      refine Module.finrank_zero_iff.2 ⟨fun w w' ↦ ?_⟩
      have htop : (⊤ : Submodule k X.obj.W) = ⊥ := by
        rw [← hX.2]
        simp [Subsingleton.elim _ (0 : X.obj.V →ₗ[k] X.obj.W)]
      have hw : w ∈ (⊥ : Submodule k X.obj.W) := htop ▸ Submodule.mem_top
      have hw' : w' ∈ (⊥ : Submodule k X.obj.W) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hw hw'
      rw [hw, hw']
    have hW : Module.finrank k X.obj.W = 0 → Module.finrank k X.obj.V = 0 := by
      intro h0
      have : Subsingleton X.obj.W := Module.finrank_zero_iff.1 h0
      refine Module.finrank_zero_iff.2 ⟨fun v v' ↦ ?_⟩
      have hd := (inD_iff X.obj).1 hX.1
      rw [hd v (Subsingleton.elim _ _) (Subsingleton.elim _ _),
        hd v' (Subsingleton.elim _ _) (Subsingleton.elim _ _)]
    rcases Nat.eq_zero_or_pos (Module.finrank k X.obj.V) with h0 | h0
    · rw [h0, hV h0] at h; simp at h
    · have hW0 : Module.finrank k X.obj.W ≠ 0 := fun h1 ↦ by have := hW h1; omega
      have hm := Nat.mul_pos (show 0 < W.n + 1 by omega) h0
      omega⟩

/-- The walk construction as a controlled embedding. -/
def WalkData.controlledEmbedding (W : WalkData k A) : ControlledEmbedding k A :=
  W.toPdDatum.controlledEmbedding

end Walk

end LargeIndecomposable
