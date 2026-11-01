module

public import LargeIndecomposable.KroneckerBricks.ExtensionOrth
public import LargeIndecomposable.KroneckerBricks.Medium

/-!
# Iterated gluing: Kronecker bricks below `ℶ_ω(|k|)`

A pool of `M` pairwise Hom-orthogonal bricks of dimension at most `D`, with
non-split extension classes between any two of them, gives a pool of `2^M`
such bricks of dimension at most `M` (`Bricks.Pool.step`): glue over one anchor
along the antichain of subsets `S_Y = {(a, [a ∈ Y])}`. Starting from the pool
of `KroneckerBricks/Medium.lean` this gives bricks of every dimension `κ` with
`|k| ≤ κ < ℶ_ω(|k|)` (`Bricks.exists_brick_of_lt_beth`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair _root_.Cardinal

universe u

variable {k : Type u} [Field k]

namespace Bricks

lemma dim_extFamily {ι : Type u} [DecidableEq ι] (C : Kron k) (B : ι → Kron k)
    (α β : ∀ i, (B i).V →ₗ[k] C.W) :
    (extFamily C B α β).dim = C.dim + Cardinal.sum fun i ↦ (B i).dim := by
  change Module.rank k (C.V × SumV B) + Module.rank k (C.W × SumW B) = _
  rw [rank_prod', rank_prod']
  change _ + Module.rank k (DirectSum ι fun i ↦ ((B i).V : Type u)) + (_ +
    Module.rank k (DirectSum ι fun i ↦ ((B i).W : Type u))) = _
  rw [rank_directSum, rank_directSum]
  simp only [Kron.dim]
  rw [Cardinal.sum_add_distrib']
  ac_rfl

variable (k) in
/-- A pool of `M` pairwise orthogonal bricks of dimension at most `D`, with
non-split extension classes between any two of them. -/
structure Pool (D M : Cardinal.{u}) where
  /-- The index type. -/
  ι : Type u
  [dec : DecidableEq ι]
  /-- The bricks. -/
  X : ι → Kron k
  card : Cardinal.mk ι = M
  brick : ∀ i, IsBrickKron (X i)
  orth : ∀ i j, i ≠ j → ∀ f : X i ⟶ X j, f = 0
  /-- A non-split extension with sub `X i` and quotient `X j`. -/
  cls : ∀ i j, i ≠ j → ∃ α β : (X j).V →ₗ[k] (X i).W, ¬Splits (X i) (X j) α β
  dim_le : ∀ i, (X i).dim ≤ D

attribute [instance] Pool.dec

variable [Infinite k]

/-- The base pool: the bricks `T_{Λ_X}`, `X ⊆ k`. -/
def basePool : Pool k (Cardinal.mk k) (2 ^ Cardinal.mk k) where
  ι := Set k
  dec := Classical.decEq _
  X X := T (LamX X)
  card := Cardinal.mk_set
  brick X := isBrick _ ((diff_lam0_infinite X).nonempty.mono Set.sdiff_subset)
  orth X Y h := hom_eq_zero (diff_infinite h)
  cls X Y h := ⟨0, betaExt (LamX Y) (LamX X) (diff_infinite (Ne.symm h)).nonempty.some,
    not_splits (diff_infinite (Ne.symm h)) (diff_infinite (Ne.symm h)).nonempty.some_mem⟩
  dim_le X := by
    rw [dim_T, Cardinal.lift_id, mk_lamX]
    have hk : Cardinal.aleph0 ≤ Cardinal.mk k := Cardinal.infinite_iff.1 inferInstance
    rw [add_assoc, Cardinal.add_eq_self hk, Cardinal.add_eq_right hk (Cardinal.one_le_aleph0.trans hk)]

namespace Pool

variable {D M : Cardinal.{u}} (P : Pool k D M) (hM : Cardinal.aleph0 ≤ M) (hDM : D ≤ M)

include hM in
lemma infinite_ι : Infinite P.ι := Cardinal.infinite_iff.2 (by rw [P.card]; exact hM)

/-- A chosen anchor. -/
def i0 : P.ι := by
  have := P.infinite_ι hM
  exact Classical.arbitrary _

/-- The constituents: the members other than the anchor. -/
abbrev ι' : Type u := ({P.i0 hM}ᶜ : Set P.ι)

lemma card_ι' : Cardinal.mk (P.ι' hM) = M := by
  have := P.infinite_ι hM
  rw [Cardinal.mk_compl_of_infinite, P.card]
  rw [Cardinal.mk_singleton, P.card]
  exact Cardinal.one_lt_aleph0.trans_le hM

lemma mk_ι'_bool : Cardinal.mk (P.ι' hM × Bool) = Cardinal.mk (P.ι' hM) := by
  rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_bool, Cardinal.lift_ofNat, P.card_ι' hM]
  exact Cardinal.mul_eq_left hM (Cardinal.ofNat_lt_aleph0.le.trans hM) (by norm_num)

/-- An identification `ι' × Bool ≃ ι'`. -/
def codeι : P.ι' hM × Bool ≃ P.ι' hM := (Cardinal.eq.1 (P.mk_ι'_bool hM)).some

open Classical in
/-- The antichain subset `S_Y = {(a, [a ∈ Y])}`. -/
def sY (Y : Set (P.ι' hM)) : Set (P.ι' hM) := Set.range fun a ↦ P.codeι hM (a, decide (a ∈ Y))

lemma mem_sY_not_mem {Y Z : Set (P.ι' hM)} (h : Y ≠ Z) :
    ∃ j, j ∈ P.sY hM Y ∧ j ∉ P.sY hM Z := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ¬(a ∈ Y ↔ a ∈ Z) := by
    by_contra hc
    push Not at hc
    exact h (Set.ext hc)
  refine ⟨P.codeι hM (a, decide (a ∈ Y)), ⟨a, rfl⟩, ?_⟩
  rintro ⟨b, hb⟩
  have := congrArg Prod.fst ((P.codeι hM).injective hb)
  have h2 := congrArg Prod.snd ((P.codeι hM).injective hb)
  simp only at this h2
  subst this
  apply ha
  by_cases hY : b ∈ Y <;> by_cases hZ : b ∈ Z <;> simp_all

/-- The anchor brick. -/
abbrev anchor : Kron k := P.X (P.i0 hM)

/-- The constituent bricks. -/
abbrev cons : P.ι' hM → Kron k := fun i ↦ P.X i.1

lemma ne_i0 (i : P.ι' hM) : P.i0 hM ≠ i.1 := fun h ↦ i.2 h.symm

/-- The gluing classes, with sub the anchor and quotient a constituent. -/
def αc (i : P.ι' hM) : (P.cons hM i).V →ₗ[k] (P.anchor hM).W :=
  (P.cls (P.i0 hM) i.1 (P.ne_i0 hM i)).choose

/-- The second gluing class. -/
def βc (i : P.ι' hM) : (P.cons hM i).V →ₗ[k] (P.anchor hM).W :=
  (P.cls (P.i0 hM) i.1 (P.ne_i0 hM i)).choose_spec.choose

lemma not_splits_c (i : P.ι' hM) : ¬Splits (P.anchor hM) (P.cons hM i) (P.αc hM i) (P.βc hM i) :=
  (P.cls (P.i0 hM) i.1 (P.ne_i0 hM i)).choose_spec.choose_spec

lemma hCB : ∀ i (f : P.anchor hM ⟶ P.cons hM i), f = 0 := fun i ↦ P.orth _ _ (P.ne_i0 hM i)

lemma hBC : ∀ i (f : P.cons hM i ⟶ P.anchor hM), f = 0 := fun i ↦ P.orth _ _ (P.ne_i0 hM i).symm

lemma hBB : ∀ i j, i ≠ j → ∀ f : P.cons hM i ⟶ P.cons hM j, f = 0 := fun i j h ↦
  P.orth _ _ fun e ↦ h (Subtype.ext e)

include hDM in
/-- The next pool. -/
def step : Pool k M (2 ^ M) where
  ι := Set (P.ι' hM)
  dec := Classical.decEq _
  X Y := subExt (P.anchor hM) (P.cons hM) (P.αc hM) (P.βc hM) (P.sY hM Y)
  card := by rw [Cardinal.mk_set, P.card_ι' hM]
  brick Y := isBrick_extFamily (P.brick _) (fun i ↦ P.brick _) (fun i ↦ P.hCB hM i)
    (fun i ↦ P.hBC hM i) (fun i j h ↦ P.hBB hM i j fun e ↦ h (Subtype.ext e))
    (fun i ↦ P.not_splits_c hM i)
  orth Y Z h := by
    obtain ⟨j, hjY, hjZ⟩ := P.mem_sY_not_mem hM h
    exact hom_subExt_eq_zero (P.brick _) (fun i ↦ P.brick _) (P.hCB hM) (P.hBC hM) (P.hBB hM)
      (P.not_splits_c hM) hjY hjZ
  cls Y Z h := by
    obtain ⟨j, hjY, -⟩ := P.mem_sY_not_mem hM h
    obtain ⟨α₀, β₀, hns⟩ := P.cls j.1 (P.i0 hM) (P.ne_i0 hM j).symm
    exact ⟨_, _, not_splits_lift (C := P.anchor hM) (B := P.cons hM) (α := P.αc hM) (β := P.βc hM)
      (S := P.sY hM Z) hjY (α₀ := α₀) (β₀ := β₀) hns⟩
  dim_le Y := by
    change (extFamily _ _ _ _).dim ≤ M
    rw [dim_extFamily]
    have hsum : (Cardinal.sum fun i : P.sY hM Y ↦ (P.cons hM i).dim) ≤ M := by
      calc (Cardinal.sum fun i : P.sY hM Y ↦ (P.cons hM i).dim)
          ≤ Cardinal.sum fun _ : P.sY hM Y ↦ D := Cardinal.sum_le_sum _ _ fun i ↦ P.dim_le _
        _ = Cardinal.mk (P.sY hM Y) * D := by rw [Cardinal.sum_const', ]
        _ ≤ M * M := mul_le_mul' ((Cardinal.mk_set_le _).trans (P.card_ι' hM).le) hDM
        _ = M := Cardinal.mul_eq_self hM
    exact (add_le_add ((P.dim_le _).trans hDM) hsum).trans (Cardinal.add_eq_self hM).le

end Pool

lemma one_le_dim {X : Kron k} (hX : IsBrickKron X) : 1 ≤ X.dim := by
  by_contra h
  push Not at h
  apply hX.1
  have h0 : X.dim = 0 := Cardinal.lt_one_iff_zero.1 h
  have hV : Module.rank k X.V = 0 := le_antisymm (h0 ▸ le_self_add) zero_le
  have hW : Module.rank k X.W = 0 := le_antisymm (h0 ▸ le_add_self) zero_le
  refine Functor.isZero X fun j ↦ ?_
  rw [ModuleCat.isZero_iff_subsingleton]
  cases j
  · exact rank_zero_iff.1 hV
  · exact rank_zero_iff.1 hW

/-- A pool gives bricks of every dimension between its bounds. -/
theorem Pool.exists_brick {D M : Cardinal.{u}} (P : Pool k D M) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hDκ : D ≤ κ) (hκM : κ ≤ M) :
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  have hM : Cardinal.aleph0 ≤ M := hκ.trans hκM
  obtain ⟨S, hS⟩ := Cardinal.le_mk_iff_exists_subset.1
    (show κ ≤ Cardinal.mk (Set.univ : Set (P.ι' hM)) by rwa [Cardinal.mk_univ, P.card_ι' hM])
  classical
  refine ⟨subExt (P.anchor hM) (P.cons hM) (P.αc hM) (P.βc hM) S, ?_,
    isBrick_extFamily (P.brick _) (fun i ↦ P.brick _) (fun i ↦ P.hCB hM i)
    (fun i ↦ P.hBC hM i) (fun i j h ↦ P.hBB hM i j fun e ↦ h (Subtype.ext e))
    (fun i ↦ P.not_splits_c hM i)⟩
  change (extFamily _ _ _ _).dim = κ
  rw [dim_extFamily]
  have hS' : Cardinal.mk S = κ := hS.2
  have hup : (Cardinal.sum fun i : S ↦ (P.cons hM i).dim) ≤ κ :=
    calc (Cardinal.sum fun i : S ↦ (P.cons hM i).dim)
        ≤ Cardinal.sum fun _ : S ↦ D := Cardinal.sum_le_sum _ _ fun i ↦ P.dim_le _
      _ = κ * D := by rw [Cardinal.sum_const', hS']
      _ ≤ κ * κ := mul_le_mul_right hDκ κ
      _ = κ := Cardinal.mul_eq_self hκ
  have hlow : κ ≤ Cardinal.sum fun i : S ↦ (P.cons hM i).dim :=
    calc κ = Cardinal.sum fun _ : S ↦ (1 : Cardinal) := by rw [Cardinal.sum_const', hS', mul_one]
      _ ≤ _ := Cardinal.sum_le_sum _ _ fun i ↦ one_le_dim (P.brick _)
  refine le_antisymm ((add_le_add ((P.dim_le _).trans hDκ) hup).trans (Cardinal.add_eq_self hκ).le)
    (hlow.trans le_add_self)

variable (k) in
/-- The iterated exponentials `ℶ_n(|k|)`: `b 0 = |k|`, `b (n + 1) = 2 ^ b n`. -/
noncomputable def bethK : ℕ → Cardinal.{u}
  | 0 => Cardinal.mk k
  | n + 1 => 2 ^ bethK n

lemma aleph0_le_bethK : ∀ n, Cardinal.aleph0 ≤ bethK k n
  | 0 => Cardinal.infinite_iff.1 inferInstance
  | n + 1 => (aleph0_le_bethK n).trans (Cardinal.cantor _).le

lemma bethK_le_succ (n : ℕ) : bethK k n ≤ bethK k (n + 1) := (Cardinal.cantor _).le

variable (k) in
/-- The pools along the iterated exponentials. -/
noncomputable def pools : ∀ n, Pool k (bethK k n) (bethK k (n + 1))
  | 0 => basePool
  | n + 1 => (pools n).step ((aleph0_le_bethK n).trans (bethK_le_succ n)) (bethK_le_succ n)

/-- Göbel–Simson bricks for every dimension `|k| ≤ κ < ℶ_ω(|k|)`. -/
theorem exists_brick_of_le_bethK (κ : Cardinal.{u}) (hk : Cardinal.mk k ≤ κ) (n : ℕ)
    (hn : κ ≤ bethK k n) : ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  classical
  have hex : ∃ m, κ ≤ bethK k (m + 1) := ⟨n, hn.trans (bethK_le_succ n)⟩
  let m := Nat.find hex
  have hm : κ ≤ bethK k (m + 1) := Nat.find_spec hex
  have hκ : Cardinal.aleph0 ≤ κ := (Cardinal.infinite_iff.1 inferInstance).trans hk
  refine (pools k m).exists_brick κ hκ ?_ hm
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; exact hk
  · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have := Nat.find_min hex (show m' < m by omega)
    rw [hm']
    exact (not_le.1 this).le

end Bricks

/-- The part of Göbel–Simson Corollary 1.3 still needed: Kronecker bricks of
every dimension `κ ≥ ℶ_ω(|k|)`, that is `κ > ℶ_n(|k|)` for all `n`. -/
def KroneckerBricksBeyond : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (κ : Cardinal.{u}), (∀ n, Bricks.bethK k n < κ) →
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T

/-- The large case of Göbel–Simson Corollary 1.3 from the case beyond `ℶ_ω(|k|)`. -/
theorem kroneckerBricksLarge_of_beyond (H : KroneckerBricksBeyond.{u}) :
    KroneckerBricksLarge.{u} := by
  intro k _ _ κ hκ
  by_cases h : ∃ n, κ ≤ Bricks.bethK k n
  · obtain ⟨n, hn⟩ := h
    exact Bricks.exists_brick_of_le_bethK κ hκ.le n hn
  · push Not at h
    exact H k κ h

end LargeIndecomposable
