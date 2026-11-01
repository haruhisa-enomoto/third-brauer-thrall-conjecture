module

public import LargeIndecomposable.Modules.SplitBasic.SplitBasicAlgebras
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Corner bimodules and their radical layers

For a split basic algebra `B` with idempotents `e_x`, this file studies the
corner `e_x B e_y` as a bimodule over the corner algebras `e_x B e_x` and
`e_y B e_y` (note v2, Section 4):

* `SplitBasicData.IsBimod x y U`: `U ⊆ e_x B e_y` is a subbimodule;
* `SplitBasicData.layer x y`: the radical layers
  `D₀ = e_x B e_y`, `D_{i+1} = (e_x J e_x) D_i + D_i (e_y J e_y)`;
* `SplitBasicData.eq_layer_of_isLow`: if every layer `D_i / D_{i+1}` has
  dimension at most one, every subbimodule is one of the `D_i`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u v w

section Low

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

/-- `V` lies in `k v + W` for some `v`: the layer `V/(V ∩ W)` has dimension at most one. -/
def IsLow (V W : Submodule k M) : Prop := ∃ v : M, V ≤ Submodule.span k {v} ⊔ W

/-- Two elements of `V` independent modulo `W`. -/
def IsPair (V W : Submodule k M) (l₁ l₂ : M) : Prop :=
  l₁ ∈ V ∧ l₂ ∈ V ∧ ∀ a b : k, a • l₁ + b • l₂ ∈ W → a = 0 ∧ b = 0

lemma le_sup_of_isLow {U V W : Submodule k M} (hV : IsLow V W) (hUV : U ≤ V)
    (hUW : ¬ U ≤ W) : V ≤ U ⊔ W := by
  obtain ⟨v, hv⟩ := hV
  obtain ⟨u, huU, huW⟩ := IsConcreteLE.not_le_iff_exists.1 hUW
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.1 (hv (hUV huU))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hp
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hpw
    exact huW (hpw ▸ hw)
  have hvU : v ∈ U ⊔ W := by
    have : v = c⁻¹ • u + c⁻¹ • (-w) := by
      rw [← smul_add, ← hpw, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.add_mem_sup (U.smul_mem _ huU) (W.smul_mem _ (W.neg_mem hw))
  refine hv.trans (sup_le ?_ le_sup_right)
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact hvU

lemma not_isPair_of_isLow {V W : Submodule k M} (hV : IsLow V W) (l₁ l₂ : M) :
    ¬ IsPair V W l₁ l₂ := by
  rintro ⟨h₁, h₂, h⟩
  obtain ⟨v, hv⟩ := hV
  obtain ⟨p₁, hp₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.1 (hv h₁)
  obtain ⟨p₂, hp₂, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 (hv h₂)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hp₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hp₂
  have key : b • (a • v + w₁) + (-a) • (b • v + w₂) ∈ W := by
    have : b • (a • v + w₁) + (-a) • (b • v + w₂) = b • w₁ + (-a) • w₂ := by
      module
    rw [this]
    exact W.add_mem (W.smul_mem _ hw₁) (W.smul_mem _ hw₂)
  obtain ⟨rfl, ha⟩ := h _ _ key
  rw [neg_eq_zero] at ha
  subst ha
  have : (1 : k) • ((0 : k) • v + w₁) + (0 : k) • ((0 : k) • v + w₂) ∈ W := by
    simpa using hw₁
  exact one_ne_zero (h _ _ this).1

lemma isLow_or_isPair (V W : Submodule k M) : IsLow V W ∨ ∃ l₁ l₂, IsPair V W l₁ l₂ := by
  by_cases hlow : IsLow V W
  · exact Or.inl hlow
  right
  obtain ⟨l₁, h₁V, h₁W⟩ := IsConcreteLE.not_le_iff_exists.1 fun h => hlow ⟨0, h⟩
  obtain ⟨l₂, h₂V, h₂W⟩ := IsConcreteLE.not_le_iff_exists.1 fun h => hlow ⟨l₁, h⟩
  refine ⟨l₁, l₂, h₁V, h₂V, fun a b hab => ?_⟩
  have hb : b = 0 := by
    by_contra hb
    apply h₂W
    have : l₂ = (-(b⁻¹ * a)) • l₁ + b⁻¹ • (a • l₁ + b • l₂) := by
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul, neg_smul, mul_smul]
      abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      (Submodule.smul_mem _ _ hab)
  subst hb
  refine ⟨?_, rfl⟩
  by_contra ha
  apply h₁W
  rw [Submodule.span_singleton_eq_bot.2 rfl, bot_sup_eq]
  rw [zero_smul, add_zero] at hab
  simpa [smul_smul, inv_mul_cancel₀ ha] using W.smul_mem a⁻¹ hab

end Low

/-- The lattice of two-sided ideals of `B` is distributive. -/
def IsDistribIdeals (B : Type v) [Ring B] : Prop :=
  ∀ I J K : TwoSidedIdeal B, I ⊓ (J ⊔ K) = I ⊓ J ⊔ I ⊓ K

namespace SplitBasicData

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B] {ι : Type w} [Fintype ι]
  (S : SplitBasicData k B ι)

/-- The corner `e_x V e_y = {b ∈ V | e_x b e_y = b}` of a subspace `V`. -/
def corner (x y : ι) (V : Submodule k B) : Submodule k B where
  carrier := {b | b ∈ V ∧ S.e x * b * S.e y = b}
  add_mem' ha hb := ⟨V.add_mem ha.1 hb.1, by rw [mul_add, add_mul, ha.2, hb.2]⟩
  zero_mem' := ⟨V.zero_mem, by simp⟩
  smul_mem' c b hb := ⟨V.smul_mem c hb.1, by rw [mul_smul_comm, smul_mul_assoc, hb.2]⟩

variable {S}

lemma e_mul_of_corner {x y : ι} {b : B} (h : S.e x * b * S.e y = b) : S.e x * b = b := by
  calc S.e x * b = S.e x * (S.e x * b * S.e y) := by rw [h]
    _ = S.e x * b * S.e y := by rw [← mul_assoc, ← mul_assoc, S.e_mul_e]
    _ = b := h

lemma mul_e_of_corner {x y : ι} {b : B} (h : S.e x * b * S.e y = b) : b * S.e y = b := by
  calc b * S.e y = S.e x * b * S.e y * S.e y := by rw [h]
    _ = S.e x * b * S.e y := by rw [mul_assoc, S.e_mul_e]
    _ = b := h

lemma corner_of_mul {x y : ι} {b : B} (hl : S.e x * b = b) (hr : b * S.e y = b) :
    S.e x * b * S.e y = b := by
  rw [hl, hr]

lemma mem_corner {x y : ι} {V : Submodule k B} {b : B} :
    b ∈ S.corner x y V ↔ b ∈ V ∧ S.e x * b * S.e y = b := Iff.rfl

variable (S)

/-- The radical `e_x J e_x` of the corner algebra `e_x B e_x`. -/
abbrev radCorner (x : ι) : Submodule k B := S.corner x x ((Ring.jacobson B).restrictScalars k)

/-- The corner `e_x I e_y` of a two-sided ideal. -/
abbrev cornerIdeal (x y : ι) (I : TwoSidedIdeal B) : Submodule k B :=
  S.corner x y (I.asIdeal.restrictScalars k)

lemma mem_radCorner {x : ι} {b : B} :
    b ∈ S.radCorner x ↔ b ∈ Ring.jacobson B ∧ S.e x * b * S.e x = b := Iff.rfl

lemma mem_cornerIdeal {x y : ι} {I : TwoSidedIdeal B} {b : B} :
    b ∈ S.cornerIdeal x y I ↔ b ∈ I ∧ S.e x * b * S.e y = b := by
  simp [cornerIdeal, mem_corner]

lemma sandwich_mem_radCorner (x : ι) {b : B} (hb : b ∈ Ring.jacobson B) :
    S.e x * b * S.e x ∈ S.radCorner x :=
  ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hb), S.sandwich_sandwich x x b⟩

/-- `U ⊆ e_x B e_y` is a subbimodule over `e_x B e_x` and `e_y B e_y`. -/
structure IsBimod (x y : ι) (U : Submodule k B) : Prop where
  corner : ∀ u ∈ U, S.e x * u * S.e y = u
  left : ∀ a, ∀ u ∈ U, S.e x * a * u ∈ U
  right : ∀ a, ∀ u ∈ U, u * a * S.e y ∈ U

variable {S}

namespace IsBimod

variable {x y : ι} {U U' : Submodule k B}

lemma e_mul (h : S.IsBimod x y U) {u : B} (hu : u ∈ U) : S.e x * u = u :=
  e_mul_of_corner (h.corner u hu)

lemma mul_e (h : S.IsBimod x y U) {u : B} (hu : u ∈ U) : u * S.e y = u :=
  mul_e_of_corner (h.corner u hu)

lemma radCorner_mul_le (h : S.IsBimod x y U) : S.radCorner x * U ≤ U :=
  Submodule.mul_le.2 fun m hm u hu => by
    simpa [e_mul_of_corner hm.2] using h.left m u hu

lemma mul_radCorner_le (h : S.IsBimod x y U) : U * S.radCorner y ≤ U :=
  Submodule.mul_le.2 fun u hu m hm => by
    simpa [mul_assoc, mul_e_of_corner hm.2] using h.right m u hu

lemma sup (h : S.IsBimod x y U) (h' : S.IsBimod x y U') : S.IsBimod x y (U ⊔ U') where
  corner z hz := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
    rw [mul_add, add_mul, h.corner a ha, h'.corner b hb]
  left c z hz := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
    rw [mul_add]
    exact Submodule.add_mem_sup (h.left c a ha) (h'.left c b hb)
  right c z hz := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
    rw [add_mul, add_mul]
    exact Submodule.add_mem_sup (h.right c a ha) (h'.right c b hb)

lemma radCorner_mul (h : S.IsBimod x y U) : S.IsBimod x y (S.radCorner x * U) where
  corner z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem m hm u hu => rw [← mul_assoc, e_mul_of_corner hm.2, mul_assoc, h.mul_e hu]
    | add a _ b _ ha hb => rw [mul_add, add_mul, ha, hb]
  left c z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem m hm u hu =>
      have hm' : S.e x * c * m ∈ S.radCorner x := by
        refine ⟨Ideal.mul_mem_left _ _ hm.1, corner_of_mul ?_ ?_⟩
        · rw [← mul_assoc, ← mul_assoc, S.e_mul_e]
        · rw [mul_assoc, mul_e_of_corner hm.2]
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul hm' hu
    | add a _ b _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  right c z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem m hm u hu =>
      rw [mul_assoc, mul_assoc, ← mul_assoc u]
      exact Submodule.mul_mem_mul hm (h.right c u hu)
    | add a _ b _ ha hb => rw [add_mul, add_mul]; exact Submodule.add_mem _ ha hb

lemma mul_radCorner (h : S.IsBimod x y U) : S.IsBimod x y (U * S.radCorner y) where
  corner z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem u hu m hm => rw [← mul_assoc, h.e_mul hu, mul_assoc, mul_e_of_corner hm.2]
    | add a _ b _ ha hb => rw [mul_add, add_mul, ha, hb]
  left c z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem u hu m hm =>
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul (h.left c u hu) hm
    | add a _ b _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  right c z hz := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem u hu m hm =>
      have hm' : m * c * S.e y ∈ S.radCorner y := by
        refine ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hm.1), corner_of_mul ?_ ?_⟩
        · rw [← mul_assoc, ← mul_assoc, e_mul_of_corner hm.2]
        · rw [mul_assoc, S.e_mul_e]
      rw [mul_assoc, mul_assoc, ← mul_assoc m]
      exact Submodule.mul_mem_mul hu hm'
    | add a _ b _ ha hb => rw [add_mul, add_mul]; exact Submodule.add_mem _ ha hb

end IsBimod

variable (S)

lemma isBimod_cornerIdeal (x y : ι) (I : TwoSidedIdeal B) : S.IsBimod x y (S.cornerIdeal x y I) where
  corner u hu := ((S.mem_cornerIdeal).1 hu).2
  left c u hu := by
    obtain ⟨hI, hc⟩ := (S.mem_cornerIdeal).1 hu
    refine (S.mem_cornerIdeal).2 ⟨I.mul_mem_left _ _ hI, corner_of_mul ?_ ?_⟩
    · rw [← mul_assoc, ← mul_assoc, S.e_mul_e]
    · rw [mul_assoc, mul_e_of_corner hc]
  right c u hu := by
    obtain ⟨hI, hc⟩ := (S.mem_cornerIdeal).1 hu
    refine (S.mem_cornerIdeal).2 ⟨I.mul_mem_right _ _ (I.mul_mem_right _ _ hI),
      corner_of_mul ?_ ?_⟩
    · rw [← mul_assoc, ← mul_assoc, e_mul_of_corner hc]
    · rw [mul_assoc, S.e_mul_e]

/-- One step `V ↦ (e_x J e_x) V + V (e_y J e_y)` of the radical filtration. -/
def layerStep (x y : ι) (V : Submodule k B) : Submodule k B :=
  S.radCorner x * V ⊔ V * S.radCorner y

/-- The radical layers `D₀ = e_x B e_y`, `D_{i+1} = (e_x J e_x) D_i + D_i (e_y J e_y)`. -/
def layer (x y : ι) (n : ℕ) : Submodule k B := (S.layerStep x y)^[n] (S.corner x y ⊤)

lemma layer_zero (x y : ι) : S.layer x y 0 = S.corner x y ⊤ := rfl

lemma layer_succ (x y : ι) (n : ℕ) :
    S.layer x y (n + 1) = S.radCorner x * S.layer x y n ⊔ S.layer x y n * S.radCorner y :=
  Function.iterate_succ_apply' _ _ _

lemma isBimod_layer (x y : ι) (n : ℕ) : S.IsBimod x y (S.layer x y n) := by
  induction n with
  | zero => simpa [cornerIdeal, corner, layer_zero] using S.isBimod_cornerIdeal x y ⊤
  | succ n ih =>
    rw [layer_succ]
    exact ih.radCorner_mul.sup ih.mul_radCorner

lemma layer_succ_le (x y : ι) (n : ℕ) : S.layer x y (n + 1) ≤ S.layer x y n :=
  (S.layer_succ x y n).le.trans <| sup_le (S.isBimod_layer x y n).radCorner_mul_le (S.isBimod_layer x y n).mul_radCorner_le

lemma layer_antitone (x y : ι) : Antitone (S.layer x y) :=
  antitone_nat_of_succ_le (S.layer_succ_le x y)

lemma cornerIdeal_le_layer_zero (x y : ι) (I : TwoSidedIdeal B) :
    S.cornerIdeal x y I ≤ S.layer x y 0 :=
  fun _ hb => ⟨trivial, hb.2⟩

lemma layer_le_pow (x y : ι) (n : ℕ) :
    S.layer x y n ≤ ((Ring.jacobson B) ^ n).restrictScalars k := by
  induction n with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top]; exact le_top
  | succ n ih =>
    rw [layer_succ]
    refine sup_le (Submodule.mul_le.2 fun m hm d hd => ?_) (Submodule.mul_le.2 fun d hd m hm => ?_)
    · rw [Submodule.restrictScalars_mem, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul hm.1 (ih hd)
    · rw [Submodule.restrictScalars_mem, Submodule.pow_succ]
      exact Ideal.mul_mem_mul (ih hd) hm.1

lemma exists_layer_eq_bot [FiniteDimensional k B] (x y : ι) : ∃ N, S.layer x y N = ⊥ := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := B)
  refine ⟨N, eq_bot_iff.2 ((S.layer_le_pow x y N).trans ?_)⟩
  rw [hN]
  intro b hb
  simpa using hb

/-- If all layers have dimension at most one, every subbimodule of `e_x B e_y` is a layer. -/
lemma eq_layer_of_isLow {x y : ι} (hlow : ∀ n, IsLow (S.layer x y n) (S.layer x y (n + 1)))
    {N : ℕ} (hN : S.layer x y N = ⊥) {U : Submodule k B} (hU : S.IsBimod x y U)
    (hU0 : U ≤ S.layer x y 0) : ∃ n, U = S.layer x y n := by
  classical
  by_cases hUN : U ≤ S.layer x y N
  · exact ⟨N, le_antisymm hUN (hN ▸ bot_le)⟩
  have hex : ∃ n, ¬ U ≤ S.layer x y n := ⟨N, hUN⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this hU0
  have hUi : U ≤ S.layer x y (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  have hUi' : ¬ U ≤ S.layer x y (Nat.find hex - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    exact Nat.find_spec hex
  generalize Nat.find hex - 1 = i at hUi hUi'
  refine ⟨i, le_antisymm hUi ?_⟩
  -- `D_j ≤ U + D_{j+1}` for all `j ≥ i`
  have step : ∀ j, i ≤ j → S.layer x y j ≤ U ⊔ S.layer x y (j + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_sup_of_isLow (hlow i) hUi hUi'
    | succ j _ ih =>
      rw [S.layer_succ x y j, S.layer_succ x y (j + 1)]
      refine sup_le ?_ ?_
      · refine (Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul ha (ih hb)).trans ?_
        rw [Submodule.mul_sup]
        exact sup_le_sup hU.radCorner_mul_le le_sup_left
      · refine (Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul (ih ha) hb).trans ?_
        rw [Submodule.sup_mul]
        exact sup_le_sup hU.mul_radCorner_le le_sup_right
  have chain : ∀ n, S.layer x y i ≤ U ⊔ S.layer x y (i + 1 + n) := by
    intro n
    induction n with
    | zero => exact step i le_rfl
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ((step _ (by omega)).trans ?_))
      rw [← add_assoc]
  have := chain N
  rw [eq_bot_iff.2 ((S.layer_antitone x y (by omega : N ≤ i + 1 + N)).trans hN.le),
    sup_bot_eq] at this
  exact this

end SplitBasicData

end LargeIndecomposable
