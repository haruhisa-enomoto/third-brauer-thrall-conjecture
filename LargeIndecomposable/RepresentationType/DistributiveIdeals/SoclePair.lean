module

public import LargeIndecomposable.RepresentationType.DistributiveIdeals.Layers
public import LargeIndecomposable.RepresentationEmbeddings.QuotientConstruction.Quotient

/-!
# A non-distributive algebra has a quotient with a socle pair

The non-distributive case behind alternative (1) of the manuscript's Theorem
`thm:finite-input` (Bongartz, Corollary 2), by the elementary proof of note v2,
Section 4: if the lattice of two-sided ideals of a split basic algebra `B` is not
distributive, there are a two-sided ideal `K ⊆ J` and `QuotientData` on `B/K`
whose idempotents are the images of `e_x, e_y`
(`SplitBasicData.exists_quotientData`).

The proof follows the note: a non-distributive ideal lattice has a corner
`e_x B e_y` whose subbimodules are not totally ordered
(`SplitBasicData.isDistribIdeals_of_chain`); hence some radical layer
`D_i / D_{i+1}` has two independent elements `s, t` (`exists_isPair`).
Instead of the note's `K = JH + HJ` with `H = B D_i B`, we kill the largest
ideal `K ⊆ J` with `e_x B K B e_y ⊆ D_{i+1}` (`socleKernel`). It contains `jl`
and `lj` for `l ∈ D_i`, `j ∈ J`, which is all that is needed; we do not show
`K ⊆ J²`, only `K ⊆ J`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u v w

namespace SplitBasicData

section Distrib

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B] {ι : Type w} [Fintype ι]
  (S : SplitBasicData k B ι)

/-- A two-sided ideal is the sum of its corners. -/
lemma mem_iff_corners (I : TwoSidedIdeal B) (b : B) :
    b ∈ I ↔ ∀ x y, S.e x * b * S.e y ∈ I := by
  refine ⟨fun h x y => I.mul_mem_right _ _ (I.mul_mem_left _ _ h), fun h => ?_⟩
  rw [← S.sum_corners b]
  exact sum_mem fun x _ => sum_mem fun y _ => h x y

/-- If, for every corner, the corners of any two ideals are comparable, the ideal
lattice is distributive. -/
lemma isDistribIdeals_of_chain (h : ∀ (x y : ι) (I₁ I₂ : TwoSidedIdeal B),
    S.cornerIdeal x y I₁ ≤ S.cornerIdeal x y I₂ ∨ S.cornerIdeal x y I₂ ≤ S.cornerIdeal x y I₁) :
    IsDistribIdeals B := by
  intro I J₁ J₂
  refine le_antisymm (fun b hb => ?_)
    (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  rw [TwoSidedIdeal.mem_inf] at hb
  rw [S.mem_iff_corners]
  intro x y
  have hcI : S.e x * b * S.e y ∈ I := I.mul_mem_right _ _ (I.mul_mem_left _ _ hb.1)
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := TwoSidedIdeal.mem_sup.1 hb.2
  have hc : S.e x * b * S.e y = S.e x * j₁ * S.e y + S.e x * j₂ * S.e y := by
    rw [← hj, mul_add, add_mul]
  have h₁ : S.e x * j₁ * S.e y ∈ S.cornerIdeal x y J₁ := (S.mem_cornerIdeal).2
    ⟨J₁.mul_mem_right _ _ (J₁.mul_mem_left _ _ hj₁), S.sandwich_sandwich x y j₁⟩
  have h₂ : S.e x * j₂ * S.e y ∈ S.cornerIdeal x y J₂ := (S.mem_cornerIdeal).2
    ⟨J₂.mul_mem_right _ _ (J₂.mul_mem_left _ _ hj₂), S.sandwich_sandwich x y j₂⟩
  rcases h x y J₁ J₂ with h12 | h21
  · have : S.e x * b * S.e y ∈ J₂ := hc ▸ J₂.add_mem ((S.mem_cornerIdeal).1 (h12 h₁)).1
      ((S.mem_cornerIdeal).1 h₂).1
    exact TwoSidedIdeal.mem_sup_right ((TwoSidedIdeal.mem_inf _).2 ⟨hcI, this⟩)
  · have : S.e x * b * S.e y ∈ J₁ := hc ▸ J₁.add_mem ((S.mem_cornerIdeal).1 h₁).1
      ((S.mem_cornerIdeal).1 (h21 h₂)).1
    exact TwoSidedIdeal.mem_sup_left ((TwoSidedIdeal.mem_inf _).2 ⟨hcI, this⟩)

/-- A non-distributive split basic algebra has a radical layer `D_i/D_{i+1}` of some
corner `e_x B e_y` containing two independent elements. -/
theorem exists_isPair [FiniteDimensional k B] (hnd : ¬ IsDistribIdeals B) :
    ∃ (x y : ι) (n : ℕ) (l₁ l₂ : B), IsPair (S.layer x y n) (S.layer x y (n + 1)) l₁ l₂ := by
  by_contra! hpair
  have hlow : ∀ x y n, IsLow (S.layer x y n) (S.layer x y (n + 1)) := fun x y n =>
    (isLow_or_isPair _ _).resolve_right fun ⟨l₁, l₂, h⟩ => hpair x y n l₁ l₂ h
  refine hnd (S.isDistribIdeals_of_chain fun x y I₁ I₂ => ?_)
  obtain ⟨N, hN⟩ := S.exists_layer_eq_bot x y
  obtain ⟨n₁, h₁⟩ := S.eq_layer_of_isLow (hlow x y) hN (S.isBimod_cornerIdeal x y I₁)
    (S.cornerIdeal_le_layer_zero x y I₁)
  obtain ⟨n₂, h₂⟩ := S.eq_layer_of_isLow (hlow x y) hN (S.isBimod_cornerIdeal x y I₂)
    (S.cornerIdeal_le_layer_zero x y I₂)
  rw [h₁, h₂]
  rcases le_total n₁ n₂ with h | h
  · exact Or.inr (S.layer_antitone x y h)
  · exact Or.inl (S.layer_antitone x y h)

/-- An independent pair in a radical layer lies in `J`: the zeroth layer of a diagonal
corner `e_x B e_x = k e_x + e_x J e_x` has dimension at most one. -/
lemma mem_rad_of_isPair {x y : ι} {n : ℕ} {l₁ l₂ : B}
    (hp : IsPair (S.layer x y n) (S.layer x y (n + 1)) l₁ l₂) :
    l₁ ∈ Ring.jacobson B ∧ l₂ ∈ Ring.jacobson B := by
  suffices hle : S.layer x y n ≤ (Ring.jacobson B).restrictScalars k from ⟨hle hp.1, hle hp.2.1⟩
  cases n with
  | succ n =>
    rw [layer_succ]
    exact sup_le (Submodule.mul_le.2 fun m hm d _ => Ideal.mul_mem_right _ _ hm.1)
      (Submodule.mul_le.2 fun d _ m hm => Ideal.mul_mem_left _ _ hm.1)
  | zero =>
    by_cases hxy : x = y
    · subst hxy
      refine absurd hp (not_isPair_of_isLow ⟨S.e x, fun u hu => ?_⟩ l₁ l₂)
      have hu' : S.e x * u * S.e x = u := hu.2
      obtain ⟨c, hc⟩ := S.corner_diag x u
      rw [hu'] at hc
      have hj : u - c • S.e x ∈ S.radCorner x := by
        refine ⟨hc, ?_⟩
        rw [mul_sub, sub_mul, hu', mul_smul_comm, smul_mul_assoc, S.e_mul_e, S.e_mul_e]
      have hex : S.e x ∈ S.layer x x 0 := ⟨trivial, by rw [S.e_mul_e, S.e_mul_e]⟩
      have hj' : u - c • S.e x ∈ S.layer x x 1 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, layer_succ]
        refine Submodule.mem_sup_left ?_
        rw [← mul_e_of_corner hj.2]
        exact Submodule.mul_mem_mul hj hex
      rw [show u = c • S.e x + (u - c • S.e x) by abel]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hj'
    · intro u hu
      rw [← hu.2]
      exact S.corner_offdiag x y hxy u

end Distrib

section Kernel

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B] {ι : Type w} [Fintype ι]
  (S : SplitBasicData k B ι)

/-- The largest two-sided ideal `K ⊆ J` with `e_x B K B e_y ⊆ W`. -/
def socleKernel (x y : ι) (W : Submodule k B) : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' {b | b ∈ Ring.jacobson B ∧ ∀ a c, S.e x * (a * b * c) * S.e y ∈ W}
    ⟨zero_mem _, fun a c => by simp⟩
    (fun {b₁ b₂} h₁ h₂ => ⟨add_mem h₁.1 h₂.1, fun a c => by
      simpa only [mul_add, add_mul] using W.add_mem (h₁.2 a c) (h₂.2 a c)⟩)
    (fun {b} h => ⟨neg_mem h.1, fun a c => by
      simpa only [mul_neg, neg_mul] using W.neg_mem (h.2 a c)⟩)
    (fun {r b} h => ⟨Ideal.mul_mem_left _ r h.1, fun a c => by
      simpa only [mul_assoc] using h.2 (a * r) c⟩)
    (fun {b r} h => ⟨Ideal.mul_mem_right _ _ h.1, fun a c => by
      simpa only [mul_assoc] using h.2 a (r * c)⟩)

lemma mem_socleKernel {x y : ι} {W : Submodule k B} {b : B} :
    b ∈ (S.socleKernel x y W).asIdeal ↔
      b ∈ Ring.jacobson B ∧ ∀ a c, S.e x * (a * b * c) * S.e y ∈ W := by
  rw [TwoSidedIdeal.mem_asIdeal, socleKernel, TwoSidedIdeal.mem_mk']
  rfl

lemma socleKernel_le (x y : ι) (W : Submodule k B) :
    (S.socleKernel x y W).asIdeal ≤ Ring.jacobson B :=
  fun _ hb => ((S.mem_socleKernel).1 hb).1

variable {S}

lemma mem_socleKernel_mul_left {x y : ι} {n : ℕ} {l j : B} (hl : l ∈ S.layer x y n)
    (hj : j ∈ Ring.jacobson B) (hlJ : l ∈ Ring.jacobson B) :
    j * l ∈ (S.socleKernel x y (S.layer x y (n + 1))).asIdeal := by
  refine (S.mem_socleKernel).2 ⟨Ideal.mul_mem_left _ _ hlJ, fun a c => ?_⟩
  have hl' : ∀ w, S.e x * (l * w) = l * w := fun w => by
    rw [← mul_assoc, (S.isBimod_layer x y n).e_mul hl]
  have hm : S.e x * (a * j) * S.e x * l ∈ S.layer x y (n + 1) := by
    rw [layer_succ]
    exact Submodule.mem_sup_left (Submodule.mul_mem_mul
      (S.sandwich_mem_radCorner x (Ideal.mul_mem_left _ _ hj)) hl)
  have := (S.isBimod_layer x y (n + 1)).right c _ hm
  simpa only [mul_assoc, hl'] using this

lemma mem_socleKernel_mul_right {x y : ι} {n : ℕ} {l j : B} (hl : l ∈ S.layer x y n)
    (hj : j ∈ Ring.jacobson B) :
    l * j ∈ (S.socleKernel x y (S.layer x y (n + 1))).asIdeal := by
  refine (S.mem_socleKernel).2 ⟨Ideal.mul_mem_left _ _ hj, fun a c => ?_⟩
  have hl' : ∀ w, l * (S.e y * w) = l * w := fun w => by
    rw [← mul_assoc, (S.isBimod_layer x y n).mul_e hl]
  have hm : l * (S.e y * (j * c) * S.e y) ∈ S.layer x y (n + 1) := by
    rw [layer_succ]
    exact Submodule.mem_sup_right (Submodule.mul_mem_mul hl
      (S.sandwich_mem_radCorner y (Ideal.mul_mem_right _ _ hj)))
  have := (S.isBimod_layer x y (n + 1)).left a _ hm
  simpa only [mul_assoc, hl'] using this

variable (S)

/-- **Note v2, Section 4.** If the lattice of two-sided ideals of a split basic
algebra `B` is not distributive, there are `x, y` and a two-sided ideal `K ⊆ J`
such that `B/K` carries `QuotientData` (Setting 3.2) with idempotents the images
of `e_x, e_y`. By `SplitBasicData.quotient`, `B/K` is again split basic with the
images of the `e`'s, and its radical is the image of `J`
(`SplitBasicData.mem_jacobson_quotient_iff`). -/
theorem exists_quotientData [FiniteDimensional k B] (hnd : ¬ IsDistribIdeals B) :
    ∃ (x y : ι) (K : TwoSidedIdeal B), K.asIdeal ≤ Ring.jacobson B ∧
      ∃ Q : QuotientData k (B ⧸ K.asIdeal),
        Q.ex = Ideal.Quotient.mk K.asIdeal (S.e x) ∧ Q.ey = Ideal.Quotient.mk K.asIdeal (S.e y) := by
  obtain ⟨x, y, n, l₁, l₂, hp⟩ := S.exists_isPair hnd
  obtain ⟨hl₁J, hl₂J⟩ := S.mem_rad_of_isPair hp
  obtain ⟨hl₁, hl₂, hind⟩ := hp
  set K := S.socleKernel x y (S.layer x y (n + 1))
  have hK : K.asIdeal ≤ Ring.jacobson B := S.socleKernel_le x y _
  have hc := (S.isBimod_layer x y n).corner
  let π := Ideal.Quotient.mk K.asIdeal
  have hcorner : ∀ l ∈ S.layer x y n, π (S.e x) * π l * π (S.e y) = π l := fun l hl => by
    rw [← map_mul, ← map_mul, hc l hl]
  have hJ : ∀ z ∈ Ring.jacobson (B ⧸ K.asIdeal), ∃ j ∈ Ring.jacobson B, π j = z :=
    fun z hz => (mem_jacobson_quotient_iff K hK z).1 hz
  refine ⟨x, y, K, hK,
    { ex := π (S.e x)
      ey := π (S.e y)
      s := π l₁
      t := π l₂
      ex_idem := (S.idem x).map π
      ey_idem := (S.idem y).map π
      s_mem := ⟨mk_mem_jacobson K hK hl₁J, hcorner l₁ hl₁⟩
      t_mem := ⟨mk_mem_jacobson K hK hl₂J, hcorner l₂ hl₂⟩
      linearIndependent := ?_
      J_mul_s := ?_
      J_mul_t := ?_
      s_mul_J := ?_
      t_mul_J := ?_ }, rfl, rfl⟩
  · refine LinearIndependent.pair_iff.2 fun a b hab => hind a b ?_
    rw [← mk_smul, ← mk_smul, ← map_add, Ideal.Quotient.eq_zero_iff_mem,
      S.mem_socleKernel] at hab
    have := hab.2 1 1
    rwa [one_mul, mul_one, (S.layer x y n).add_mem ((S.layer x y n).smul_mem a hl₁)
      ((S.layer x y n).smul_mem b hl₂) |> hc _] at this
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := hJ z hz
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_socleKernel_mul_left hl₁ hj hl₁J
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := hJ z hz
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_socleKernel_mul_left hl₂ hj hl₂J
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := hJ z hz
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_socleKernel_mul_right hl₁ hj
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := hJ z hz
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_socleKernel_mul_right hl₂ hj

end Kernel

end SplitBasicData

end LargeIndecomposable
