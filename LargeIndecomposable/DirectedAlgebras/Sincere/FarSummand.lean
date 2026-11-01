module

public import LargeIndecomposable.DirectedAlgebras.Sincere.PolyBuild

/-!
# Summands far from a set

Let `U` be a sincere indecomposable module of a directed algebra and `H` a nonempty set of points.
On the convex set `E` of points with no path to or from `H`, the truncation of `U` has a summand
through every point `v` far from `H`, and that summand reaches near `H` (`exists_far_summand`). So
its support is large. The size of balls in the underlying graph is controlled by `card_layerF_le`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module Classical

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A}

variable (D) in
/-- Balls in the underlying graph. -/
def layerF (H : Finset D.ι) : ℕ → Finset D.ι
  | 0 => H
  | n + 1 => (layerF H n).biUnion fun a ↦ insert a (Finset.univ.filter (D.gr.Adj a))

lemma layerF_succ_mono (H : Finset D.ι) (n : ℕ) : D.layerF H n ⊆ D.layerF H (n + 1) := fun a ha ↦
  Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_insert_self _ _⟩

lemma layerF_mono (H : Finset D.ι) {m n : ℕ} (h : m ≤ n) : D.layerF H m ⊆ D.layerF H n := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih => exact ih.trans (layerF_succ_mono H n)

lemma layerF_adj {H : Finset D.ι} {n : ℕ} {a b : D.ι} (ha : a ∈ D.layerF H n) (h : D.gr.Adj a b) :
    b ∈ D.layerF H (n + 1) :=
  Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)⟩

lemma exists_of_mem_layerF_succ {H : Finset D.ι} {n : ℕ} {b : D.ι}
    (h : b ∈ D.layerF H (n + 1)) (h' : b ∉ D.layerF H n) : ∃ a ∈ D.layerF H n, D.gr.Adj a b := by
  obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.1 h
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact absurd ha h'
  · exact ⟨a, ha, (Finset.mem_filter.1 hb).2⟩

/-- **The size of balls.** -/
theorem card_layerF_le {Δ : ℕ} (hΔ : ∀ a, (Finset.univ.filter (D.gr.Adj a)).card ≤ Δ)
    (H : Finset D.ι) (n : ℕ) : (D.layerF H n).card ≤ H.card * (Δ + 1) ^ n := by
  induction n with
  | zero => simp [layerF]
  | succ n ih =>
    have h1 : (D.layerF H (n + 1)).card ≤ (D.layerF H n).card * (Δ + 1) := by
      refine Finset.card_biUnion_le_card_mul _ _ _ fun a _ ↦ ?_
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hΔ a))
    calc _ ≤ _ := h1
      _ ≤ H.card * (Δ + 1) ^ n * (Δ + 1) := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [pow_succ, mul_assoc]

/-- The points with no path to or from `H`. -/
def farSet (D : DirData k A) (H : Set D.ι) : Set D.ι :=
  {c | (∀ x ∈ H, ¬Relation.ReflTransGen D.Arr x c) ∧ ∀ x ∈ H, ¬Relation.ReflTransGen D.Arr c x}

lemma isConvexSet_farSet (H : Set D.ι) : D.IsConvexSet (D.farSet H) := by
  intro x z c hx hz h1 h2
  exact ⟨fun y hy h ↦ hz.1 y hy (h.trans h2), fun y hy h ↦ hx.2 y hy (h1.trans h)⟩

lemma not_mem_farSet {H : Set D.ι} {x : D.ι} (hx : x ∈ H) : x ∉ D.farSet H := fun h ↦
  h.1 x hx Relation.ReflTransGen.refl

/-- A chain in a directed algebra is a sequence. -/
lemma exists_seq_of_reach {x c : D.ι} (h : Relation.ReflTransGen D.Arr x c) :
    ∃ (r : ℕ) (y : ℕ → D.ι), y 0 = x ∧ y r = c ∧ ∀ i < r, D.Arr (y i) (y (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ ↦ x, rfl, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨r, y, h0, hr, hy⟩ := ih
    refine ⟨r + 1, Function.update y (r + 1) c, ?_, ?_, fun i hi ↦ ?_⟩
    · rw [Function.update_of_ne (by omega), h0]
    · simp
    · rw [Function.update_of_ne (by omega)]
      by_cases hi' : i = r
      · subst hi'
        rw [Function.update_self, hr]
        exact hbc
      · rw [Function.update_of_ne (by omega)]
        exact hy i (by omega)

/-- **A connected graph of bounded degree with many points has a long path.** -/
theorem exists_long_path (hconn : ∀ a b, D.gr.Reachable a b) {Δ : ℕ}
    (hΔ : ∀ a, (Finset.univ.filter (D.gr.Adj a)).card ≤ Δ) (r : ℕ)
    (hcard : (Δ + 1) ^ r < Fintype.card D.ι) :
    ∃ f : ℕ → D.ι, (∀ i < r, D.gr.Adj (f i) (f (i + 1))) ∧
      ∀ i j, i ≤ r → j ≤ r → f i = f j → i = j := by
  have hpos : 0 < Fintype.card D.ι := by omega
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.1 hpos
  let H : Finset D.ι := {v₀}
  have hsz : (D.layerF H r).card < Fintype.card D.ι := by
    refine lt_of_le_of_lt (card_layerF_le hΔ H r) ?_
    simpa [H] using hcard
  obtain ⟨v, hv⟩ : ∃ v, v ∉ D.layerF H r := by
    by_contra hno
    push Not at hno
    have : D.layerF H r = Finset.univ := Finset.eq_univ_iff_forall.2 hno
    rw [this, Finset.card_univ] at hsz
    exact lt_irrefl _ hsz
  obtain ⟨w⟩ := hconn v₀ v
  let p := w.toPath
  have key : ∀ {a b : D.ι} (q : D.gr.Walk a b) (n : ℕ), a ∈ D.layerF H n →
      b ∈ D.layerF H (n + q.length) := by
    intro a b q
    induction q with
    | nil => exact fun n h ↦ h
    | cons hadj _ ih =>
      intro n h
      have := ih (n + 1) (layerF_adj h hadj)
      simpa [SimpleGraph.Walk.length_cons, add_assoc, add_comm 1] using this
  have hlen : r < (p : D.gr.Walk v₀ v).length := by
    by_contra h
    push Not at h
    have h1 := key (p : D.gr.Walk v₀ v) 0 (Finset.mem_singleton_self v₀)
    exact hv (layerF_mono H (by omega) h1)
  refine ⟨(p : D.gr.Walk v₀ v).getVert, fun i hi ↦ ?_, fun i j hi hj hij ↦ ?_⟩
  · exact (p : D.gr.Walk v₀ v).adj_getVert_succ (by omega)
  · exact p.2.getVert_injOn (by simp; omega) (by simp; omega) hij

section Far

variable {U : FDMod k A} (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {M : ℕ}
  (hM : RunB D M) (H : Finset D.ι)

include hT hU hs hM in
/-- Points near `H` include everything comparable with `H`. -/
theorem compl_farSet_subset {c : D.ι} (hc : c ∉ D.farSet (H : Set D.ι)) :
    c ∈ D.layerF H (2 * M) := by
  have hadj : ∀ {a b : D.ι}, D.Arr a b → D.gr.Adj a b := gr_adj_of_arr
  simp only [farSet, Set.mem_setOf_eq, not_and_or, not_forall, not_not] at hc
  rcases hc with ⟨x, hx, h⟩ | ⟨x, hx, h⟩
  · obtain ⟨r, y, h0, hr, hy⟩ := exists_seq_of_reach h
    have hlt := run_lt hT hU hs hM hy
    have key : ∀ i ≤ r, y i ∈ D.layerF H i := by
      intro i
      induction i with
      | zero =>
        intro _
        change y 0 ∈ H
        rw [h0]
        exact hx
      | succ i ih => exact fun hi ↦ layerF_adj (ih (by omega)) (hadj (hy i (by omega)))
    rw [← hr]
    exact layerF_mono H hlt.le (key r le_rfl)
  · obtain ⟨r, y, h0, hr, hy⟩ := exists_seq_of_reach h
    have hlt := run_lt hT hU hs hM hy
    have key : ∀ i ≤ r, y (r - i) ∈ D.layerF H i := by
      intro i
      induction i with
      | zero =>
        intro _
        change y (r - 0) ∈ H
        rw [Nat.sub_zero, hr]
        exact hx
      | succ i ih =>
        intro hi
        have h1 := hy (r - (i + 1)) (by omega)
        have e1 : r - (i + 1) + 1 = r - i := by omega
        rw [e1] at h1
        exact layerF_adj (ih (by omega)) (hadj h1).symm
    have := key r le_rfl
    rw [Nat.sub_self, h0] at this
    exact layerF_mono H hlt.le this

include hT hU hs hM in
/-- **A far point lies on a large summand.** -/
theorem exists_far_summand {x₀ : D.ι} (hx₀ : x₀ ∈ H) {K : ℕ} {v : D.ι}
    (hv : v ∉ D.layerF H (2 * M + K + 1)) :
    ∃ (Y : FDMod k A) (inc : Y →ₗ[A] trunc U (isConvexSet_farSet (D := D) (H : Set D.ι)))
      (pr : trunc U (isConvexSet_farSet (D := D) (H : Set D.ι)) →ₗ[A] Y), IndNT Y ∧
      (∀ y, pr (inc y) = y) ∧ K ≤ (Finset.univ.filter fun c ↦ ∃ y : Y, D.e c • y ≠ 0).card := by
  have hE := isConvexSet_farSet (D := D) (H : Set D.ι)
  set E := D.farSet (H : Set D.ι)
  have hsub : ∀ c, c ∉ E → c ∈ D.layerF H (2 * M) := fun c hc ↦
    compl_farSet_subset hT hU hs hM H hc
  have hvE : v ∈ E := by
    by_contra h
    exact hv (layerF_mono H (by omega) (hsub v h))
  obtain ⟨u, hu⟩ := hs v
  obtain ⟨Y, inc, pr, hY, hr, y, hy⟩ := exists_summand hE hvE hu
  obtain ⟨u₀, hu₀⟩ := hs x₀
  obtain ⟨b, hb, yb, hyb⟩ := exists_bdry_of_summand hE hU.1.1 inc pr hr hY.2 hu₀
    (Or.inl (not_mem_farSet (Finset.mem_coe.2 hx₀)))
  have hb1 : b ∈ D.layerF H (2 * M + 1) := by
    obtain ⟨-, c, hc, hbc⟩ := hb
    have h1 := hsub c hc
    rcases hbc with h | h
    · exact layerF_adj h1 (gr_adj_of_arr h).symm
    · exact layerF_adj h1 (gr_adj_of_arr h)
  -- one new point of the support in every layer
  have hstep : ∀ j, j < K → ∃ c, c ∈ D.layerF H (2 * M + j + 2) ∧ c ∉ D.layerF H (2 * M + j + 1) ∧
      ∃ y : Y, D.e c • y ≠ 0 := by
    intro j hj
    have hbj : b ∈ D.layerF H (2 * M + j + 1) := layerF_mono H (by omega) hb1
    have hvj : v ∉ D.layerF H (2 * M + j + 1) := fun h ↦ hv (layerF_mono H (by omega) h)
    obtain ⟨a, c, ha, hc, w, y', hcase⟩ := exists_cross hY.1 (↑(D.layerF H (2 * M + j + 1)))
      (Finset.mem_coe.2 hbj) hyb (fun h ↦ hvj (Finset.mem_coe.1 h)) hy
    refine ⟨c, ?_, fun h ↦ hc (Finset.mem_coe.2 h), ?_⟩
    · rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact layerF_adj (Finset.mem_coe.1 ha) (gr_adj_of_arr h1)
      · exact layerF_adj (Finset.mem_coe.1 ha) (gr_adj_of_arr h1).symm
    · rcases hcase with ⟨-, h1⟩ | ⟨-, h1⟩
      · refine ⟨(w * D.e a) • y', fun h0 ↦ h1 ?_⟩
        rw [mul_assoc, mul_smul, h0]
      · refine ⟨y', fun h0 ↦ h1 ?_⟩
        rw [mul_smul, h0, smul_zero]
  haveI : Nonempty D.ι := ⟨x₀⟩
  choose! f hf1 hf2 hf3 using hstep
  refine ⟨Y, inc, pr, hY, hr, ?_⟩
  have hinj : Set.InjOn f (↑(Finset.range K) : Set ℕ) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hf2 j hj' (layerF_mono H (by omega) (hij ▸ hf1 i hi'))
    · exact hf2 i hi' (layerF_mono H (by omega) (hij ▸ hf1 j hj'))
  calc K = ((Finset.range K).image f).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card fun c hc ↦ by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf3 j (Finset.mem_range.1 hj)⟩

end Far

/-- The support of a module has at most its dimension. -/
lemma card_supp_le_finrank (Y : FDMod k A) :
    (Finset.univ.filter fun c ↦ ∃ y : Y, D.e c • y ≠ 0).card ≤ finrank k Y := by
  have h1 : finrank k Y = ∑ x, finrank k (eSub Y (D.e x)) := by
    rw [(piEquiv D.e D.idem D.orth D.sum Y).finrank_eq, Module.finrank_pi_fintype]
  rw [h1, Finset.card_filter]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  split_ifs with hc
  · obtain ⟨y, hy⟩ := hc
    have h2 := dimZ_ne_zero (D := D) hy
    have h3 : ((finrank k (eSub Y (D.e c)) : ℕ) : ℤ) ≠ 0 := h2
    omega
  · exact Nat.zero_le _

section Final

variable [IsAlgClosed k] {U : FDMod k A} (hT : ∀ x, x ∈ D.T) (hC : ∀ x y, cartan D y x ≤ 1)
  (hDir : ∀ N : FDMod k A, IndNT N → Directing N) (hU : Directing U) (hs : Sincere D U) {M : ℕ}
  (hM : RunB D M)
include hT hC hDir hU hs hM

/-- **A polygon and a far point give a contradiction.** -/
theorem false_of_far {κ : Type} [Fintype κ] [DecidableEq κ] (P : Poly D κ) (H : Finset D.ι)
    (hH : P.H ⊆ (H : Set D.ι)) {K : ℕ} {v : D.ι} (hv : v ∉ D.layerF H (2 * M + K + 1))
    (hnext : ∀ Y : FDMod k A, IndNT Y → K ≤ (Finset.univ.filter fun c ↦ ∃ y : Y, D.e c • y ≠ 0).card →
      ∃ (κ' : Type) (_ : Fintype κ') (_ : DecidableEq κ') (P' : Poly D κ'),
        ∀ c ∈ P'.H, ∃ y : Y, D.e c • y ≠ 0) : False := by
  have hx₀ : P.a ∈ H := Finset.mem_coe.1 (hH (Or.inl rfl))
  obtain ⟨Y, inc, pr, hY, hr, hcard⟩ := exists_far_summand hT hU hs hM H hx₀ hv
  obtain ⟨κ', _, _, P', hP'⟩ := hnext Y hY hcard
  refine false_of_two_polys hT hC hDir hU hs P P' fun c hc l hl ↦ ?_
  have hlE : l ∈ D.farSet (H : Set D.ι) := by
    by_contra h
    obtain ⟨y, hy⟩ := hP' l hl
    exact hy (e_smul_summand hT hDir hU hs hr h y)
  exact ⟨hlE.1 c (hH hc), hlE.2 c (hH hc)⟩

/-- **Large modules with polygons do not exist.** -/
theorem false_of_large {K Δ h : ℕ} (hΔ : ∀ a, (Finset.univ.filter (D.gr.Adj a)).card ≤ Δ)
    (hcardU : K < finrank k U)
    (hBr : ∀ Y : FDMod k A, IndNT Y → K < finrank k Y →
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (P : Poly D κ),
        (∀ c ∈ P.H, ∃ y : Y, D.e c • y ≠ 0) ∧ (Finset.univ.filter (· ∈ P.H)).card ≤ h)
    (hlarge : h * (Δ + 1) ^ (2 * M + (K + 1) + 1) < Fintype.card D.ι) : False := by
  obtain ⟨κ, _, _, P, -, hcard⟩ := hBr U ⟨hU.1.1, hU.1.2⟩ hcardU
  let H : Finset D.ι := Finset.univ.filter (· ∈ P.H)
  have hsz : (D.layerF H (2 * M + (K + 1) + 1)).card < Fintype.card D.ι := by
    refine lt_of_le_of_lt ((card_layerF_le hΔ H _).trans ?_) hlarge
    exact Nat.mul_le_mul_right _ hcard
  obtain ⟨v, hv⟩ : ∃ v, v ∉ D.layerF H (2 * M + (K + 1) + 1) := by
    by_contra hno
    push Not at hno
    have : D.layerF H (2 * M + (K + 1) + 1) = Finset.univ := Finset.eq_univ_iff_forall.2 hno
    rw [this, Finset.card_univ] at hsz
    exact lt_irrefl _ hsz
  refine false_of_far hT hC hDir hU hs hM P H (fun c hc ↦ ?_) hv fun Y hY hc ↦ ?_
  · exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
  · have h1 := card_supp_le_finrank (D := D) Y
    obtain ⟨κ', i1, i2, P', hP', -⟩ := hBr Y hY (by omega)
    exact ⟨κ', i1, i2, P', hP'⟩

end Final

section QuotFinal

variable {D₀ : DirData k A} {T' : Set D₀.ι} {hsub : T' ⊆ D₀.T} [IsAlgClosed k]

/-- The points of the polygon of branch data. -/
lemma BranchQ.H_props {Y : FDMod k (D₀.QAlg T')} {κ : Type} (B : BranchQ (T' := T') Y κ)
    (hC₀ : ∀ x y, cartan D₀ y x ≤ 1) (hC : ∀ x y, cartan (D₀.quotAny hsub) y x ≤ 1)
    (hT' : ∀ x, x ∈ (D₀.quotAny hsub).T) (c : (D₀.quotAny hsub).ι)
    (hc : c ∈ ((B.data (hsub := hsub) hC₀).poly hC hT').H) :
    (∃ y : Y, (D₀.quotAny hsub).e c • y ≠ 0) ∧ ∃ z, D₀.Cn c.1 B.a.1 z ∧ z ≠ 0 := by
  obtain ⟨i, -, -⟩ := B.two
  have hact : ∀ {z : A} {c' : T'}, D₀.Cn c'.1 B.a.1 z → D₀.qmap T' z ≠ 0 → (∃ (L : A) (u : Y),
      D₀.qmap T' (L * z) • u ≠ 0) → ∃ y : Y, (D₀.quotAny hsub).e c' • y ≠ 0 := by
    rintro z c' hz - ⟨L, u, hu⟩
    refine ⟨D₀.qmap T' z • u, fun h0 ↦ hu ?_⟩
    have h1 : (D₀.quotAny hsub).e c' • D₀.qmap T' z • u = D₀.qmap T' (D₀.e c'.1 * z) • u := by
      rw [map_mul, mul_smul]
      rfl
    rw [hz.1] at h1
    rw [map_mul, mul_smul, ← h1, h0, smul_zero]
  rcases hc with rfl | rfl | hc
  · obtain ⟨u, hu⟩ := B.act i
    refine ⟨?_, D₀.e B.a.1, cn_e _, D₀.ne _ (hsub B.a.2)⟩
    have h1 : D₀.qmap T' (B.G i * B.F i) ≠ 0 := fun h ↦ hu (by rw [h, zero_smul])
    refine ⟨(D₀.quotAny hsub).e B.a • u, fun h0 ↦ hu ?_⟩
    have h2 : D₀.qmap T' (B.G i * B.F i) • u =
        D₀.qmap T' (B.G i * B.F i) • ((D₀.quotAny hsub).e B.a • u) := by
      rw [← mul_smul]
      congr 1
      change _ = D₀.qmap T' _ * D₀.qmap T' (D₀.e B.a.1)
      rw [← map_mul, ((B.hG i).mul (B.hF i)).2]
    have h0' : (D₀.quotAny hsub).e B.a • (D₀.quotAny hsub).e B.a • u = 0 := h0
    rw [← mul_smul, show (D₀.quotAny hsub).e B.a * (D₀.quotAny hsub).e B.a =
      (D₀.quotAny hsub).e B.a from ((D₀.quotAny hsub).idem B.a).eq] at h0'
    rw [h2, h0', smul_zero]
  · obtain ⟨u, hu⟩ := B.act i
    have hz := (B.hG i).mul (B.hF i)
    have hne : B.G i * B.F i ≠ 0 := fun h ↦ hu (by rw [h, map_zero, zero_smul])
    refine ⟨⟨D₀.qmap T' (B.G i * B.F i) • u, fun h0 ↦ hu ?_⟩, _, hz, hne⟩
    have h2 : (D₀.quotAny hsub).e B.b • D₀.qmap T' (B.G i * B.F i) • u =
        D₀.qmap T' (B.G i * B.F i) • u := by
      rw [← mul_smul]
      congr 1
      change D₀.qmap T' (D₀.e B.b.1) * D₀.qmap T' _ = _
      rw [← map_mul, hz.1]
    have h0' : (D₀.quotAny hsub).e B.b • D₀.qmap T' (B.G i * B.F i) • u = 0 := h0
    rw [← h2, h0']
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hc
    obtain ⟨L, M, R, hL, hM, hR, hne⟩ := BranchQ.tri_up hj.2
    have hz := (hM.mul hR)
    have hMR : M * R ≠ 0 := fun h ↦ hne (by rw [mul_assoc, h, mul_zero])
    obtain ⟨u, hu⟩ := B.act_of_ne hC₀ ((hL.mul hM).mul hR) hne
    refine ⟨?_, _, hz, hMR⟩
    refine hact hz (fun h ↦ hu ?_) ⟨L, u, ?_⟩
    · rw [mul_assoc, map_mul, h, mul_zero, zero_smul]
    · rwa [← mul_assoc]

/-- **Large sincere directing modules exclude branch data.** -/
theorem false_of_large_quot {U : FDMod k (D₀.QAlg T')} (hC₀ : ∀ x y, cartan D₀ y x ≤ 1)
    (hDir : ∀ N : FDMod k (D₀.QAlg T'), IndNT N → Directing N) (hU : Directing U)
    (hs : Sincere (D₀.quotAny hsub) U) {M K Δ h : ℕ} (hM : RunB D₀ M)
    (hΔ : ∀ a, (Finset.univ.filter ((D₀.quotAny hsub).gr.Adj a)).card ≤ Δ)
    (hcardU : K < finrank k U)
    (hcount : ∀ a : T', (Finset.univ.filter fun c : (D₀.quotAny hsub).ι ↦
      ∃ z, D₀.Cn c.1 a.1 z ∧ z ≠ 0).card ≤ h)
    (cc : D₀.ι → D₀.ι → A) (Cond : D₀.ι → D₀.ι → Prop) (hcc : ∀ i j, D₀.Cn j i (cc i j))
    (hB₂ : ∀ N : FDMod k A, IndNT N → K < finrank k N →
      ∃ i j, Cond i j ∧ ∃ n : N, cc i j • n ≠ 0)
    (hB₁ : ∀ (Y : FDMod k (D₀.QAlg T')) (i j : T'), Cond i.1 j.1 →
      (∃ u : Y, D₀.qmap T' (cc i.1 j.1) • u ≠ 0) →
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ), Nonempty (BranchQ (T' := T') Y κ))
    (hlarge : h * (Δ + 1) ^ (2 * M + (K + 1) + 1) < Fintype.card (D₀.quotAny hsub).ι) : False := by
  have hT' : ∀ x, x ∈ (D₀.quotAny hsub).T := fun _ ↦ Set.mem_univ _
  have hC : ∀ x y, cartan (D₀.quotAny hsub) y x ≤ 1 := fun x y ↦
    (cartan_quotAny_le hsub x y).trans (hC₀ x.1 y.1)
  refine false_of_large hT' hC hDir hU hs (runB_quot hM) hΔ hcardU (fun Y hY hlt ↦ ?_) hlarge
  have hN : IndNT (resFD (D₀.qmap T') Y) := (indNT_res_iff (D₀.qmap_surjective T') Y).2 hY
  obtain ⟨i, j, hcond, n, hn⟩ := hB₂ _ hN hlt
  have hn' : D₀.qmap T' (cc i j) • (show Y from n) ≠ 0 := hn
  have hq0 : D₀.qmap T' (cc i j) ≠ 0 := fun h ↦ hn' (by rw [h, zero_smul])
  have hj : j ∈ T' := by
    by_contra h'
    exact hq0 (qmap_cn_eq_zero (hcc i j) h')
  have hi : i ∈ T' := by
    by_contra h'
    apply hq0
    rw [← (hcc i j).2, map_mul, D₀.qmap_e_out T' h', mul_zero]
  obtain ⟨κ, i1, i2, ⟨B⟩⟩ := hB₁ Y ⟨i, hi⟩ ⟨j, hj⟩ hcond ⟨n, hn'⟩
  refine ⟨κ, i1, i2, (B.data (hsub := hsub) hC₀).poly hC hT', fun c hc ↦
    (B.H_props hC₀ hC hT' c hc).1, ?_⟩
  refine (Finset.card_le_card fun c hc ↦ ?_).trans (hcount B.a)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (B.H_props hC₀ hC hT' c (Finset.mem_filter.1 hc).2).2⟩

end QuotFinal

section Desc

variable (D₀ : DirData k A)

/-- **The support algebra of a module.** -/
theorem sincere_descend (N : FDMod k A) (hN : IndNT N) :
    ∃ (hsub : D₀.Supp N ⊆ D₀.T) (U : FDMod k (D₀.QAlg (D₀.Supp N))), IndNT U ∧
      finrank k U = finrank k N ∧ Sincere (D₀.quotAny hsub) U := by
  have hsub : D₀.Supp N ⊆ D₀.T := by
    rintro y ⟨m, hm⟩
    by_contra hy
    exact hm (by rw [D₀.zero y hy, zero_smul])
  have hl : LivesOn (D := D₀) (D₀.Supp N) N := (livesOn_iff_supp _ _).2 subset_rfl
  refine ⟨hsub, descendQ N hl, ?_, rfl, ?_⟩
  · exact (indNT_res_iff (D₀.qmap_surjective _) _).1 (indNT_of_iso (isoM_descend' N hl) hN)
  · rintro ⟨x, m, hm⟩
    refine ⟨show descendQ N hl from m, fun h0 ↦ hm ?_⟩
    exact (FDMod.lin (descIsoQ N hl)).map_smul (D₀.e x) m |>.symm.trans
      (congrArg (FDMod.lin (descIsoQ N hl)) h0 |>.trans (map_zero _))

end Desc

end DirData

end LargeIndecomposable.AR
