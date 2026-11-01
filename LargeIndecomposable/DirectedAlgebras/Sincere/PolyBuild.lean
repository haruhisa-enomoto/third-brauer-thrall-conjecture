module

public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereGraph

/-!
# Polygons from branching morphisms

Let `w : a → b` be a nonzero morphism in a directed algebra with one-dimensional corners. Suppose
that `w` factors through at least two points `n j` (the first points of the arms), and that the
sets of points through which `w` factors after `n j` are disjoint. Then the points through which
`w` factors form a polygon (`polyOfData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A}

/-- An element of the corner `e_y A e_x`. -/
def Cn (D : DirData k A) (y x : D.ι) (z : A) : Prop := D.e y * z = z ∧ z * D.e x = z

lemma cn_corner (y x : D.ι) (a : A) : D.Cn y x (D.e y * a * D.e x) :=
  ⟨by rw [← mul_assoc, ← mul_assoc, D.e_mul_e], by rw [mul_assoc, D.e_mul_e]⟩

lemma Cn.mul {x y z : D.ι} {a b : A} (ha : D.Cn z y a) (hb : D.Cn y x b) : D.Cn z x (a * b) :=
  ⟨by rw [← mul_assoc, ha.1], by rw [mul_assoc, hb.2]⟩

lemma Cn.eq {x y : D.ι} {a : A} (ha : D.Cn y x a) : D.e y * a * D.e x = a := by
  rw [ha.1, ha.2]

lemma cn_e (x : D.ι) : D.Cn x x (D.e x) := ⟨D.e_mul_e x, D.e_mul_e x⟩

/-- Corners are lines. -/
lemma Cn.scalar (hC : ∀ x y, cartan D y x ≤ 1) {x y : D.ι} {z₀ z : A} (h0 : D.Cn y x z₀)
    (h : D.Cn y x z) (hne : z₀ ≠ 0) : ∃ c : k, z = c • z₀ := by
  let P := projE (k := k) (D.idem x)
  let el : ∀ {u : A}, D.Cn y x u → eSub P (D.e y) := fun {u} hu ↦
    ⟨⟨u, hu.2⟩, Subtype.ext hu.1⟩
  have hv : el h0 ≠ 0 := fun h' ↦ hne (congrArg (fun w : eSub P (D.e y) ↦ ((w : P) :
    leftIdeal (D.idem x)).1) h')
  have hle : finrank k (eSub P (D.e y)) ≤ 1 := by
    have : (finrank k (eSub P (D.e y)) : ℤ) ≤ 1 := hC x y
    omega
  obtain ⟨v, hv'⟩ := finrank_le_one_iff.1 hle
  obtain ⟨a, ha⟩ := hv' (el h0)
  obtain ⟨b, hb⟩ := hv' (el h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hv (by rw [← ha, zero_smul])
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : el h = (b * a⁻¹) • el h0 := by
    rw [← ha, ← hb, smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  exact congrArg (fun w : eSub P (D.e y) ↦ ((w : P) : leftIdeal (D.idem x)).1) h1

/-- A factorization `a → n → c → b` of nonzero composite. -/
def Tri (D : DirData k A) (a b n c : D.ι) : Prop :=
  ∃ L M R, D.Cn b c L ∧ D.Cn c n M ∧ D.Cn n a R ∧ L * M * R ≠ 0

section TriLemmas

variable (hC : ∀ x y, cartan D y x ≤ 1)
include hC

/-- Going back along a nonzero composite. -/
lemma tri_step {a b n c c' : D.ι} (h : D.Tri a b n c') {M₁ M₂ : A} (h1 : D.Cn c' c M₁)
    (h2 : D.Cn c n M₂) (h12 : M₁ * M₂ ≠ 0) : ∃ L, D.Cn b c' L ∧ L * M₁ ≠ 0 ∧ D.Tri a b n c := by
  obtain ⟨L, M, R, hL, hM, hR, hne⟩ := h
  obtain ⟨l, hl⟩ := Cn.scalar hC (h1.mul h2) hM h12
  have h3 : L * (M₁ * M₂) * R ≠ 0 := by
    intro h0
    apply hne
    rw [hl, mul_smul_comm, smul_mul_assoc, h0, smul_zero]
  have h4 : L * M₁ ≠ 0 := by
    intro h0
    apply h3
    rw [← mul_assoc, h0, zero_mul, zero_mul]
  refine ⟨L, hL, h4, L * M₁, M₂, R, hL.mul h1, h2, hR, ?_⟩
  rwa [mul_assoc L M₁]

/-- Two factorizations of the same composite through `c`. -/
lemma tri_swap {a b n n' c c' : D.ι} (h : D.Tri a b n' c) {L M₁ M₂ : A} (hL : D.Cn b c' L)
    (h1 : D.Cn c' c M₁) (h2 : D.Cn c a M₂) (hne : L * M₁ * M₂ ≠ 0) (hc : n = n') :
    D.Tri a b n c' := by
  subst hc
  obtain ⟨L', M, R, hL', hM, hR, hne'⟩ := h
  have h3 : M * R ≠ 0 := fun h0 ↦ hne' (by rw [mul_assoc, h0, mul_zero])
  have h4 : M₂ ≠ 0 := fun h0 ↦ hne (by rw [h0, mul_zero])
  obtain ⟨l, hl⟩ := Cn.scalar hC (hM.mul hR) h2 h3
  refine ⟨L, M₁ * M, R, hL, h1.mul hM, hR, fun h0 ↦ hne ?_⟩
  rw [hl, mul_smul_comm, ← mul_assoc]
  have : L * M₁ * M * R = 0 := by rw [mul_assoc L M₁]; exact h0
  rw [this, smul_zero]

end TriLemmas

/-- The data of a polygon. -/
structure PolyData (D : DirData k A) (κ : Type) where
  /-- The source. -/
  a : D.ι
  /-- The sink. -/
  b : D.ι
  hab : a ≠ b
  /-- The first points of the arms. -/
  n : κ → D.ι
  hna : ∀ j, n j ≠ a
  hnb : ∀ j, n j ≠ b
  self : ∀ j, D.Tri a b (n j) (n j)
  cover : ∀ c L M, c ≠ a → c ≠ b → D.Cn b c L → D.Cn c a M → L * M ≠ 0 → ∃ j, D.Tri a b (n j) c
  disj : ∀ i j c, c ≠ b → D.Tri a b (n i) c → D.Tri a b (n j) c → i = j
  two : ∃ i j : κ, i ≠ j

namespace PolyData

variable {κ : Type} (P : PolyData D κ)

/-- An arm. -/
def arm (j : κ) : Set D.ι := {c | c ≠ P.b ∧ D.Tri P.a P.b (P.n j) c}

lemma a_arm (j : κ) : P.a ∉ P.arm j := by
  rintro ⟨-, L, M, R, -, hM, hR, hne⟩
  have h1 : M * R = 0 := by
    rw [← hM.eq, ← hR.eq]
    exact D.corner_cross (P.hna j).symm _ _
  exact hne (by rw [mul_assoc, h1, mul_zero])

lemma mem_of_cross {b c' : D.ι} (hbc : c' ≠ b) {L M : A} (hL : D.Cn b c' L) (hM : D.Cn c' b M) :
    L * M = 0 := by
  rw [← hL.eq, ← hM.eq]
  exact D.corner_cross hbc.symm _ _

lemma corner_mul (c' c x : D.ι) (u v : A) :
    (D.e c' * u * D.e c) * (D.e c * v * D.e x) = D.e c' * u * (D.e c * v * D.e x) := by
  rw [mul_assoc (D.e c' * u), (cn_corner c x v).1]

variable (hC : ∀ x y, cartan D y x ≤ 1)
include hC

/-- A point before a point of an arm, seen from the source, is in the arm. -/
lemma tail_mem {l : κ} {c c' : D.ι} (hc' : c' ∈ P.arm l) (hca : c ≠ P.a) {M₁ M₂ : A}
    (h1 : D.Cn c' c M₁) (h2 : D.Cn c P.a M₂) (h12 : M₁ * M₂ ≠ 0) : c ∈ P.arm l := by
  obtain ⟨hne, L, M, R, hL, hM, hR, hLMR⟩ := hc'
  have hMR : M * R ≠ 0 := fun h0 ↦ hLMR (by rw [mul_assoc, h0, mul_zero])
  obtain ⟨t, ht⟩ := Cn.scalar hC (h1.mul h2) (hM.mul hR) h12
  have h3 : L * (M₁ * M₂) ≠ 0 := by
    intro h0
    apply hLMR
    rw [mul_assoc, ht, mul_smul_comm, h0, smul_zero]
  have h4 : L * M₁ ≠ 0 := fun h0 ↦ h3 (by rw [← mul_assoc, h0, zero_mul])
  have hcb : c ≠ P.b := by
    rintro rfl
    exact h4 (mem_of_cross hne hL h1)
  obtain ⟨j, hj⟩ := P.cover c (L * M₁) M₂ hca hcb (hL.mul h1) h2 (by rwa [mul_assoc])
  have h5 : D.Tri P.a P.b (P.n j) c' := tri_swap hC hj hL h1 h2 (by rwa [mul_assoc]) rfl
  have hjl : j = l := P.disj j l c' hne h5 ⟨L, M, R, hL, hM, hR, hLMR⟩
  subst hjl
  exact ⟨hcb, hj⟩

/-- A point between `n j` and a point of the arm is in the arm. -/
lemma mid_mem {j : κ} {c c' : D.ι} (hc' : c' ∈ P.arm j) {M₁ M₂ : A} (h1 : D.Cn c' c M₁)
    (h2 : D.Cn c (P.n j) M₂) (h12 : M₁ * M₂ ≠ 0) : c ∈ P.arm j := by
  obtain ⟨L, hL, h3, h4⟩ := tri_step hC hc'.2 h1 h2 h12
  refine ⟨?_, h4⟩
  rintro rfl
  exact h3 (mem_of_cross hc'.1 hL h1)

/-- The arms give thin quotients. -/
lemma thin1 (j : κ) : Thin D (P.n j) (P.arm j) where
  mem := ⟨P.hnb j, P.self j⟩
  ne c hc := by
    obtain ⟨-, L, M, R, -, hM, -, hne⟩ := hc
    refine ⟨M, ?_⟩
    rw [hM.eq]
    exact fun h0 ↦ hne (by rw [h0, mul_zero, zero_mul])
  cl c c' hc hc' u v := by
    by_contra h0
    rw [← corner_mul] at h0
    exact hc (P.mid_mem hC hc' (cn_corner _ _ _) (cn_corner _ _ _) h0)

/-- The sink is reached from the arms. -/
lemma thin2 (j : κ) : Thin D (P.n j) (insert P.b (P.arm j)) where
  mem := Or.inr ⟨P.hnb j, P.self j⟩
  ne c hc := by
    obtain ⟨L₀, M₀, R₀, hL₀, hM₀, hR₀, hne₀⟩ := P.self j
    rcases hc with rfl | hc
    · refine ⟨L₀, ?_⟩
      rw [hL₀.eq]
      exact fun h0 ↦ hne₀ (by rw [h0, zero_mul, zero_mul])
    · exact (P.thin1 hC j).ne c hc
  cl c c' hc hc' u v := by
    by_contra h0
    rw [← corner_mul] at h0
    rcases hc' with rfl | hc'
    · apply hc
      obtain ⟨L₀, M₀, R₀, hL₀, hM₀, hR₀, hne₀⟩ := P.self j
      have hLM : L₀ * M₀ ≠ 0 := fun h ↦ hne₀ (by rw [h, zero_mul])
      obtain ⟨t, ht⟩ := Cn.scalar hC ((cn_corner _ _ u).mul (cn_corner _ _ v)) (hL₀.mul hM₀) h0
      have h3 : (D.e P.b * u * D.e c) * (D.e c * v * D.e (P.n j)) * R₀ ≠ 0 := by
        intro h
        apply hne₀
        rw [ht, smul_mul_assoc, h, smul_zero]
      by_cases hcb : c = P.b
      · exact Or.inl hcb
      · exact Or.inr ⟨hcb, _, _, R₀, cn_corner _ _ u, cn_corner _ _ v, hR₀, h3⟩
    · exact hc (Or.inr (P.mid_mem hC hc' (cn_corner _ _ _) (cn_corner _ _ _) h0))

/-- Unions of arms and the source give thin quotients. -/
lemma thinU (hT : ∀ x, x ∈ D.T) (J : Set κ) : Thin D P.a (insert P.a (⋃ j ∈ J, P.arm j)) where
  mem := Or.inl rfl
  ne c hc := by
    rcases hc with rfl | hc
    · refine ⟨1, ?_⟩
      rw [mul_one, D.e_mul_e]
      exact D.ne _ (hT _)
    · obtain ⟨j, -, -, L, M, R, -, hM, hR, hne⟩ := Set.mem_iUnion₂.1 hc
      refine ⟨M * R, ?_⟩
      rw [(hM.mul hR).eq]
      exact fun h0 ↦ hne (by rw [mul_assoc, h0, mul_zero])
  cl c c' hc hc' u v := by
    by_contra h0
    rw [← corner_mul] at h0
    have hca : c ≠ P.a := fun h ↦ hc (Or.inl h)
    rcases hc' with rfl | hc'
    · apply h0
      exact D.corner_cross hca.symm _ _
    · obtain ⟨j, hj, hc'j⟩ := Set.mem_iUnion₂.1 hc'
      exact hc (Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, P.tail_mem hC hc'j hca (cn_corner _ _ _)
        (cn_corner _ _ _) h0⟩))

/-- The whole polygon gives a thin quotient. -/
lemma thinH (hT : ∀ x, x ∈ D.T) : Thin D P.a (insert P.a (insert P.b (⋃ j, P.arm j))) where
  mem := Or.inl rfl
  ne c hc := by
    rcases hc with rfl | rfl | hc
    · exact (P.thinU hC hT Set.univ).ne _ (Or.inl rfl)
    · obtain ⟨i, -, -⟩ := P.two
      obtain ⟨L, M, R, hL, hM, hR, hne⟩ := P.self i
      refine ⟨L * M * R, ?_⟩
      rw [((hL.mul hM).mul hR).eq]
      exact hne
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hc
      exact (P.thinU hC hT {j}).ne c (Or.inr (Set.mem_iUnion₂.2 ⟨j, rfl, hj⟩))
  cl c c' hc hc' u v := by
    by_contra h0
    rw [← corner_mul] at h0
    have hca : c ≠ P.a := fun h ↦ hc (Or.inl h)
    have hcb : c ≠ P.b := fun h ↦ hc (Or.inr (Or.inl h))
    rcases hc' with rfl | rfl | hc'
    · exact h0 (D.corner_cross hca.symm _ _)
    · obtain ⟨j, hj⟩ := P.cover c _ _ hca hcb (cn_corner _ _ u) (cn_corner _ _ v) h0
      exact hc (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hcb, hj⟩)))
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hc'
      exact hc (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, P.tail_mem hC hj hca (cn_corner _ _ _)
        (cn_corner _ _ _) h0⟩)))

/-- **The polygon of the data.** -/
def poly (hT : ∀ x, x ∈ D.T) : Poly D κ where
  a := P.a
  b := P.b
  hab := P.hab
  n := P.n
  arm := P.arm
  two := P.two
  a_arm := P.a_arm
  b_arm _ h := h.1 rfl
  disj i j hij c hi hj := hij (P.disj i j c hi.1 hi.2 hj.2)
  th1 := P.thin1 hC
  th2 := P.thin2 hC
  th3 j := by
    have := P.thinU hC hT {j}
    simpa using this
  th4 i j _ := by
    have := P.thinU hC hT {i, j}
    simpa using this
  th5 := P.thinH hC hT

end PolyData

section Quot

variable (D₀ : DirData k A) (T' : Set D₀.ι) (hsub : T' ⊆ D₀.T)

include hsub in
/-- **All indecomposables of a quotient are directing.** -/
theorem directing_quotAny (hg : ∀ x, Good (projE (k := k) (D₀.idem x))) (hT : ∀ x, x ∈ D₀.T) (b : ℕ)
    (hb : ∀ N : FDMod k A, IndNT N → finrank k N ≤ b) (N : FDMod k (D₀.QAlg T')) (hN : IndNT N) :
    Directing N :=
  directing_of_bounded (D₀.quotAny hsub)
    (fun x ↦ good_quot hsub x (hg x.1)) (fun _ ↦ Set.mem_univ _) b
    (fun N' hN' ↦ hb _ ((indNT_res_iff (D₀.qmap_surjective T') N').2 hN')) N hN

variable {T' D₀ hsub}

/-- Corners of the quotient lift. -/
lemma lift_cn {y x : T'} {z : D₀.QAlg T'} (h : (D₀.quotAny hsub).Cn y x z) :
    ∃ z₀, D₀.Cn y.1 x.1 z₀ ∧ D₀.qmap T' z₀ = z := by
  obtain ⟨w, rfl⟩ := D₀.qmap_surjective T' z
  refine ⟨D₀.e y.1 * w * D₀.e x.1, cn_corner _ _ _, ?_⟩
  rw [map_mul, map_mul]
  exact h.eq

lemma map_cn {y x : T'} {z₀ : A} (h : D₀.Cn y.1 x.1 z₀) :
    (D₀.quotAny hsub).Cn y x (D₀.qmap T' z₀) :=
  ⟨by
    change D₀.qmap T' (D₀.e y.1) * D₀.qmap T' z₀ = _
    rw [← map_mul, h.1], by
    change D₀.qmap T' z₀ * D₀.qmap T' (D₀.e x.1) = _
    rw [← map_mul, h.2]⟩

lemma qmap_cn_eq_zero {c x : D₀.ι} {z : A} (hz : D₀.Cn c x z) (hc : c ∉ T') : D₀.qmap T' z = 0 := by
  rw [← hz.1, map_mul, D₀.qmap_e_out T' hc, zero_mul]

/-- Branch data of a module over a quotient. -/
structure BranchQ (U : FDMod k (D₀.QAlg T')) (κ : Type) where
  /-- The source. -/
  a : T'
  /-- The sink. -/
  b : T'
  hab : a ≠ b
  /-- The first points of the arms. -/
  n : κ → T'
  hna : ∀ j, n j ≠ a
  hnb : ∀ j, n j ≠ b
  /-- The first morphisms. -/
  F : κ → A
  /-- The other morphisms. -/
  G : κ → A
  hF : ∀ j, D₀.Cn (n j).1 a.1 (F j)
  hG : ∀ j, D₀.Cn b.1 (n j).1 (G j)
  act : ∀ j, ∃ u : U, D₀.qmap T' (G j * F j) • u ≠ 0
  cover : ∀ c L M, c ≠ a.1 → c ≠ b.1 → D₀.Cn b.1 c L → D₀.Cn c a.1 M → L * M ≠ 0 →
    ∃ j, D₀.Tri a.1 b.1 (n j).1 c
  disj : ∀ i j c, c ≠ b.1 → D₀.Tri a.1 b.1 (n i).1 c → D₀.Tri a.1 b.1 (n j).1 c → i = j
  two : ∃ i j : κ, i ≠ j

variable {U : FDMod k (D₀.QAlg T')} {κ : Type} (B : BranchQ U κ)
  (hC₀ : ∀ x y, cartan D₀ y x ≤ 1)
include hC₀

/-- A nonzero composite of the base acts nonzero. -/
lemma BranchQ.act_of_ne {z : A} (hz : D₀.Cn B.b.1 B.a.1 z) (h0 : z ≠ 0) :
    ∃ u : U, D₀.qmap T' z • u ≠ 0 := by
  obtain ⟨i, -, -⟩ := B.two
  obtain ⟨u, hu⟩ := B.act i
  obtain ⟨c, hc⟩ := Cn.scalar hC₀ hz ((B.hG i).mul (B.hF i)) h0
  refine ⟨u, fun h ↦ hu ?_⟩
  rw [hc, map_smul, smul_assoc, h, smul_zero]

/-- Factorizations in the base lie over points of the quotient. -/
lemma BranchQ.tri_mem {n c : D₀.ι} (h : D₀.Tri B.a.1 B.b.1 n c) : c ∈ T' ∧ n ∈ T' := by
  obtain ⟨L, M, R, hL, hM, hR, hne⟩ := h
  obtain ⟨u, hu⟩ := B.act_of_ne hC₀ ((hL.mul hM).mul hR) hne
  have hq : D₀.qmap T' (L * M * R) ≠ 0 := fun h ↦ hu (by rw [h, zero_smul])
  constructor
  · by_contra hc
    apply hq
    rw [map_mul, map_mul, ← hM.1, map_mul (D₀.qmap T') (D₀.e c) M, D₀.qmap_e_out T' hc, zero_mul,
      mul_zero, zero_mul]
  · by_contra hc
    apply hq
    rw [map_mul, map_mul, ← hR.1, map_mul (D₀.qmap T') (D₀.e n) R, D₀.qmap_e_out T' hc, zero_mul,
      mul_zero]

/-- Factorizations go down to the quotient. -/
lemma BranchQ.tri_down {n c : T'} (h : D₀.Tri B.a.1 B.b.1 n.1 c.1) :
    (D₀.quotAny hsub).Tri B.a B.b n c := by
  obtain ⟨L, M, R, hL, hM, hR, hne⟩ := h
  obtain ⟨u, hu⟩ := B.act_of_ne hC₀ ((hL.mul hM).mul hR) hne
  refine ⟨D₀.qmap T' L, D₀.qmap T' M, D₀.qmap T' R, map_cn hL, map_cn hM, map_cn hR, fun h ↦ hu ?_⟩
  rw [map_mul, map_mul, h, zero_smul]

omit hC₀ in
/-- Factorizations come from the base. -/
lemma BranchQ.tri_up {a b n c : T'} (h : (D₀.quotAny hsub).Tri a b n c) :
    D₀.Tri a.1 b.1 n.1 c.1 := by
  obtain ⟨L, M, R, hL, hM, hR, hne⟩ := h
  obtain ⟨L₀, hL₀, rfl⟩ := lift_cn hL
  obtain ⟨M₀, hM₀, rfl⟩ := lift_cn hM
  obtain ⟨R₀, hR₀, rfl⟩ := lift_cn hR
  refine ⟨L₀, M₀, R₀, hL₀, hM₀, hR₀, fun h0 ↦ hne ?_⟩
  rw [← map_mul, ← map_mul, h0, map_zero]

/-- **The polygon data of branch data.** -/
def BranchQ.data : PolyData (D₀.quotAny hsub) κ where
  a := B.a
  b := B.b
  hab := B.hab
  n := B.n
  hna := B.hna
  hnb := B.hnb
  self j := by
    obtain ⟨u, hu⟩ := B.act j
    refine ⟨D₀.qmap T' (B.G j), D₀.qmap T' (D₀.e (B.n j).1), D₀.qmap T' (B.F j), map_cn (B.hG j),
      map_cn (cn_e _), map_cn (B.hF j), fun h ↦ hu ?_⟩
    rw [← map_mul, (B.hG j).2] at h
    rw [map_mul, h, zero_smul]
  cover c L M hca hcb hL hM hne := by
    obtain ⟨L₀, hL₀, rfl⟩ := lift_cn hL
    obtain ⟨M₀, hM₀, rfl⟩ := lift_cn hM
    obtain ⟨j, hj⟩ := B.cover c.1 L₀ M₀ (fun h ↦ hca (Subtype.ext h)) (fun h ↦ hcb (Subtype.ext h))
      hL₀ hM₀ (fun h0 ↦ hne (by rw [← map_mul, h0, map_zero]))
    exact ⟨j, B.tri_down hC₀ hj⟩
  disj i j c hcb h1 h2 := B.disj i j c.1 (fun h ↦ hcb (Subtype.ext h)) (BranchQ.tri_up h1)
    (BranchQ.tri_up h2)
  two := B.two

omit hC₀ in
/-- **Chains of quotients are bounded.** -/
theorem runB_quot {M : ℕ} (hM : RunB D₀ M) : RunB (D₀.quotAny hsub) M := by
  intro x c s t w hne hlen hch
  have hlift : ∀ i, ∃ c₀ : A, D₀.qmap T' c₀ = c i := fun i ↦ D₀.qmap_surjective T' (c i)
  choose c₀ hc₀ using hlift
  have key : ∀ {t : ℕ} {w : D₀.QAlg T'}, IsChain (D₀.quotAny hsub) x c s t w →
      ∃ w₀, IsChain D₀ (fun i ↦ (x i).1) c₀ s t w₀ ∧ D₀.qmap T' w₀ = w := by
    intro t w h
    induction h with
    | refl => exact ⟨1, .refl, map_one _⟩
    | @step t w _ ih =>
      obtain ⟨w₀, h1, h2⟩ := ih
      refine ⟨_, h1.step, ?_⟩
      rw [map_mul, map_mul, h2, hc₀]
      rfl
  obtain ⟨w₀, h1, rfl⟩ := key hch
  have h2 := hM (fun i ↦ (x i).1) c₀ s t w₀ (fun i h3 h4 h5 ↦ hne i h3 h4 (Subtype.ext h5)) hlen h1
  change D₀.qmap T' (D₀.e (x t).1) * D₀.qmap T' w₀ * D₀.qmap T' (D₀.e (x s).1) = 0
  rw [← map_mul, ← map_mul, h2, map_zero]

end Quot

end DirData

end LargeIndecomposable.AR
