module

public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereEuler
public import LargeIndecomposable.DirectedAlgebras.Preprojective.NotWeaklyPositive
public import LargeIndecomposable.UnitForms.Ovsienko
public import LargeIndecomposable.UnitForms.RootBound

/-!
# Critical algebras, without tilting

Let `D` be a directed algebra in which indecomposable projectives are good, with unbounded
indecomposables, such that the indecomposables killed by any `e_i` are rigid and bounded. Then the
Euler form is critical, and at a source or sink `x` where the radical vector is `1` there is a brick
`V` with `V(x) = 0` and at least two independent extensions with the simple at `x`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A)

/-- The simple module at `x`. -/
def simpleM (x : D.ι) (hx : x ∈ D.T) : FDMod k A :=
  letI : Module A k := Module.compHom k (D.chi x hx).toRingHom
  { carrier := k
    isScalarTower := ⟨fun c a m ↦ by
      change D.chi x hx (c • a) * m = c * (D.chi x hx a * m)
      rw [map_smul, smul_eq_mul, mul_assoc]⟩ }

variable {D}

/-- The action on the simple module. -/
lemma simpleM_smul {x : D.ι} (hx : x ∈ D.T) (a : A) (m : D.simpleM x hx) :
    a • m = (show k from (D.chi x hx a * (show k from m))) := rfl

lemma dimZ_simpleM {x : D.ι} (hx : x ∈ D.T) (y : D.ι) :
    dimZ D (D.simpleM x hx) y = if y = x then 1 else 0 := by
  unfold dimZ dimv
  by_cases hy : y = x
  · subst hy
    have htop : eSub (D.simpleM y hx) (D.e y) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      change D.chi y hx (D.e y) * (show k from m) = m
      rw [D.chi_e_self, one_mul]
    rw [htop, finrank_top, if_pos rfl]
    change ((finrank k k : ℕ) : ℤ) = 1
    simp
  · have hbot : eSub (D.simpleM x hx) (D.e y) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have h1 : D.chi x hx (D.e y) * (show k from m) = m := hm
      rw [D.chi_e_ne x hx hy, zero_mul] at h1
      exact (Submodule.mem_bot k).2 h1.symm
    rw [hbot, finrank_bot, if_neg hy]
    rfl

/-- Every nonnegative vector is a dimension vector. -/
theorem exists_dimZ (hT : ∀ x, x ∈ D.T) : ∀ (n : ℕ) (v : D.ι → ℕ), ∑ i, v i = n →
    ∃ M : FDMod k A, dimZ D M = fun i ↦ (v i : ℤ) := by
  classical
  intro n
  induction n with
  | zero =>
    intro v hv
    refine ⟨FDMod.zero k A, funext fun i ↦ ?_⟩
    have h1 : v i = 0 := (Finset.sum_eq_zero_iff.1 hv) i (Finset.mem_univ i)
    rw [h1]
    simp only [dimZ, dimv, Nat.cast_zero, Nat.cast_eq_zero]
    exact Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)
  | succ n ih =>
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hv
    let v' : D.ι → ℕ := fun j ↦ if j = i then v j - 1 else v j
    have hsum : ∑ j, v' j = n := by
      have h1 : v = fun j ↦ v' j + if j = i then 1 else 0 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [v']; omega
        · simp [v', hj]
      have h2 := hv
      rw [h1, Finset.sum_add_distrib] at h2
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      omega
    obtain ⟨M, hM⟩ := ih v' hsum
    refine ⟨FDMod.prod (D.simpleM i (hT i)) M, ?_⟩
    have h := dimZ_exact D (M := D.simpleM i (hT i)) (N := FDMod.prod (D.simpleM i (hT i)) M)
      (L := M) (LinearMap.inl A _ _) (LinearMap.snd A _ _) LinearMap.inl_injective
      (fun q ↦ ⟨(0, q), rfl⟩) (LinearMap.range_inl A _ _)
    rw [h, hM]
    funext j
    simp only [Pi.add_apply, dimZ_simpleM]
    by_cases hj : j = i
    · subst hj; simp [v']; omega
    · simp [v', hj]

/-- A module of given dimension vector with minimal endomorphism ring. -/
theorem exists_minEnd (hT : ∀ x, x ∈ D.T) (v : D.ι → ℕ) :
    ∃ V : FDMod k A, dimZ D V = (fun i ↦ (v i : ℤ)) ∧ ∀ W : FDMod k A,
      dimZ D W = dimZ D V → finrank k (V →ₗ[A] V) ≤ finrank k (W →ₗ[A] W) := by
  classical
  have hex : ∃ n, ∃ W : FDMod k A, dimZ D W = (fun i ↦ (v i : ℤ)) ∧
      finrank k (W →ₗ[A] W) = n := by
    obtain ⟨M, hM⟩ := exists_dimZ (k := k) (D := D) hT _ v rfl
    exact ⟨_, M, hM, rfl⟩
  obtain ⟨V, hV, hn⟩ := Nat.find_spec hex
  refine ⟨V, hV, fun W hW ↦ ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨W, hW.trans hV, rfl⟩

lemma smul_eq_zero_of_dimZ {V : FDMod k A} {a : D.ι} (h : dimZ D V a = 0) (m : V) :
    D.e a • m = 0 := by
  have h1 : finrank k (eSub V (D.e a)) = 0 := by
    have : ((finrank k (eSub V (D.e a)) : ℕ) : ℤ) = 0 := h
    exact_mod_cast this
  have hb := Submodule.finrank_eq_zero.1 h1
  have hmem : D.e a • m ∈ eSub V (D.e a) := by
    change D.e a • D.e a • m = _
    rw [← mul_smul, D.e_mul_e]
  rw [hb] at hmem
  exact (Submodule.mem_bot k).1 hmem

/-- The hypothesis on modules killed by one idempotent. -/
def RigidOff (D : DirData k A) : Prop :=
  ∀ (i : D.ι) (N : FDMod k A), IsIndecMod A N → Nontrivial N → (∀ m : N, D.e i • m = 0) →
    ExtVanish N N

/-- Minimal modules killed by `e_a` are rigid. -/
theorem rigid_of_minEnd (hR : RigidOff D) {a : D.ι} {V : FDMod k A} (hV : dimZ D V a = 0)
    (hmin : ∀ W : FDMod k A, dimZ D W = dimZ D V → finrank k (V →ₗ[A] V) ≤ finrank k (W →ₗ[A] W)) :
    ExtVanish V V := by
  refine extVanish_of_minEnd_on (dimZ D) (fun L M N f g hf hg hex ↦ ?_) V
    (fun M h1 h2 ⟨f, hf⟩ ↦ hR a M h1 h2 fun m ↦ hf ?_) hmin
  · exact dimZ_exact D f g hf hg hex
  · rw [map_smul, smul_eq_zero_of_dimZ hV, map_zero]

lemma finrank_end_pos {V : FDMod k A} (h : Nontrivial V) : 0 < finrank k (V →ₗ[A] V) := by
  haveI : Nontrivial (V →ₗ[A] V) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨LinearMap.id, 0, fun h0 ↦ hv (LinearMap.congr_fun h0 v)⟩⟩
  exact Module.finrank_pos

lemma nontrivial_of_dimZ {V : FDMod k A} {i : D.ι} (h : dimZ D V i ≠ 0) : Nontrivial V := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply h
  have : finrank k (eSub V (D.e i)) = 0 :=
    Submodule.finrank_eq_zero.2 (eq_bot_iff.2 fun m _ ↦ (Submodule.mem_bot k).2 (Subsingleton.elim _ _))
  simp [dimZ, dimv, this]

variable {U : FDMod k A}

/-- **Nonsincere vectors have positive Euler form.** -/
theorem euler_pos_off (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) (hR : RigidOff D)
    (a : D.ι) (x : D.ι → ℤ) (hx : Forms.UnitForm.Pos x) (hxa : x a = 0) :
    0 < euler D x x := by
  obtain ⟨V, hV, hmin⟩ := exists_minEnd (k := k) (D := D) hT (fun i ↦ (x i).toNat)
  have hVx : dimZ D V = x := by
    rw [hV]
    funext i
    exact Int.toNat_of_nonneg (hx.1 i)
  have hVa : dimZ D V a = 0 := by rw [hVx, hxa]
  have hrig := rigid_of_minEnd hR hVa hmin
  have h1 := hom_le_euler (D := D) hT hU hs hrig
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx.2 (funext h)
  have hnt : Nontrivial V := nontrivial_of_dimZ (i := i) (by rwa [hVx])
  have h2 := finrank_end_pos hnt
  rw [hVx] at h1
  omega

/-- **The Euler form is critical.** -/
theorem eulerForm_critical [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hR : RigidOff D)
    (hc : ∀ b, ∃ X : FDMod k A, Directing X ∧ Sincere D X ∧ b < finrank k X)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞) (hunb : ∀ b, ∃ X, 𝒞 X ∧ b < finrank k X) :
    (eulerForm D hT).Critical := by
  obtain ⟨U, hU, hs, -⟩ := hc 0
  refine ⟨not_weaklyPositive_of_unbounded D hT h𝒞 hunb, fun a x hx hxa ↦ ?_⟩
  rw [eulerForm_val]
  exact euler_pos_off hT hU hs hR a x hx hxa

/-- The polar form of the Euler form. -/
lemma B_eulerForm (hT : ∀ x, x ∈ D.T) (u v : D.ι → ℤ) :
    (eulerForm D hT).B u v = euler D u v + euler D v u := by
  simp only [Forms.UnitForm.B, eulerForm, euler_apply, add_mul, Finset.sum_add_distrib]
  have e : ∑ a, ∑ b, (cartan D)⁻¹ a b * u a * v b = ∑ a, ∑ b, (cartan D)⁻¹ b a * v a * u b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  rw [e, add_comm]

/-- At a sink, `⟨e_x, v⟩ = v_x`. -/
lemma euler_sink (hT : ∀ x, x ∈ D.T) {x : D.ι} (hx : IsSink D x) (v : D.ι → ℤ) :
    euler D (Pi.single x 1) v = v x := by
  classical
  have h : (fun j ↦ cartan D j x) = Pi.single x 1 := by
    funext j
    by_cases hj : j = x
    · subst hj
      rw [cartan_diag D (hT j)]
      simp
    · rw [Pi.single_eq_of_ne hj]
      have hb : eSub (projE (k := k) (D.idem x)) (D.e j) = ⊥ := by
        rw [eq_bot_iff]
        intro m hm
        have h1 : D.e j • m = m := hm
        have h2 : D.e j * (m : A) * D.e x = m := by
          rw [mul_assoc, show (m : A) * D.e x = m from m.2]
          exact congrArg Subtype.val h1
        rw [hx j hj] at h2
        exact (Submodule.mem_bot k).2 (Subtype.ext h2.symm)
      simp only [cartan]
      rw [hb, finrank_bot]
      rfl
  rw [← h, euler_cartan_col D hT]

/-- At a source, `⟨u, e_x⟩ = u_x`. -/
lemma euler_source (hT : ∀ x, x ∈ D.T) {x : D.ι} (hx : IsSource D x) (u : D.ι → ℤ) :
    euler D u (Pi.single x 1) = u x := by
  classical
  have hrow : ∀ j, cartan D x j = if j = x then 1 else 0 := by
    intro j
    by_cases hj : j = x
    · subst hj
      rw [cartan_diag D (hT j)]
      simp
    · rw [if_neg hj]
      have hb : eSub (projE (k := k) (D.idem j)) (D.e x) = ⊥ := by
        rw [eq_bot_iff]
        intro m hm
        have h1 : D.e x • m = m := hm
        have h2 : D.e x * (m : A) * D.e j = m := by
          rw [mul_assoc, show (m : A) * D.e j = m from m.2]
          exact congrArg Subtype.val h1
        rw [hx j hj] at h2
        exact (Submodule.mem_bot k).2 (Subtype.ext h2.symm)
      simp only [cartan]
      rw [hb, finrank_bot]
      rfl
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  have h1 : (cartan D).mulVec ((cartan D)⁻¹.mulVec u) x = u x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h2 : (cartan D).mulVec ((cartan D)⁻¹.mulVec u) x = (cartan D)⁻¹.mulVec u x := by
    simp only [Matrix.mulVec, dotProduct, hrow]
    simp
  unfold euler
  simp only [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← h2, h1]

/-- **Euler form `-2` gives two independent extension classes.** -/
theorem two_le_of_euler (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) (X Y : FDMod k A)
    (h : euler D (dimZ D X) (dimZ D Y) = -2) :
    finrank k (LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D X (coverList D X))).subtype)) + 2 ≤
      finrank k (syz D X →ₗ[A] Y) := by
  have h2 := euler_ge (D := D) hT hU hs X Y
  rw [h] at h2
  omega

/-- The output of the construction at a point: a brick missing `x`, with two independent classes
of extensions with the simple at `x`, in one of the two directions. -/
def PointBrickM (D : DirData k A) (hT : ∀ x, x ∈ D.T) : Prop :=
  ∃ (x : D.ι) (V : FDMod k A), (∀ φ : V ⟶ V, ∃ c : k, FDMod.lin φ = c • LinearMap.id) ∧
    Nontrivial V ∧ (∀ m : V, D.e x • m = 0) ∧
    ((finrank k (LinearMap.range (precomp k (Y := D.simpleM x (hT x))
        (LinearMap.ker (sumMap D V (coverList D V))).subtype)) + 2 ≤
        finrank k (syz D V →ₗ[A] D.simpleM x (hT x))) ∨
      (finrank k (LinearMap.range (precomp k (Y := V)
        (LinearMap.ker (sumMap D (D.simpleM x (hT x)) (coverList D (D.simpleM x (hT x))))).subtype)) +
        2 ≤ finrank k (syz D (D.simpleM x (hT x)) →ₗ[A] V)))

/-- **Critical directed algebras carry a point and a brick**, without tilting. -/
theorem pointBrickM [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hcard : 3 ≤ Fintype.card D.ι)
    (hR : RigidOff D) (hc : ∀ b, ∃ X : FDMod k A, Directing X ∧ Sincere D X ∧ b < finrank k X)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞) (hunb : ∀ b, ∃ X, 𝒞 X ∧ b < finrank k X) :
    PointBrickM D hT := by
  classical
  have hcrit := eulerForm_critical hT hR hc h𝒞 hunb
  let q := eulerForm D hT
  obtain ⟨hnn, z, c, hz, hrad, hzc, h6, hzero⟩ := Forms.UnitForm.Critical.ovsienko q hcrit hcard
  obtain ⟨R, hR0, hRb⟩ := q.bounded_off hnn c z hzero
  have hval0 : q.val z = 0 := Forms.UnitForm.val_eq_zero_of_radical q hrad
  -- a large sincere directing module
  let n : ℕ := Fintype.card D.ι
  obtain ⟨U, hU, hs, hUb⟩ := hc (n * (7 * (R + 1)).toNat)
  let d : D.ι → ℤ := dimZ D U
  let t : ℤ := d c
  let r : D.ι → ℤ := d - t • z
  have hrc : r c = 0 := by simp [r, t, hzc]
  have hval1 : q.val d = 1 := by
    change (eulerForm D hT).val _ = 1
    rw [eulerForm_val, euler_directing D hT hU, hU.finrank_end]
    rfl
  have hrval : q.val r = 1 := by
    have h := q.val_smul_add_radical z hrad 1 (-t) d
    have h2 : (1 : ℤ) • d + (-t) • z = r := by
      funext i
      simp [r, sub_eq_add_neg]
    rw [h2, hval1] at h
    simpa using h
  have hrb : ∀ a, |r a| ≤ R + 1 := fun a ↦ by
    have h := hRb r hrc hrval a
    rw [abs_le]
    constructor <;> nlinarith
  have hdeq : ∀ a, d a = t * z a + r a := fun a ↦ by
    simp [r]
  have hdnn : ∀ a, 0 ≤ d a := fun a ↦ by simp [d, dimZ]
  have ht : R + 1 < t := by
    by_contra hle
    push Not at hle
    have hsum : (finrank k U : ℤ) = ∑ i, d i := by
      rw [finrank_eq_sum_dimv D.e D.idem D.orth D.sum U]
      push_cast
      rfl
    have hbound : ∀ i, d i ≤ 7 * (R + 1) := fun i ↦ by
      have h1 := abs_le.1 (hrb i)
      have h2 := h6 i
      have h3 := hz i
      have h4 := hdnn c
      have h5 : t * z i ≤ (R + 1) * 6 := by
        calc t * z i ≤ (R + 1) * z i := by
              exact mul_le_mul_of_nonneg_right hle h3.le
          _ ≤ (R + 1) * 6 := by
              exact mul_le_mul_of_nonneg_left h2 (by omega)
      rw [hdeq]
      linarith [h1.2]
    have h1 : ∑ i, d i ≤ ∑ _i : D.ι, 7 * (R + 1) := Finset.sum_le_sum fun i _ ↦ hbound i
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : ((n * (7 * (R + 1)).toNat : ℕ) : ℤ) = n * (7 * (R + 1)) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
    have h3 : ((n * (7 * (R + 1)).toNat : ℕ) : ℤ) < finrank k U := by exact_mod_cast hUb
    rw [h2, hsum] at h3
    have h4 : (Fintype.card D.ι : ℤ) = n := rfl
    rw [h4] at h1
    omega
  -- the minimum
  obtain ⟨x₀, -, hmin⟩ := (Finset.univ : Finset D.ι).exists_min_image
    (fun x ↦ finrank k (eSub U (D.e x))) ⟨c, Finset.mem_univ c⟩
  obtain ⟨x, hxm, hxe⟩ := exists_min_extreme hT hU hs (finrank k (eSub U (D.e x₀)))
    (fun y ↦ hmin y (Finset.mem_univ y)) x₀ rfl
  have hzx : z x = 1 := by
    have h1 := hz x
    by_contra hne
    have h2 : 2 ≤ z x := by omega
    have h3 := abs_le.1 (hrb x)
    have h4 : d x ≤ t := by
      have h5 : finrank k (eSub U (D.e x)) ≤ finrank k (eSub U (D.e c)) := by
        rw [hxm]
        exact hmin c (Finset.mem_univ c)
      have : ((finrank k (eSub U (D.e x)) : ℕ) : ℤ) ≤ (finrank k (eSub U (D.e c)) : ℕ) := by
        exact_mod_cast h5
      exact this
    have h5 : 2 * t ≤ t * z x := by nlinarith
    rw [hdeq] at h4
    linarith [h3.1]
  -- the brick
  let e : D.ι → ℤ := Pi.single x 1
  let w : D.ι → ℤ := z - e
  have hwx : w x = 0 := by simp [w, e, hzx]
  have hwnn : ∀ i, 0 ≤ w i := fun i ↦ by
    by_cases hi : i = x
    · subst hi; rw [hwx]
    · have := hz i
      simp only [w, e, Pi.sub_apply, Pi.single_eq_of_ne hi]
      omega
  have hwval : q.val w = 1 := by
    have h := q.val_sub_single z x
    rw [hval0, hrad] at h
    simpa [w, e] using h
  obtain ⟨y, hy⟩ : ∃ y, y ≠ x := by
    have : 1 < Fintype.card D.ι := by omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 this
    by_cases h : a = x
    · exact ⟨b, fun h' ↦ hab (h.trans h'.symm)⟩
    · exact ⟨a, h⟩
  obtain ⟨V, hV, hmin'⟩ := exists_minEnd (k := k) (D := D) hT (fun i ↦ (w i).toNat)
  have hVw : dimZ D V = w := by
    rw [hV]
    funext i
    exact Int.toNat_of_nonneg (hwnn i)
  have hVx : dimZ D V x = 0 := by rw [hVw, hwx]
  have hrig := rigid_of_minEnd hR hVx hmin'
  have hle := hom_le_euler (D := D) hT hU hs hrig
  have hwe : euler D w w = 1 := by
    rw [← eulerForm_val D hT]
    exact hwval
  have hnt : Nontrivial V := by
    refine nontrivial_of_dimZ (i := y) ?_
    rw [hVw]
    have := hz y
    simp only [w, e, Pi.sub_apply, Pi.single_eq_of_ne hy]
    omega
  have hend1 : finrank k (V →ₗ[A] V) = 1 := by
    have h1 := finrank_end_pos hnt
    rw [hVw, hwe] at hle
    omega
  have hbrick : ∀ φ : V ⟶ V, ∃ c : k, FDMod.lin φ = c • LinearMap.id := by
    have hid : (LinearMap.id : V →ₗ[A] V) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact fun h0 ↦ hv (LinearMap.congr_fun h0 v)
    intro φ
    obtain ⟨c, hc'⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).1 hend1 φ
    exact ⟨c, hc'.symm⟩
  refine ⟨x, V, hbrick, hnt, smul_eq_zero_of_dimZ hVx, ?_⟩
  -- the extensions
  let S := D.simpleM x (hT x)
  have hdS : dimZ D S = e := by
    funext j
    rw [dimZ_simpleM]
    simp [e, Pi.single_apply]
  have hB : euler D w e + euler D e w = -2 := by
    rw [← B_eulerForm hT]
    change q.B w e = -2
    have h1 : q.B w e = q.B z e - q.B e e := q.B_sub_left z e e
    have h2 : q.B e e = 2 := by
      have := q.two_mul_val e
      rw [q.val_single] at this
      omega
    rw [h1, hrad, h2]
    norm_num
  rcases hxe with hsink | hsrc
  · left
    have h1 := euler_sink hT hsink w
    have h3 : euler D e w = w x := h1
    rw [hwx] at h3
    exact two_le_of_euler hT hU hs V S (by rw [hVw, hdS]; omega)
  · right
    have h1 := euler_source hT hsrc w
    have h3 : euler D w e = w x := h1
    rw [hwx] at h3
    exact two_le_of_euler hT hU hs S V (by rw [hVw, hdS]; omega)

end DirData

end LargeIndecomposable.AR
