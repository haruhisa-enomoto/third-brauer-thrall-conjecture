module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.MinimalQuot
public import LargeIndecomposable.UnitForms.Roots

/-!
# Roots from directing modules

Assume all indecomposables of a directed algebra are directing, and that it has a sincere
directing module. Then:

* the Euler form is weakly positive (`eulerForm_weaklyPositive`);
* dimension vectors of indecomposables are roots (`isRoot_dimZ`);
* points with no path between them are orthogonal (`eulerForm_c_eq_zero`);
* thin quotients of projectives exist (`exists_thinQuot`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Endomorphisms of a directing module are scalars.** -/
theorem finrank_end_directing [IsAlgClosed k] {M : FDMod k A} (hM : Directing M) :
    finrank k (M →ₗ[A] M) = 1 := by
  haveI : Nontrivial M := hM.1.2
  refine finrank_eq_one (LinearMap.id : M →ₗ[A] M) (fun h ↦ ?_) fun φ ↦ ?_
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (LinearMap.congr_fun h v)
  · let φk : Module.End k M := φ.restrictScalars k
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φk
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    let ψ : M →ₗ[A] M := φ - c • LinearMap.id
    have hψv : ψ v = 0 := by
      have h1 : φ v = c • v := hv.apply_eq_smul
      change φ v - c • v = 0
      rw [h1, sub_self]
    rcases hM.endo (show M ⟶ M from (FDMod.ofLin ψ)) with h | h
    · refine ⟨c, ?_⟩
      have : ψ = 0 := h
      exact (sub_eq_zero.1 this).symm
    · exact absurd (h.1 (hψv.trans (map_zero ψ).symm)) hv.2

namespace DirData

variable {D : DirData k A}

/-- `C⁻¹` vanishes off the path order. -/
lemma cartan_inv_eq_zero (hT : ∀ x, x ∈ D.T) (a : D.ι) : ∀ b,
    ¬Relation.ReflTransGen D.Arr a b → (cartan D)⁻¹ b a = 0 := by
  classical
  haveI : IsTrans D.ι (Relation.TransGen D.Arr) := ⟨fun _ _ _ ↦ Relation.TransGen.trans⟩
  haveI : Std.Irrefl (Relation.TransGen D.Arr) :=
    ⟨fun x h ↦ D.acyc x x h Relation.ReflTransGen.refl⟩
  have hwf : WellFounded (Relation.TransGen D.Arr) := Finite.wellFounded_of_trans_of_irrefl _
  intro b
  induction b using hwf.induction with
  | _ b ih =>
    intro hb
    have hab : b ≠ a := by
      rintro rfl
      exact hb Relation.ReflTransGen.refl
    have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
    have h1 : (cartan D * (cartan D)⁻¹) b a = 0 := by
      rw [mul_nonsing_inv _ hu, Matrix.one_apply_ne hab]
    rw [Matrix.mul_apply, Finset.sum_eq_single b, cartan_diag D (hT b), one_mul] at h1
    · exact h1
    · intro i _ hi
      by_cases hr : Relation.ReflTransGen D.Arr i b
      · have htr := D.transGen_of_ne hr hi
        rw [ih i htr fun h ↦ hb (h.trans hr), mul_zero]
      · rw [cartan_eq_zero D hr, zero_mul]
    · simp

/-- **Points with no path between them are orthogonal.** -/
theorem eulerForm_c_eq_zero (hT : ∀ x, x ∈ D.T) {a b : D.ι}
    (h1 : ¬Relation.ReflTransGen D.Arr a b) (h2 : ¬Relation.ReflTransGen D.Arr b a) :
    (eulerForm D hT).c a b = 0 := by
  change (cartan D)⁻¹ b a + (cartan D)⁻¹ a b = 0
  rw [cartan_inv_eq_zero hT a b h1, cartan_inv_eq_zero hT b a h2, add_zero]

lemma dimZ_nonneg (M : FDMod k A) (i : D.ι) : 0 ≤ dimZ D M i := Int.natCast_nonneg _

lemma dimZ_ne_zero {M : FDMod k A} {x : D.ι} {n : M} (hn : D.e x • n ≠ 0) : dimZ D M x ≠ 0 := by
  intro h
  exact hn (smul_eq_zero_of_dimZ h n)

/-- Dimension vectors of nonzero modules are positive. -/
lemma pos_dimZ {M : FDMod k A} (hM : Nontrivial M) : Forms.UnitForm.Pos (dimZ D M) := by
  refine ⟨dimZ_nonneg M, fun h ↦ ?_⟩
  obtain ⟨x, n, hn⟩ := exists_e_smul_ne D hM
  exact dimZ_ne_zero hn (congrFun h x)

variable {U : FDMod k A}

/-- **The Euler form is weakly positive.** -/
theorem eulerForm_weaklyPositive (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    (hDir : ∀ N : FDMod k A, IndNT N → Directing N) : (eulerForm D hT).WeaklyPositive := by
  intro x hx
  rw [eulerForm_val]
  obtain ⟨V, hV, hmin⟩ := exists_minEnd (k := k) (D := D) hT (fun i ↦ (x i).toNat)
  have hVx : dimZ D V = x := by
    rw [hV]
    funext i
    exact Int.toNat_of_nonneg (hx.1 i)
  have hrig : ExtVanish V V :=
    extVanish_of_minEnd (dimZ D) (fun L M N f g hf hg hex ↦ dimZ_exact D f g hf hg hex)
      (fun M h1 h2 ↦ (hDir M ⟨h1, h2⟩).extVanish) V hmin
  have h1 := hom_le_euler (D := D) hT hU hs hrig
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx.2 (funext h)
  have hnt : Nontrivial V := nontrivial_of_dimZ (i := i) (by rwa [hVx])
  have h2 := finrank_end_pos hnt
  rw [hVx] at h1
  omega

/-- **Dimension vectors of directing modules are roots.** -/
theorem isRoot_dimZ [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) {N : FDMod k A} (hN : Directing N) :
    (eulerForm D hT).IsRoot (dimZ D N) := by
  refine ⟨pos_dimZ hN.1.2, ?_⟩
  rw [eulerForm_val, euler_directing D hT hN, finrank_end_directing hN]
  norm_num

/-- The kernel of a thin quotient. -/
def thinKer (x : D.ι) (E : Set D.ι)
    (hcl : ∀ c c', c ∉ E → c' ∈ E → ∀ u v : A, D.e c' * u * (D.e c * v * D.e x) = 0) :
    Submodule A (projE (k := k) (D.idem x)) where
  carrier := {m | ∀ c ∈ E, D.e c * (m : A) = 0}
  add_mem' {m n} hm hn c hc := by
    change D.e c * ((m : A) + n) = 0
    rw [mul_add, hm c hc, hn c hc, add_zero]
  zero_mem' c _ := mul_zero _
  smul_mem' a m hm c' hc' := by
    classical
    change D.e c' * (a * (m : A)) = 0
    have hm1 : (m : A) * D.e x = m := m.2
    have h1 : a * (m : A) = ∑ c, a * (D.e c * (m : A)) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, D.sum, one_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hc : c ∈ E
    · rw [hm c hc, mul_zero, mul_zero]
    · have h2 := hcl c c' hc hc' a (m : A)
      rw [mul_assoc (D.e c), hm1] at h2
      rw [← mul_assoc]
      exact h2

/-- **Thin quotients of projectives.** -/
theorem exists_thinQuot (hT : ∀ x, x ∈ D.T) (hC : ∀ x y, cartan D y x ≤ 1) (x : D.ι) (E : Set D.ι)
    (hxE : x ∈ E) (hne : ∀ c ∈ E, ∃ a : A, D.e c * a * D.e x ≠ 0)
    (hcl : ∀ c c', c ∉ E → c' ∈ E → ∀ u v : A, D.e c' * u * (D.e c * v * D.e x) = 0) :
    ∃ N : FDMod k A, IndNT N ∧ (∀ c ∈ E, dimZ D N c = 1) ∧ ∀ c, c ∉ E → dimZ D N c = 0 := by
  classical
  let P := projE (k := k) (D.idem x)
  let L : Submodule A P := thinKer x E hcl
  let N : FDMod k A := FDMod.ofQuot P L
  have hgen : L.mkQ (genP (k := k) x) ≠ 0 := by
    intro h
    have h1 : genP (k := k) x ∈ L := (Submodule.Quotient.mk_eq_zero L).1 h
    have h2 : D.e x * D.e x = 0 := h1 x hxE
    rw [(D.idem x).eq] at h2
    exact D.ne x (hT x) h2
  have hnt : Nontrivial N := ⟨⟨_, 0, hgen⟩⟩
  refine ⟨N, ⟨isIndecMod_of_brick (quot_brick (hT x) L), hnt⟩, fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- the piece at a point of `E`
    obtain ⟨a, ha⟩ := hne c hc
    let f : eSub P (D.e c) →ₗ[k] eSub N (D.e c) := eSubMap D.e (show P ⟶ N from (FDMod.ofLin L.mkQ)) c
    have hfi : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).2 fun p hp ↦ ?_
      have h1 : (p : P) ∈ L := (Submodule.Quotient.mk_eq_zero L).1 (congrArg Subtype.val hp)
      have h2 : D.e c * (((p : P) : leftIdeal (D.idem x)) : A) = 0 := h1 c hc
      have h3 : D.e c • (p : P) = p := p.2
      apply Subtype.ext
      rw [← h3]
      exact Subtype.ext h2
    have hfs : Function.Surjective f := by
      rintro ⟨m, hm⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective L m
      refine ⟨⟨D.e c • p, ?_⟩, Subtype.ext ?_⟩
      · change D.e c • (D.e c • p) = D.e c • p
        rw [← mul_smul, (D.idem c).eq]
      · change L.mkQ (D.e c • p) = L.mkQ p
        rw [map_smul]
        exact hm
    have h1 : finrank k (eSub N (D.e c)) = finrank k (eSub P (D.e c)) :=
      (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).finrank_eq.symm
    have h2 : (finrank k (eSub P (D.e c)) : ℤ) ≤ 1 := hC x c
    have hpos : 0 < finrank k (eSub P (D.e c)) := by
      have hw : (⟨D.e c * a * D.e x, by
        change D.e c * a * D.e x * D.e x = _
        rw [mul_assoc, D.e_mul_e]⟩ : P) ∈ eSub P (D.e c) := by
        apply Subtype.ext
        change D.e c * (D.e c * a * D.e x) = _
        rw [← mul_assoc, ← mul_assoc, (D.idem c).eq]
      haveI : Nontrivial (eSub P (D.e c)) :=
        ⟨⟨⟨_, hw⟩, 0, fun h ↦ ha (congrArg (fun z : eSub P (D.e c) ↦ (((z : P) : leftIdeal
          (D.idem x)) : A)) h)⟩⟩
      exact finrank_pos
    change (finrank k (eSub N (D.e c)) : ℤ) = 1
    rw [h1]
    omega
  · have h0 : eSub N (D.e c) = ⊥ := by
      refine eq_bot_iff.2 fun m hm ↦ (Submodule.mem_bot k).2 ?_
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective L m
      have hm' : D.e c • L.mkQ p = L.mkQ p := hm
      rw [← hm', ← map_smul]
      refine (Submodule.Quotient.mk_eq_zero L).2 fun c' hc' ↦ ?_
      have hne' : c' ≠ c := fun h ↦ hc (h ▸ hc')
      change D.e c' * (D.e c * (p : A)) = 0
      rw [← mul_assoc, D.orth c' c hne', zero_mul]
    change (finrank k (eSub N (D.e c)) : ℤ) = 0
    rw [h0, finrank_bot]
    rfl

/-- The indicator vector of a set of points. -/
def ind {ι : Type} (E : Set ι) : ι → ℤ := by
  classical
  exact fun c ↦ if c ∈ E then 1 else 0

lemma ind_of_mem {ι : Type} {E : Set ι} {c : ι} (h : c ∈ E) : ind E c = 1 := by
  simp [ind, h]

lemma ind_of_not_mem {ι : Type} {E : Set ι} {c : ι} (h : c ∉ E) : ind E c = 0 := by
  simp [ind, h]

lemma ind_nonneg {ι : Type} (E : Set ι) (c : ι) : 0 ≤ ind E c := by
  classical
  by_cases h : c ∈ E
  · rw [ind_of_mem h]; norm_num
  · rw [ind_of_not_mem h]

lemma ind_union {ι : Type} {E F : Set ι} (h : ∀ c, c ∈ E → c ∉ F) :
    ind (E ∪ F) = ind E + ind F := by
  classical
  funext c
  by_cases h1 : c ∈ E
  · simp [ind_of_mem (Set.mem_union_left F h1), ind_of_mem h1, ind_of_not_mem (h c h1)]
  · by_cases h2 : c ∈ F
    · simp [ind_of_mem (Set.mem_union_right E h2), ind_of_not_mem h1, ind_of_mem h2]
    · have h3 : c ∉ E ∪ F := by simp [h1, h2]
      simp [ind_of_not_mem h1, ind_of_not_mem h2, ind_of_not_mem h3]

lemma ind_insert {ι : Type} [DecidableEq ι] {E : Set ι} {a : ι} (h : a ∉ E) :
    ind (insert a E) = Pi.single a 1 + ind E := by
  classical
  have h1 : insert a E = {a} ∪ E := Set.insert_eq a E
  rw [h1, ind_union (by rintro c rfl; exact h)]
  congr 1
  funext c
  by_cases hc : c = a
  · subst hc; simp [ind_of_mem]
  · simp [ind_of_not_mem (show c ∉ ({a} : Set ι) from hc), Pi.single_eq_of_ne hc]

/-- The data of a thin quotient of a projective. -/
structure Thin (D : DirData k A) (x : D.ι) (E : Set D.ι) : Prop where
  mem : x ∈ E
  ne : ∀ c ∈ E, ∃ a : A, D.e c * a * D.e x ≠ 0
  cl : ∀ c c', c ∉ E → c' ∈ E → ∀ u v : A, D.e c' * u * (D.e c * v * D.e x) = 0

/-- A polygon in a directed algebra. -/
structure Poly (D : DirData k A) (κ : Type) where
  /-- The source. -/
  a : D.ι
  /-- The sink. -/
  b : D.ι
  hab : a ≠ b
  /-- The first points of the arms. -/
  n : κ → D.ι
  /-- The arms. -/
  arm : κ → Set D.ι
  two : ∃ i j : κ, i ≠ j
  a_arm : ∀ j, a ∉ arm j
  b_arm : ∀ j, b ∉ arm j
  disj : ∀ i j, i ≠ j → ∀ c, c ∈ arm i → c ∉ arm j
  th1 : ∀ j, Thin D (n j) (arm j)
  th2 : ∀ j, Thin D (n j) (insert b (arm j))
  th3 : ∀ j, Thin D a (insert a (arm j))
  th4 : ∀ i j, i ≠ j → Thin D a (insert a (arm i ∪ arm j))
  th5 : Thin D a (insert a (insert b (⋃ j, arm j)))

/-- The points of a polygon. -/
def Poly.H {κ : Type} (P : Poly D κ) : Set D.ι := insert P.a (insert P.b (⋃ j, P.arm j))

section Anchors

variable [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hC : ∀ x y, cartan D y x ≤ 1)
  (hDir : ∀ N : FDMod k A, IndNT N → Directing N)
include hT hC hDir

/-- Thin sets give roots. -/
theorem isRoot_ind {x : D.ι} {E : Set D.ι} (h : Thin D x E) :
    (eulerForm D hT).IsRoot (ind E) := by
  obtain ⟨N, hN, h1, h0⟩ := exists_thinQuot hT hC x E h.mem h.ne h.cl
  have : dimZ D N = ind E := by
    funext c
    by_cases hc : c ∈ E
    · rw [h1 c hc, ind_of_mem hc]
    · rw [h0 c hc, ind_of_not_mem hc]
  rw [← this]
  exact isRoot_dimZ hT (hDir N hN)

/-- A pairing from a sum of two roots. -/
lemma B_of_sum {x y s : D.ι → ℤ} (hx : (eulerForm D hT).val x = 1)
    (hy : (eulerForm D hT).val y = 1) (hs : (eulerForm D hT).IsRoot s) (e : s = x + y) :
    (eulerForm D hT).B x y = -1 := by
  have h := (eulerForm D hT).val_add x y
  rw [← e, hs.2, hx, hy] at h
  omega

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **The anchor of a polygon.** -/
def Poly.anchor (P : Poly D κ) : Forms.UnitForm.Anchor (eulerForm D hT) κ where
  a := P.a
  b := P.b
  r j := ind (P.arm j)
  root_r j := isRoot_ind hT hC hDir (P.th1 j)
  B_a j := by
    refine B_of_sum hT hC hDir ((eulerForm D hT).val_single _)
      (isRoot_ind hT hC hDir (P.th1 j)).2 (isRoot_ind hT hC hDir (P.th3 j)) ?_
    exact ind_insert (P.a_arm j)
  B_b j := by
    obtain h := isRoot_ind hT hC hDir (P.th2 j)
    refine B_of_sum hT hC hDir ((eulerForm D hT).val_single _)
      (isRoot_ind hT hC hDir (P.th1 j)).2 h ?_
    exact ind_insert (P.b_arm j)
  B_r i j hij := by
    have h1 := isRoot_ind hT hC hDir (P.th3 i)
    have h2 := isRoot_ind hT hC hDir (P.th4 i j hij)
    have h3 := isRoot_ind hT hC hDir (P.th1 j)
    have hd : ∀ c, c ∈ insert P.a (P.arm i) → c ∉ P.arm j := by
      rintro c (rfl | hc)
      · exact P.a_arm j
      · exact P.disj i j hij c hc
    have e : ind (insert P.a (P.arm i ∪ P.arm j)) = ind (insert P.a (P.arm i)) + ind (P.arm j) := by
      have : insert P.a (P.arm i ∪ P.arm j) = insert P.a (P.arm i) ∪ P.arm j := by
        rw [Set.insert_union]
      rw [this]
      exact ind_union hd
    have h4 := B_of_sum hT hC hDir h1.2 h3.2 h2 e
    have h5 : (eulerForm D hT).B (Pi.single P.a 1) (ind (P.arm j)) = -1 := by
      refine B_of_sum hT hC hDir ((eulerForm D hT).val_single _) h3.2
        (isRoot_ind hT hC hDir (P.th3 j)) ?_
      exact ind_insert (P.a_arm j)
    have h6 : ind (insert P.a (P.arm i)) = Pi.single P.a 1 + ind (P.arm i) :=
      ind_insert (P.a_arm i)
    rw [h6, Forms.UnitForm.B_add_left, h5] at h4
    omega
  two := P.two

/-- The thin vector of a polygon. -/
lemma Poly.anchor_t (P : Poly D κ) : (P.anchor hT hC hDir).t = ind P.H := by
  have hu : ∀ S : Finset κ, ∑ j ∈ S, ind (P.arm j) = ind (⋃ j ∈ S, P.arm j) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      funext c
      simp [ind_of_not_mem]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, ih, Finset.set_biUnion_insert]
      refine (ind_union ?_).symm
      intro c hc hc'
      obtain ⟨j, hj, hcj⟩ := Set.mem_iUnion₂.1 hc'
      exact P.disj a j (fun h ↦ ha (h ▸ hj)) c hc hcj
  have h1 : (P.anchor hT hC hDir).t = Pi.single P.a 1 + Pi.single P.b 1 + ind (⋃ j, P.arm j) := by
    change Pi.single P.a 1 + Pi.single P.b 1 + ∑ j, ind (P.arm j) = _
    rw [hu Finset.univ]
    simp
  have hb : P.b ∉ ⋃ j, P.arm j := by
    simp only [Set.mem_iUnion, not_exists]
    exact P.b_arm
  have ha : P.a ∉ insert P.b (⋃ j, P.arm j) := by
    simp only [Set.mem_insert_iff, Set.mem_iUnion, not_or, not_exists]
    exact ⟨P.hab, P.a_arm⟩
  rw [h1, Poly.H, ind_insert ha, ind_insert hb, add_assoc]

variable {U : FDMod k A} (hU : Directing U) (hs : Sincere D U)
include hU hs

/-- **Two orthogonal polygons cannot live in a sincere directing module.** -/
theorem false_of_two_polys {κ' : Type} [Fintype κ'] [DecidableEq κ'] (P : Poly D κ) (P' : Poly D κ')
    (horth : ∀ k' ∈ P.H, ∀ l ∈ P'.H, ¬Relation.ReflTransGen D.Arr k' l ∧
      ¬Relation.ReflTransGen D.Arr l k') : False := by
  have hw := eulerForm_weaklyPositive hT hU hs hDir
  have h1 : Thin D P.a P.H := P.th5
  have h2 : Thin D P'.a P'.H := P'.th5
  have hne : ∀ c, 1 ≤ dimZ D U c := fun c ↦ by
    obtain ⟨u, hu⟩ := hs c
    have h3 := dimZ_ne_zero hu
    have h4 := dimZ_nonneg (D := D) U c
    omega
  refine Forms.UnitForm.false_of_anchors hw (P.anchor hT hC hDir) (P'.anchor hT hC hDir) ?_ ?_
    (isRoot_dimZ hT hU) ?_ ?_
  · rw [P.anchor_t hT hC hDir]
    exact (isRoot_ind hT hC hDir h1).2
  · rw [P'.anchor_t hT hC hDir]
    exact (isRoot_ind hT hC hDir h2).2
  · intro c
    rw [P.anchor_t hT hC hDir, P'.anchor_t hT hC hDir]
    by_cases h3 : c ∈ P.H
    · have h4 : c ∉ P'.H := fun h ↦ (horth c h3 c h).1 Relation.ReflTransGen.refl
      rw [ind_of_mem h3, ind_of_not_mem h4]
      have := hne c
      omega
    · rw [ind_of_not_mem h3, zero_add]
      by_cases h4 : c ∈ P'.H
      · rw [ind_of_mem h4]; exact hne c
      · rw [ind_of_not_mem h4]; exact dimZ_nonneg U c
  · intro c l hc hl
    rw [P.anchor_t hT hC hDir] at hc
    rw [P'.anchor_t hT hC hDir] at hl
    have h3 : c ∈ P.H := by
      by_contra h
      rw [ind_of_not_mem h] at hc
      exact lt_irrefl _ hc
    have h4 : l ∈ P'.H := by
      by_contra h
      rw [ind_of_not_mem h] at hl
      exact lt_irrefl _ hl
    exact eulerForm_c_eq_zero hT (horth c h3 l h4).1 (horth c h3 l h4).2

end Anchors

end DirData

end LargeIndecomposable.AR
