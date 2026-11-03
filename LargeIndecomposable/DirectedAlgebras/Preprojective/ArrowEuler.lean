module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.CriticalAbstract

/-!
# Roots off a point are bricks

Let `D` be a directed algebra with a sincere directing module whose indecomposables killed by
any `e_i` are rigid (`RigidOff`). A module of minimal endomorphism dimension with dimension
vector `x ≥ 0`, `x_a = 0`, is rigid (`rigid_of_minEnd`), so `dim End ≤ ⟨x, x⟩`
(`hom_le_euler`). Hence a root off a point is the dimension vector of a module with
one-dimensional endomorphism algebra (`exists_brick_off`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {U : FDMod k A}

/-- **A root off a point is the dimension vector of a brick.** -/
theorem exists_brick_off (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    (hR : RigidOff D) (a : D.ι) (x : D.ι → ℤ) (hx : Forms.UnitForm.Pos x) (hxa : x a = 0)
    (h1 : euler D x x = 1) :
    ∃ V : FDMod k A, dimZ D V = x ∧ finrank k (V →ₗ[A] V) = 1 := by
  obtain ⟨V, hV, hmin⟩ := exists_minEnd (k := k) (D := D) hT (fun i ↦ (x i).toNat)
  have hVx : dimZ D V = x := by
    rw [hV]
    funext i
    exact Int.toNat_of_nonneg (hx.1 i)
  have hVa : dimZ D V a = 0 := by rw [hVx, hxa]
  have hrig := rigid_of_minEnd hR hVa hmin
  have hle := hom_le_euler (D := D) hT hU hs hrig
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx.2 (funext h)
  have hnt : Nontrivial V := nontrivial_of_dimZ (i := i) (by rwa [hVx])
  have hpos := finrank_end_pos hnt
  rw [hVx, h1] at hle
  exact ⟨V, hVx, by omega⟩

section Arrow

variable (D : DirData k A) {a b : D.ι}

/-- The part of `Ae_a` away from `a` and `b`. -/
def arrowSub (hdir : ∀ y, y ≠ a → ∀ c d : A, D.e a * c * D.e y * d * D.e a = 0)
    (hirr : ∀ y, y ≠ a → y ≠ b → ∀ c d : A, D.e b * c * D.e y * d * D.e a = 0) :
    Submodule A (projE (k := k) (D.idem a)) where
  carrier := {m | D.e a • m = 0 ∧ D.e b • m = 0}
  add_mem' {m n} hm hn := ⟨by rw [smul_add, hm.1, hn.1, add_zero], by
    rw [smul_add, hm.2, hn.2, add_zero]⟩
  zero_mem' := ⟨smul_zero _, smul_zero _⟩
  smul_mem' c m hm := by
    have key : ∀ z, (z = a ∨ z = b) → D.e z • (c • m) = 0 := by
      intro z hz
      apply Subtype.ext
      change D.e z * (c * (m : A)) = 0
      have hm' : (m : A) * D.e a = m := m.2
      have hdec : (m : A) = ∑ y, D.e y * m := by rw [← Finset.sum_mul, D.sum, one_mul]
      rw [hdec, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      by_cases hya : y = a
      · subst hya
        have : D.e y * (m : A) = 0 := congrArg Subtype.val hm.1
        rw [this, mul_zero, mul_zero]
      by_cases hyb : y = b
      · subst hyb
        have : D.e y * (m : A) = 0 := congrArg Subtype.val hm.2
        rw [this, mul_zero, mul_zero]
      rcases hz with rfl | rfl
      · rw [← hm', show D.e z * (c * (D.e y * (m * D.e z))) = D.e z * c * D.e y * m * D.e z by
          noncomm_ring]
        exact hdir y hya c m
      · rw [← hm', show D.e z * (c * (D.e y * (m * D.e a))) = D.e z * c * D.e y * m * D.e a by
          noncomm_ring]
        exact hirr y hya hyb c m
    exact ⟨key a (Or.inl rfl), key b (Or.inr rfl)⟩

variable (hdir : ∀ y, y ≠ a → ∀ c d : A, D.e a * c * D.e y * d * D.e a = 0)
  (hirr : ∀ y, y ≠ a → y ≠ b → ∀ c d : A, D.e b * c * D.e y * d * D.e a = 0)

/-- **The arrow module** `Ae_a / (part away from a and b)`. -/
abbrev arrowMod : FDMod k A := FDMod.ofQuot (projE (k := k) (D.idem a)) (D.arrowSub hdir hirr)

/-- At a point `y ∉ {a, b}` the arrow module vanishes. -/
lemma arrowMod_eSub_out {y : D.ι} (hya : y ≠ a) (hyb : y ≠ b) :
    finrank k (eSub (D.arrowMod hdir hirr) (D.e y)) = 0 := by
  rw [Submodule.finrank_eq_zero, eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_bot]
  have hx' : D.e y • x = x := hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hmem : D.e y • m ∈ D.arrowSub hdir hirr := by
    exact ⟨by rw [← mul_smul, D.orth a y (Ne.symm hya), zero_smul],
      by rw [← mul_smul, D.orth b y (Ne.symm hyb), zero_smul]⟩
  rw [← hx', ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2 hmem]

/-- The quotient map on corners. -/
def arrowCornerMap (y : D.ι) :
    eSub (projE (k := k) (D.idem a)) (D.e y) →ₗ[k] eSub (D.arrowMod hdir hirr) (D.e y) :=
  ((D.arrowSub hdir hirr).mkQ.restrictScalars k).restrict fun m (hm : D.e y • m = m) ↦ by
    change D.e y • Submodule.Quotient.mk m = Submodule.Quotient.mk m
    rw [← Submodule.Quotient.mk_smul, hm]

lemma arrowCornerMap_apply (y : D.ι) (m : eSub (projE (k := k) (D.idem a)) (D.e y)) :
    ((D.arrowCornerMap hdir hirr y m : eSub (D.arrowMod hdir hirr) (D.e y)) :
      D.arrowMod hdir hirr) = Submodule.Quotient.mk (m : projE (k := k) (D.idem a)) := rfl

/-- At `y ∈ {a, b}` the arrow module is the corner of `Ae_a`. -/
lemma arrowCornerMap_bijective {y : D.ι} (hy : y = a ∨ y = b) :
    Function.Bijective (D.arrowCornerMap hdir hirr y) := by
  refine ⟨fun m n hmn ↦ ?_, fun x ↦ ?_⟩
  · have h := congrArg Subtype.val hmn
    rw [arrowCornerMap_apply, arrowCornerMap_apply, Submodule.Quotient.eq] at h
    obtain ⟨h1, h2⟩ := h
    have hz : D.e y • ((m : projE (k := k) (D.idem a)) - n) = 0 := by
      rcases hy with rfl | rfl
      · exact h1
      · exact h2
    have hm : D.e y • (m : projE (k := k) (D.idem a)) = m := m.2
    have hn : D.e y • (n : projE (k := k) (D.idem a)) = n := n.2
    rw [smul_sub, hm, hn, sub_eq_zero] at hz
    exact Subtype.ext hz
  · obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x : D.arrowMod hdir hirr)
    have hx : D.e y • (x : D.arrowMod hdir hirr) = x := x.2
    refine ⟨⟨D.e y • m, by
      change D.e y • (D.e y • m) = D.e y • m
      rw [← mul_smul, (D.idem y).eq]⟩, Subtype.ext ?_⟩
    rw [arrowCornerMap_apply]
    change Submodule.Quotient.mk (D.e y • m) = _
    rw [Submodule.Quotient.mk_smul, hm, hx]

include hdir hirr in
lemma dimZ_arrowMod (hab : a ≠ b) (haa : cartan D a a = 1) (hba : cartan D b a = 1) :
    dimZ D (D.arrowMod hdir hirr) = Pi.single a 1 + Pi.single b 1 := by
  funext y
  simp only [dimZ, dimv, Pi.add_apply, Pi.single_apply]
  by_cases hya : y = a
  · subst hya
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective _
      (D.arrowCornerMap_bijective hdir hirr (Or.inl rfl)))]
    have : (cartan D y y : ℤ) = finrank k (eSub (projE (k := k) (D.idem y)) (D.e y)) := rfl
    rw [if_pos rfl, if_neg hab, ← this, haa]; rfl
  by_cases hyb : y = b
  · subst hyb
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective _
      (D.arrowCornerMap_bijective hdir hirr (Or.inr rfl)))]
    have : (cartan D y a : ℤ) = finrank k (eSub (projE (k := k) (D.idem a)) (D.e y)) := rfl
    rw [if_neg hya, if_pos rfl, ← this, hba]; rfl
  · rw [D.arrowMod_eSub_out hdir hirr hya hyb, if_neg hya, if_neg hyb]; rfl

/-- The generator `e_a` of the arrow module. -/
def arrowGen : D.arrowMod hdir hirr :=
  Submodule.Quotient.mk (⟨D.e a, e_mem (D.idem a)⟩ : projE (k := k) (D.idem a))

lemma arrowGen_smul (m : projE (k := k) (D.idem a)) :
    (m : A) • D.arrowGen hdir hirr = Submodule.Quotient.mk m := by
  rw [arrowGen, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext m.2

lemma arrowGen_mem : D.e a • D.arrowGen hdir hirr = D.arrowGen hdir hirr := by
  rw [arrowGen, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (D.idem a).eq

include hdir hirr in
/-- **The arrow module is a brick.** -/
lemma arrowMod_brick (ha : a ∈ D.T) (haa : cartan D a a = 1)
    (φ : D.arrowMod hdir hirr ⟶ D.arrowMod hdir hirr) :
    ∃ c : k, FDMod.lin φ = c • LinearMap.id := by
  set g := D.arrowGen hdir hirr with hgdef
  have hg : D.e a • g = g := D.arrowGen_mem hdir hirr
  have hφg : D.e a • FDMod.lin φ g = FDMod.lin φ g := by rw [← map_smul, hg]
  have h1 : finrank k (eSub (D.arrowMod hdir hirr) (D.e a)) = 1 := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective _
      (D.arrowCornerMap_bijective hdir hirr (Or.inl rfl)))]
    have e2 : ((finrank k (eSub (projE (k := k) (D.idem a)) (D.e a)) : ℕ) : ℤ) = 1 := haa
    exact_mod_cast e2
  have hea : (⟨⟨D.e a, e_mem (D.idem a)⟩, by
      change D.e a • (⟨D.e a, e_mem (D.idem a)⟩ : projE (k := k) (D.idem a)) = _
      exact Subtype.ext (D.idem a).eq⟩ : eSub (projE (k := k) (D.idem a)) (D.e a)) ≠ 0 := by
    intro h0
    exact D.ne a ha (congrArg (fun z : eSub (projE (k := k) (D.idem a)) (D.e a) ↦ ((z : _) : A)) h0)
  have hg0 : (⟨g, hg⟩ : eSub (D.arrowMod hdir hirr) (D.e a)) ≠ 0 := by
    intro h0
    apply hea
    apply (D.arrowCornerMap_bijective hdir hirr (Or.inl rfl)).1
    rw [map_zero]
    exact Subtype.ext (congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hg0).1 h1 ⟨FDMod.lin φ g, hφg⟩
  have hc' : c • g = FDMod.lin φ g := congrArg Subtype.val hc
  refine ⟨c, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← arrowGen_smul, map_smul, ← hc', LinearMap.smul_apply, LinearMap.id_apply, smul_comm]

include hdir hirr in
/-- **An arrow gives a full edge**: if all indecomposables are directing, then for an element of
`e_b A e_a` that does not factor through other points, `q_ab = -1`. -/
theorem eulerForm_c_arrow (hT : ∀ x, x ∈ D.T) (hdirAll : ∀ N : FDMod k A, IndNT N → Directing N)
    (hab : a ≠ b) (hba : cartan D b a = 1) : (eulerForm D hT).c a b = -1 := by
  classical
  have haa : cartan D a a = 1 := cartan_diag D (hT a)
  set M := D.arrowMod hdir hirr
  have hdim := D.dimZ_arrowMod hdir hirr hab haa hba
  have hbrick := D.arrowMod_brick hdir hirr (hT a) haa
  have hnt : Nontrivial M := nontrivial_of_dimZ (D := D) (i := a) (by
    rw [hdim]; simp [Pi.single_apply, hab])
  have hind : IndNT M := ⟨isIndecMod_of_brick hbrick, hnt⟩
  have hend : finrank k (M →ₗ[A] M) = 1 := by
    have hid : (LinearMap.id : M →ₗ[A] M) ≠ 0 := by
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      intro h0
      exact hm (LinearMap.congr_fun h0 m)
    refine (finrank_eq_one_iff_of_nonzero' _ hid).2 fun φ ↦ ?_
    obtain ⟨c, hc⟩ := hbrick (FDMod.ofLin φ)
    exact ⟨c, hc.symm⟩
  have he := euler_directing D hT (hdirAll M hind)
  rw [hend, hdim, ← eulerForm_val D hT] at he
  have e2 := (eulerForm D hT).two_mul_val (Pi.single a 1 + Pi.single b 1)
  rw [he] at e2
  rw [Forms.UnitForm.B_add_left, Forms.UnitForm.B_add_right, Forms.UnitForm.B_add_right,
    Forms.UnitForm.B_single_single, Forms.UnitForm.B_single_single,
    Forms.UnitForm.B_single_single, Forms.UnitForm.B_single_single, (eulerForm D hT).diag,
    (eulerForm D hT).diag, (eulerForm D hT).symm b a] at e2
  push_cast at e2
  linarith

end Arrow

end DirData

end LargeIndecomposable.AR
