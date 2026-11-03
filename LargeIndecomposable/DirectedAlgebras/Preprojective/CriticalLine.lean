module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.BrickOff
public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerInterval
public import LargeIndecomposable.DirectedAlgebras.Directing.SupportSplit
public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereGraph
public import LargeIndecomposable.Modules.Homological.Restrict
public import LargeIndecomposable.UnitForms.DTildeGraph
public import LargeIndecomposable.UnitForms.Roots

/-!
# A line in a critical quotient

Let `D` be a directed algebra whose arrows join points with no third point between them, with
one-dimensional corners. Let `Λ = D / ⟨e_v : v ∉ T'⟩` have a critical Euler form in at least ten
variables, rigid modules off each point and a sincere directing module. The Euler form has an
induced path through all points of `T'` but two (`UnitForm.Critical.longPath`). Along it:

* consecutive points are joined by an arrow of `D`: a brick of dimension vector `e_a + e_b`
  exists (`exists_brick_off`), and without an arrow its support would split
  (`not_isIndecMod_of_split`);
* other points are not joined by an arrow: an arrow is a full edge (`eulerForm_c_quot_interval`);
* the brick with dimension vector the indicator of the path, restricted to `D`, is an
  indecomposable `D`-module with one-dimensional spaces on the path, zero elsewhere, and every
  arrow of the path acts on it (again by `not_isIndecMod_of_split`).

This is `exists_critical_line`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {T' : Set D.ι} (hsub : T' ⊆ D.T)

/-- On the restriction of a quotient module, `e_x` acts as its image. -/
lemma res_e_smul (V : FDMod k (D.QAlg T')) (x : D.ι) (w : resFD (D.qmap T') V) :
    toX (D.e x • w) = D.qmap T' (D.e x) • toX w := rfl

/-- Points with no space act by zero on the restriction. -/
lemma res_smul_eq_zero (V : FDMod k (D.QAlg T')) (x : D.ι)
    (h : ∀ hx : x ∈ T', dimZ (D.quotAny hsub) V ⟨x, hx⟩ = 0) (w : resFD (D.qmap T') V) :
    D.e x • w = 0 := by
  by_cases hx : x ∈ T'
  · have := smul_eq_zero_of_dimZ (D := D.quotAny hsub) (h hx) (toX w)
    exact this
  · change D.qmap T' (D.e x) • toX w = 0
    rw [D.qmap_e_out T' hx, zero_smul]

/-- The spaces of the restriction at points of `T'`. -/
lemma finrank_eSub_res (V : FDMod k (D.QAlg T')) {x : D.ι} (hx : x ∈ T') :
    finrank k (eSub (resFD (D.qmap T') V) (D.e x)) =
      finrank k (eSub V ((D.quotAny hsub).e ⟨x, hx⟩)) := by
  refine LinearEquiv.finrank_eq
    { toFun := fun m ↦ ⟨toX (m : resFD (D.qmap T') V), m.2⟩
      invFun := fun m ↦ ⟨ofX (m : V), m.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

end DirData

end LargeIndecomposable.AR

namespace LargeIndecomposable.Forms.UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : UnitForm ι}

/-- The indicator vector of the first `m` points of a sequence. -/
def pathVec (P : ℕ → ι) (m : ℕ) : ι → ℤ := ∑ i ∈ Finset.range m, Pi.single (P i) 1

/-- **The indicator of an induced path is a root.** -/
lemma val_pathVec {P : ℕ → ι} {M : ℕ}
    (hc : ∀ k, k + 1 < M → q.c (P k) (P (k + 1)) = -1)
    (h0 : ∀ k l, l < M → k + 2 ≤ l → q.c (P k) (P l) = 0) :
    ∀ m, m + 1 ≤ M → q.val (pathVec P (m + 1)) = 1 := by
  intro m
  induction m with
  | zero => intro _; simp [pathVec, val_single]
  | succ m ih =>
    intro hm
    have e : pathVec P (m + 1 + 1) = pathVec P (m + 1) + Pi.single (P (m + 1)) 1 := by
      simp [pathVec, Finset.sum_range_succ]
    rw [e, val_add, ih (by omega), val_single]
    have hB : q.B (pathVec P (m + 1)) (Pi.single (P (m + 1)) 1) = -1 := by
      rw [pathVec, B_sum_left, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero fun i hi ↦ by
        rw [B_single_single, q.symm]
        have := h0 i (m + 1) (by omega) (by simp at hi; omega)
        rw [q.symm] at this; exact this]
      rw [B_single_single, hc m (by omega), zero_add]
    rw [hB]; ring

lemma pathVec_apply {P : ℕ → ι} {M : ℕ} (hinj : ∀ k l, k < M → l < M → P k = P l → k = l)
    (y : ι) : pathVec P M y = if ∃ i < M, P i = y then 1 else 0 := by
  classical
  simp only [pathVec, Finset.sum_apply, Pi.single_apply]
  split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [if_neg]
      intro h'
      exact hji (hinj j i (Finset.mem_range.1 hj) hi h'.symm)
    · intro h'; exact absurd (Finset.mem_range.2 hi) h'
  · refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [if_neg]
    intro h'
    exact h ⟨i, Finset.mem_range.1 hi, h'.symm⟩

end LargeIndecomposable.Forms.UnitForm

namespace LargeIndecomposable.AR

open Module

namespace DirData

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable {D : DirData k A} {T' : Set D.ι} (hsub : T' ⊆ D.T)

lemma isIndecMod_of_finrank_end {B : Type u} [Ring B] [Algebra k B] {V : FDMod k B}
    (h : finrank k (V →ₗ[B] V) = 1) : IsIndecMod B V := by
  refine isIndecMod_of_brick fun φ ↦ ?_
  have hid : (LinearMap.id : V →ₗ[B] V) ≠ 0 := by
    intro h0
    have hsub : Subsingleton (V →ₗ[B] V) := by
      refine ⟨fun f g ↦ LinearMap.ext fun v ↦ ?_⟩
      have hv : ∀ w : V, w = 0 := fun w ↦ by
        have := LinearMap.congr_fun h0 w; simpa using this
      rw [hv (f v), hv (g v)]
    rw [finrank_zero_of_subsingleton] at h
    exact absurd h (by norm_num)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).1 h (FDMod.lin φ)
  exact ⟨c, hc.symm⟩

/-- **A line in a critical quotient.** -/
theorem exists_critical_line (hT : ∀ x, x ∈ D.T)
    (hH : ∀ a b, D.Arr a b →
      (∀ v, Relation.ReflTransGen D.Arr a v → Relation.ReflTransGen D.Arr v b → v = a ∨ v = b) ∧
        (∃ c, D.e b * c * D.e a ≠ 0) ∧ cartan D b a ≤ 1)
    {U : FDMod k (D.QAlg T')} (hU : Directing U) (hs : Sincere (D.quotAny hsub) U)
    (hR : RigidOff (D.quotAny hsub))
    (hcrit : (eulerForm (D.quotAny hsub) fun _ ↦ Set.mem_univ _).Critical)
    (h10 : 10 ≤ Fintype.card (D.quotAny hsub).ι) :
    ∃ (P : ℕ → D.ι) (V : FDMod k A),
      (∀ i, i < Fintype.card (D.quotAny hsub).ι - 2 → P i ∈ T') ∧
      (∀ i j, i < Fintype.card (D.quotAny hsub).ι - 2 → j < Fintype.card (D.quotAny hsub).ι - 2 →
        P i = P j → i = j) ∧
      (∀ i, i + 1 < Fintype.card (D.quotAny hsub).ι - 2 →
        D.Arr (P i) (P (i + 1)) ∨ D.Arr (P (i + 1)) (P i)) ∧
      (∀ i j, j < Fintype.card (D.quotAny hsub).ι - 2 → i + 2 ≤ j →
        ¬D.Arr (P i) (P j) ∧ ¬D.Arr (P j) (P i)) ∧
      IsIndecMod A V ∧
      (∀ x, (∀ i, i < Fintype.card (D.quotAny hsub).ι - 2 → P i ≠ x) → ∀ v : V, D.e x • v = 0) ∧
      (∀ i, i < Fintype.card (D.quotAny hsub).ι - 2 → finrank k (eSub V (D.e (P i))) = 1) ∧
      (∀ i, i + 1 < Fintype.card (D.quotAny hsub).ι - 2 → ∃ (c : A) (v : V),
        (D.e (P (i + 1)) * c * D.e (P i)) • v ≠ 0 ∨ (D.e (P i) * c * D.e (P (i + 1))) • v ≠ 0) := by
  classical
  set Λ := D.quotAny hsub with hΛ
  have hTΛ : ∀ x, x ∈ Λ.T := fun _ ↦ Set.mem_univ _
  set q := eulerForm Λ hTΛ with hq
  set M := Fintype.card Λ.ι - 2 with hM
  obtain ⟨P', hinj, hcons, hnon⟩ := Forms.UnitForm.Critical.longPath q hcrit h10
  have hφ := D.qmap_surjective T'
  -- arrows only between consecutive points
  have hnoArr : ∀ i j, j < M → i + 2 ≤ j → ¬D.Arr (P' i).1 (P' j).1 ∧ ¬D.Arr (P' j).1 (P' i).1 := by
    intro i j hj hij
    have hne : (P' i).1 ≠ (P' j).1 := fun h ↦ by
      have := hinj i j (by omega) hj (Subtype.ext h); omega
    have h0 : q.c (P' i) (P' j) = 0 := hnon i j hj hij
    refine ⟨fun harr ↦ ?_, fun harr ↦ ?_⟩
    · obtain ⟨hmid, ⟨c, hc⟩, hle⟩ := hH _ _ harr
      have := eulerForm_c_quot_interval hsub (P' i).2 (P' j).2 hne hc hle hmid
      change q.c (P' i) (P' j) = -1 at this
      rw [h0] at this; norm_num at this
    · obtain ⟨hmid, ⟨c, hc⟩, hle⟩ := hH _ _ harr
      have := eulerForm_c_quot_interval hsub (P' j).2 (P' i).2 (Ne.symm hne) hc hle hmid
      change q.c (P' j) (P' i) = -1 at this
      rw [q.symm, h0] at this; norm_num at this
  -- a point off a set of at most two points
  have hthird : ∀ a b : Λ.ι, ∃ u, u ≠ a ∧ u ≠ b := by
    intro a b
    have hc : 2 < (Finset.univ : Finset Λ.ι).card := by rw [Finset.card_univ]; omega
    obtain ⟨u, hu⟩ : ((Finset.univ.erase a).erase b).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.pred_card_le_card_erase (s := Finset.univ.erase a) (a := b)
      have := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset Λ.ι)) (a := a)
      omega
    exact ⟨u, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu), Finset.ne_of_mem_erase hu⟩
  -- consecutive points are joined by an arrow
  have hArr : ∀ i, i + 1 < M → D.Arr (P' i).1 (P' (i + 1)).1 ∨ D.Arr (P' (i + 1)).1 (P' i).1 := by
    intro i hi
    set a := P' i
    set b := P' (i + 1)
    have hab : a ≠ b := fun h ↦ by have := hinj i (i + 1) (by omega) (by omega) h; omega
    obtain ⟨u, hua, hub⟩ := hthird a b
    set x : Λ.ι → ℤ := Pi.single a 1 + Pi.single b 1
    have hpos : Forms.UnitForm.Pos x := ⟨fun y ↦ by
      simp only [x, Pi.add_apply, Pi.single_apply]; split_ifs <;> norm_num, fun h0 ↦ by
      have := congrFun h0 a
      simp [x, Pi.single_apply, hab] at this⟩
    have hx0 : ∀ z : Λ.ι, z ≠ a → z ≠ b → x z = 0 := fun z h1 h2 ↦ by
      simp [x, Pi.single_apply, h1, h2]
    have hxu : x u = 0 := hx0 u hua hub
    have h1 : euler Λ x x = 1 := by
      rw [← eulerForm_val Λ hTΛ, Forms.UnitForm.val_add, Forms.UnitForm.val_single,
        Forms.UnitForm.val_single, Forms.UnitForm.B_single_single]
      change 1 + 1 + q.c a b = 1
      rw [hcons i hi]; norm_num
    obtain ⟨V2, hdim, hend⟩ := exists_brick_off hTΛ hU hs hR u x hpos hxu h1
    have hind : IsIndecMod A (resFD (D.qmap T') V2) :=
      (isIndecMod_res_iff hφ V2).2 (isIndecMod_of_finrank_end hend)
    by_contra hno
    push Not at hno
    refine D.not_isIndecMod_of_split (resFD (D.qmap T') V2) {a.1} {b.1}
      (fun y hy hy' ↦ hab (Subtype.ext ((Set.mem_singleton_iff.1 hy).symm.trans
        (Set.mem_singleton_iff.1 hy'))))
      (fun y hya hyb w ↦ res_smul_eq_zero hsub V2 y (fun hy ↦ by
        rw [hdim]
        have h1 : (⟨y, hy⟩ : Λ.ι) ≠ a := fun h ↦ hya (by rw [← h]; rfl)
        have h2 : (⟨y, hy⟩ : Λ.ι) ≠ b := fun h ↦ hyb (by rw [← h]; rfl)
        exact hx0 ⟨y, hy⟩ h1 h2) w)
      (fun y z hy hz harr ↦ by
        rw [Set.mem_singleton_iff.1 hy, Set.mem_singleton_iff.1 hz] at harr
        exact absurd harr hno.1)
      (fun y z hy hz harr ↦ by
        rw [Set.mem_singleton_iff.1 hy, Set.mem_singleton_iff.1 hz] at harr
        exact absurd harr hno.2) ?_ ?_ hind
    · obtain ⟨v, hv⟩ := exists_smul_ne_of_dimZ (D := Λ) (Y := V2) (c := a) (by
        rw [hdim]; simp [x, Pi.single_apply, hab])
      exact ⟨a.1, rfl, ofX v, hv⟩
    · obtain ⟨v, hv⟩ := exists_smul_ne_of_dimZ (D := Λ) (Y := V2) (c := b) (by
        rw [hdim]; simp [x, Pi.single_apply, Ne.symm hab])
      exact ⟨b.1, rfl, ofX v, hv⟩
  -- the thin brick on the path
  have hM1 : 1 ≤ M := by omega
  obtain ⟨s, hs'⟩ : ∃ s : Λ.ι, ∀ i, i < M → P' i ≠ s := by
    by_contra hall
    push Not at hall
    have hsub' : (Finset.univ : Finset Λ.ι) ⊆ (Finset.range M).image P' := fun z _ ↦ by
      obtain ⟨i, hi, h⟩ := hall z
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, h⟩
    have := (Finset.card_le_card hsub').trans Finset.card_image_le
    rw [Finset.card_univ, Finset.card_range] at this
    omega
  set x := Forms.UnitForm.pathVec P' M with hx
  have hxval : ∀ z, x z = if ∃ i < M, P' i = z then 1 else 0 :=
    Forms.UnitForm.pathVec_apply hinj
  have hpos : Forms.UnitForm.Pos x := ⟨fun z ↦ by rw [hxval]; split_ifs <;> norm_num, fun h0 ↦ by
    have := congrFun h0 (P' 0)
    rw [hxval, if_pos ⟨0, hM1, rfl⟩] at this
    exact absurd this (by norm_num)⟩
  have hxs : x s = 0 := by
    rw [hxval, if_neg]
    rintro ⟨i, hi, h⟩
    exact hs' i hi h
  have h1 : euler Λ x x = 1 := by
    rw [← eulerForm_val Λ hTΛ]
    have := Forms.UnitForm.val_pathVec (q := q) (P := P') (M := M) hcons hnon (M - 1) (by omega)
    rwa [show M - 1 + 1 = M by omega] at this
  obtain ⟨V, hdim, hend⟩ := exists_brick_off hTΛ hU hs hR s x hpos hxs h1
  have hindW : IsIndecMod A (resFD (D.qmap T') V) :=
    (isIndecMod_res_iff hφ V).2 (isIndecMod_of_finrank_end hend)
  have hon : ∀ i, i < M → dimZ Λ V (P' i) = 1 := fun i hi ↦ by
    rw [hdim, hxval, if_pos ⟨i, hi, rfl⟩]
  have hoff : ∀ z : D.ι, (∀ i, i < M → (P' i).1 ≠ z) → ∀ w : resFD (D.qmap T') V,
      D.e z • w = 0 := fun z hz w ↦ res_smul_eq_zero hsub V z (fun hz' ↦ by
    rw [hdim]
    refine (hxval ⟨z, hz'⟩).trans (if_neg ?_)
    rintro ⟨i, hi, h⟩
    exact hz i hi (congrArg Subtype.val h)) w
  have hne : ∀ i, i < M → ∃ w : resFD (D.qmap T') V, D.e (P' i).1 • w ≠ 0 := fun i hi ↦ by
    obtain ⟨v, hv⟩ := exists_smul_ne_of_dimZ (D := Λ) (Y := V) (c := P' i) (by rw [hon i hi]; norm_num)
    exact ⟨ofX v, hv⟩
  refine ⟨fun i ↦ (P' i).1, resFD (D.qmap T') V, fun i _ ↦ (P' i).2,
    fun i j hi hj h ↦ hinj i j hi hj (Subtype.ext h), hArr, hnoArr, hindW, hoff, fun i hi ↦ ?_,
    fun i hi ↦ ?_⟩
  · rw [finrank_eSub_res hsub V (P' i).2]
    have := hon i hi
    change ((finrank k (eSub V (Λ.e (P' i))) : ℕ) : ℤ) = 1 at this
    exact_mod_cast this
  · by_contra hno
    push Not at hno
    refine D.not_isIndecMod_of_split (resFD (D.qmap T') V) {z | ∃ k, k ≤ i ∧ (P' k).1 = z}
      {z | ∃ k, i < k ∧ k < M ∧ (P' k).1 = z} ?_ ?_ ?_ ?_
      ⟨(P' i).1, ⟨i, le_rfl, rfl⟩, hne i (by omega)⟩
      ⟨(P' (i + 1)).1, ⟨i + 1, by omega, hi, rfl⟩, hne (i + 1) hi⟩ hindW
    · rintro z ⟨k1, hk1, rfl⟩ ⟨k2, hk2, hk2M, h⟩
      have := hinj k2 k1 hk2M (by omega) (Subtype.ext h)
      omega
    · intro z hzL hzR w
      refine hoff z (fun k hk h ↦ ?_) w
      rcases le_or_gt k i with hki | hki
      · exact hzL ⟨k, hki, h⟩
      · exact hzR ⟨k, hki, hk, h⟩
    · rintro z1 z2 ⟨k1, hk1, rfl⟩ ⟨k2, hk2, hk2M, rfl⟩ harr c w
      by_cases hk : k1 + 2 ≤ k2
      · exact absurd harr (hnoArr k1 k2 hk2M hk).1
      · obtain rfl : k1 = i := by omega
        obtain rfl : k2 = k1 + 1 := by omega
        exact (hno c w).1
    · rintro z1 z2 ⟨k1, hk1, hk1M, rfl⟩ ⟨k2, hk2, rfl⟩ harr c w
      by_cases hk : k2 + 2 ≤ k1
      · exact absurd harr (hnoArr k2 k1 hk1M hk).2
      · obtain rfl : k2 = i := by omega
        obtain rfl : k1 = k2 + 1 := by omega
        exact (hno c w).2

end DirData

end LargeIndecomposable.AR
