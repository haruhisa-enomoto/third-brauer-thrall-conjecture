module

public import LargeIndecomposable.Modules.Idempotents.PrimitiveDecomposition
public import LargeIndecomposable.Modules.Corners.Corner
public import LargeIndecomposable.Modules.SplitBasic.SplitBasicAlgebras
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Artinian.Module

/-!
# Split basic algebras from primitive idempotents

Over an algebraically closed field, a finite-dimensional algebra with a
complete set of pairwise non-isomorphic primitive orthogonal idempotents is
split basic (`SplitBasicData`): each corner `g A g` is local with residue
field `k`, and the off-diagonal corners lie in the radical.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u

variable {A : Type u} [Ring A]

/-- `aA ≅ bA`, by elements `x ∈ aAb`, `y ∈ bAa` with `xy = a`, `yx = b`.
(Adapted from `BasicCorner.lean` of `multiplicative-bases-deformations`.) -/
def IsoData (a b : A) : Prop :=
  ∃ x y : A, a * x * b = x ∧ b * y * a = y ∧ x * y = a ∧ y * x = b

lemma left_of_sandwich' {g z : A} (hg : IsIdempotentElem g) (h : g * z * g = z) : g * z = z := by
  rw [← h, ← mul_assoc, ← mul_assoc, hg.eq]

lemma right_of_sandwich' {g z : A} (hg : IsIdempotentElem g) (h : g * z * g = z) : z * g = z := by
  rw [← h, mul_assoc, hg.eq]

/-- A sufficient condition for membership in the radical: `z = g z g'` with
`z (g' y g)` nilpotent for all `y`. -/
lemma mem_jacobson_of_sandwich {g g' z : A} (hg : IsIdempotentElem g) (hg' : IsIdempotentElem g')
    (hz : g * z * g' = z) (h : ∀ y : A, IsNilpotent (z * (g' * y * g))) :
    z ∈ Ring.jacobson A := by
  refine Corner.mem_jacobson_of_forall_isUnit fun y ↦ IsNilpotent.isUnit_one_sub ?_
  obtain ⟨N, hN⟩ := h y
  have hzg : z * g' = z := by rw [← hz, mul_assoc, hg'.eq]
  have hgz : g * z = z := by rw [← hz, ← mul_assoc, ← mul_assoc, hg.eq]
  set w := g' * y * g
  have hzyz : z * y * z = z * w * z := by
    calc z * y * z = (z * g') * y * (g * z) := by rw [hzg, hgz]
      _ = z * w * z := by simp only [w, mul_assoc]
  have key : ∀ m : ℕ, (z * y) ^ m * z = (z * w) ^ m * z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (z * y) ^ (m + 1) * z = (z * y) ^ m * (z * y * z) := by
            rw [pow_succ]; simp only [mul_assoc]
        _ = (z * y) ^ m * (z * w * z) := by rw [hzyz]
        _ = ((z * y) ^ m * z) * (w * z) := by simp only [mul_assoc]
        _ = ((z * w) ^ m * z) * (w * z) := by rw [ih]
        _ = (z * w) ^ (m + 1) * z := by rw [pow_succ]; simp only [mul_assoc]
  have hpow : ∀ n : ℕ, (y * z) ^ (n + 1) = y * ((z * y) ^ n * z) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
  refine ⟨N + 1, ?_⟩
  rw [hpow, key, hN, zero_mul, mul_zero]

section Corner

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
  {g : A} (hg : IsPrimitiveIdempotent g)

/-- The only idempotents of a primitive corner are `0` and `1`. -/
lemma corner_idem_eq (f : hg.1.Corner) (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  have hf' : IsIdempotentElem (Corner.val hg.1 f) := by
    change _ * _ = _; rw [← Corner.val_mul, hf.eq]
  rcases hg.2.2 _ hf' (Corner.mul_val hg.1 f) (Corner.val_mul_e hg.1 f) with h | h
  · left; exact Corner.ext hg.1 (by rw [h, Corner.val_zero])
  · right; exact Corner.ext hg.1 (by rw [h, Corner.val_one])

/-- Complementary left ideals of a primitive corner are trivial. -/
lemma corner_isCompl {I I' : Submodule hg.1.Corner hg.1.Corner} (h : IsCompl I I') :
    I = ⊥ ∨ I' = ⊥ := by
  obtain ⟨i, hi, i', hi', h1⟩ := Submodule.mem_sup.1 (h.codisjoint.eq_top ▸ Submodule.mem_top :
    (1 : hg.1.Corner) ∈ I ⊔ I')
  have hii : i * i = i := by
    have hm : i - i * i ∈ I ⊓ I' := by
      refine ⟨I.sub_mem hi (I.smul_mem i hi), ?_⟩
      have e : i * i + i * i' = i := by rw [← mul_add, h1, mul_one]
      have : i - i * i = i * i' := by
        calc i - i * i = (i * i + i * i') - i * i := by rw [e]
          _ = i * i' := by abel
      rw [this]; exact I'.smul_mem i hi'
    rw [h.disjoint.eq_bot, Submodule.mem_bot, sub_eq_zero] at hm
    exact hm.symm
  have key : ∀ {J J' : Submodule hg.1.Corner hg.1.Corner}, Disjoint J J' →
      ∀ j' ∈ J', (∀ x ∈ J, x * j' = x) → J = ⊥ := by
    intro J J' hJ j' hj' hx
    rw [eq_bot_iff]
    intro x hxJ
    have : x ∈ J ⊓ J' := ⟨hxJ, hx x hxJ ▸ J'.smul_mem x hj'⟩
    rwa [hJ.eq_bot] at this
  rcases corner_idem_eq hg i hii with h0 | h1'
  · left
    have h1'' : i' = 1 := by rw [h0, zero_add] at h1; exact h1
    refine key h.disjoint i' hi' fun x _ ↦ ?_
    rw [h1'', mul_one]
  · right
    have h0 : i' = 0 := by rw [h1', add_eq_left] at h1; exact h1
    refine key h.disjoint.symm i hi fun x hx ↦ ?_
    rw [h1', mul_one]

include k hg in
/-- Fitting's lemma in a primitive corner: an element of `g A g` is nilpotent
or invertible in `g A g`. -/
theorem corner_dichotomy (z : A) (hz : g * z * g = z) :
    IsNilpotent z ∨ ∃ u, g * u * g = u ∧ z * u = g ∧ u * z = g := by
  let R := hg.1.Corner
  have : FiniteDimensional k R := Corner.finiteDimensional hg.1 (k := k)
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  have : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  let z' : R := Corner.mk hg.1 z (by rw [Corner.mem_iff hg.1]; exact ⟨left_of_sandwich' hg.1 hz,
    right_of_sandwich' hg.1 hz⟩)
  let L : R →ₗ[R] R := LinearMap.toSpanSingleton R R z'
  have hLpow : ∀ (m : ℕ) (x : R), (L ^ m) x = x * z' ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih => intro x; rw [pow_succ', Module.End.mul_apply, ih, pow_succ]; simp [L, mul_assoc]
  obtain ⟨n, hn, hn1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow L).and (Filter.eventually_ge_atTop 1)).exists
  rcases corner_isCompl hg hn with hk | hr
  · right
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : x * z' = 0 := by simpa [L] using hx
      have : x ∈ LinearMap.ker (L ^ n) := by
        rw [LinearMap.mem_ker, hLpow]
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
        rw [pow_succ', ← mul_assoc, hx', zero_mul]
      rwa [hk] at this
    have hLk : Function.Injective (L.restrictScalars k) := hinj
    obtain ⟨u', hu'⟩ := (LinearMap.injective_iff_surjective.1 hLk) 1
    have hu'z : u' * z' = 1 := by simpa [L] using hu'
    have hzu : z' * u' = 1 := hinj (by
      change (z' * u') * z' = 1 * z'
      rw [mul_assoc, hu'z, mul_one, one_mul])
    refine ⟨Corner.val hg.1 u', ?_, ?_, ?_⟩
    · rw [Corner.mul_val, Corner.val_mul_e]
    · have := congrArg (Corner.val hg.1) hzu
      rwa [Corner.val_mul, Corner.val_one] at this
    · have := congrArg (Corner.val hg.1) hu'z
      rwa [Corner.val_mul, Corner.val_one] at this
  · left
    have : (L ^ n) 1 = 0 := by rw [← Submodule.mem_bot R, ← hr]; exact LinearMap.mem_range_self _ _
    rw [hLpow, one_mul] at this
    refine ⟨n + 1, ?_⟩
    have := congrArg (fun x ↦ Corner.val hg.1 (x * z')) this
    simp only [zero_mul, Corner.val_zero] at this
    rw [← pow_succ, Corner.val_pow] at this
    exact this

include hg in
/-- A nilpotent element of `g A g` has no right inverse in `g A g`. -/
lemma not_rightInv_of_nilpotent {a v : A} (ha : IsNilpotent a) (hv : g * v = v)
    (hav : a * v = g) : False := by
  obtain ⟨n, hn⟩ := ha
  have hgv : ∀ m : ℕ, g * v ^ (m + 1) = v ^ (m + 1) := fun m ↦ by
    rw [pow_succ', ← mul_assoc, hv]
  have key : ∀ m : ℕ, a ^ (m + 1) * v ^ (m + 1) = g := by
    intro m
    induction m with
    | zero => simp [hav]
    | succ m ih =>
      calc a ^ (m + 2) * v ^ (m + 2) = a ^ (m + 1) * (a * v) * v ^ (m + 1) := by
            rw [pow_succ a (m + 1), pow_succ' v (m + 1)]; simp only [mul_assoc]
        _ = a ^ (m + 1) * (g * v ^ (m + 1)) := by rw [hav, mul_assoc]
        _ = g := by rw [hgv, ih]
  rcases n with _ | m
  · rw [pow_zero] at hn
    exact hg.2.1 (by rw [← one_mul g, hn, zero_mul])
  · have := key m
    rw [hn, zero_mul] at this
    exact hg.2.1 this.symm

variable [IsAlgClosed k]

include hg in
/-- The residue field of a primitive corner is `k`. -/
theorem corner_residue (z : A) (hz : g * z * g = z) : ∃ c : k, IsNilpotent (z - c • g) := by
  let R := hg.1.Corner
  have : FiniteDimensional k R := Corner.finiteDimensional hg.1 (k := k)
  have : Nontrivial R := ⟨⟨0, 1, fun h ↦ hg.2.1 (by
    have := congrArg (Corner.val hg.1) h
    rwa [Corner.val_zero, Corner.val_one, eq_comm] at this)⟩⟩
  let z' : R := Corner.mk hg.1 z (by rw [Corner.mem_iff hg.1]; exact ⟨left_of_sandwich' hg.1 hz,
    right_of_sandwich' hg.1 hz⟩)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.mulLeft k z')
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hsand : g * (z - c • g) * g = z - c • g := by
    rw [mul_sub, sub_mul, hz, mul_smul_comm, smul_mul_assoc, hg.1.eq, hg.1.eq]
  rcases corner_dichotomy (k := k) hg _ hsand with h | ⟨u, hu, -, huz⟩
  · exact h
  exfalso
  have hv0 : v ≠ 0 := hv.2
  have hzv : z' * v = c • v := hv.apply_eq_smul
  apply hv0
  apply Corner.ext hg.1
  have hz'v : z * Corner.val hg.1 v = c • Corner.val hg.1 v := by
    have := congrArg (Corner.val hg.1) hzv
    rw [Corner.val_mul, Corner.val_smul] at this
    exact this
  have h1 : (z - c • g) * Corner.val hg.1 v = 0 := by
    rw [sub_mul, smul_mul_assoc, Corner.mul_val, hz'v, sub_self]
  calc Corner.val hg.1 v = g * Corner.val hg.1 v := (Corner.mul_val hg.1 v).symm
    _ = u * (z - c • g) * Corner.val hg.1 v := by rw [huz]
    _ = 0 := by rw [mul_assoc, h1, mul_zero]
    _ = Corner.val hg.1 0 := (Corner.val_zero hg.1).symm

end Corner

variable {k : Type u} [Field k] [IsAlgClosed k] [Algebra k A] [FiniteDimensional k A]

/-- Over an algebraically closed field, a complete set of pairwise
non-isomorphic primitive orthogonal idempotents makes `A` split basic. -/
def splitBasicDataOf {ι : Type} [Fintype ι] (e : ι → A) (hc : CompleteOrthogonalIdempotents e)
    (hp : ∀ i, IsPrimitiveIdempotent (e i)) (hb : ∀ i j, IsoData (e i) (e j) → i = j) :
    SplitBasicData k A ι where
  e := e
  complete := hc
  ne_zero i := (hp i).2.1
  corner_diag x b := by
    have hz : e x * (e x * b * e x) * e x = e x * b * e x := by
      simp only [← mul_assoc, (hc.idem x).eq]; rw [mul_assoc _ (e x) (e x), (hc.idem x).eq]
    obtain ⟨c, hnil⟩ := corner_residue (k := k) (hp x) _ hz
    refine ⟨c, mem_jacobson_of_sandwich (hc.idem x) (hc.idem x) ?_ fun y ↦ ?_⟩
    · rw [mul_sub, sub_mul, hz, mul_smul_comm, smul_mul_assoc, (hc.idem x).eq, (hc.idem x).eq]
    · set a := e x * b * e x - c • e x
      have ha : e x * a * e x = a := by
        simp only [a]; rw [mul_sub, sub_mul, hz, mul_smul_comm, smul_mul_assoc, (hc.idem x).eq,
          (hc.idem x).eq]
      set w := e x * y * e x
      have hw : e x * w = w := by simp only [w, ← mul_assoc, (hc.idem x).eq]
      have hw2 : w * e x = w := by simp only [w, mul_assoc, (hc.idem x).eq]
      have haw : e x * (a * w) * e x = a * w := by
        rw [← mul_assoc, left_of_sandwich' (hc.idem x) ha, mul_assoc, hw2]
      rcases corner_dichotomy (k := k) (hp x) _ haw with h | ⟨u, hu, hawu, -⟩
      · exact h
      · exact (not_rightInv_of_nilpotent (hp x) hnil (v := w * u)
          (by rw [← mul_assoc, hw]) (by rw [← mul_assoc, hawu])).elim
  corner_offdiag x y hxy b := by
    have hgx := hc.idem x
    have hgy := hc.idem y
    refine mem_jacobson_of_sandwich hgx hgy ?_ fun y' ↦ ?_
    · simp only [← mul_assoc, hgx.eq]; rw [mul_assoc _ (e y) (e y), hgy.eq]
    set z := e x * b * e y
    set w := e y * y' * e x
    have hz1 : e x * z = z := by simp only [z, ← mul_assoc, hgx.eq]
    have hz2 : z * e y = z := by simp only [z, mul_assoc, hgy.eq]
    have hw1 : e y * w = w := by simp only [w, ← mul_assoc, hgy.eq]
    have hw2 : w * e x = w := by simp only [w, mul_assoc, hgx.eq]
    have hzw : e x * (z * w) * e x = z * w := by
      rw [← mul_assoc, hz1, mul_assoc, hw2]
    rcases corner_dichotomy (k := k) (hp x) _ hzw with h | ⟨u, hu, hzwu, hu2⟩
    · exact h
    exfalso
    have hu1 : u * e x = u := right_of_sandwich' hgx hu
    have hu0 : e x * u = u := left_of_sandwich' hgx hu
    let t := w * u * z
    have ht : t * t = t := by
      calc t * t = w * u * (z * w * u) * z := by simp only [t, mul_assoc]
        _ = t := by rw [hzwu, mul_assoc w u (e x), hu1]
    have hty : e y * t = t ∧ t * e y = t := ⟨by simp only [t, ← mul_assoc, hw1],
      by simp only [t, mul_assoc, hz2]⟩
    rcases (hp y).2.2 t ht hty.1 hty.2 with h0 | h1
    · apply (hp x).2.1
      calc e x = (z * w * u) * (z * w * u) := by rw [hzwu, hgx.eq]
        _ = z * t * w * u := by simp only [t, mul_assoc]
        _ = 0 := by rw [h0, mul_zero, zero_mul, zero_mul]
    · exact hxy (hb x y ⟨z, w * u, by rw [hz1, hz2],
        by rw [mul_assoc, mul_assoc w, hu1, ← mul_assoc, hw1],
        by rw [← mul_assoc]; exact hzwu, h1 ▸ by simp only [t, mul_assoc]⟩)

end LargeIndecomposable
