module

public import LargeIndecomposable.Modules.Corners.SplitBasicOf
public import LargeIndecomposable.Modules.Morita.Coind

/-!
# The basic algebra as a full corner

For a complete set `f_s` of primitive orthogonal idempotents of `A`, choose
one representative `f_r` in each class of `f_s A ≅ f_t A` and put
`e = Σ f_r`. Then `e` is full (`AeA = A`, in the form `IsFull`), and over an
algebraically closed field `eAe` is split basic. This is the first step of
Lemma 3.1.

The representative choice and the corner idempotents are adapted from
`LargeIndecomposable/Foundations/BasicCorner.lean` of
`multiplicative-bases-deformations`, commit
`7b9f39f221d8a420a1531f487a3b93ae6d26ce85`.

## References

* *Multiplicative bases and deformations of representation-finite algebras*, <https://github.com/haruhisa-enomoto/multiplicative-bases-deformations>. Numbered statements cited here refer to it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u

namespace BasicCorner

open Classical

variable {A : Type u} [Ring A]

theorem isoData_refl {a : A} (ha : IsIdempotentElem a) : IsoData a a :=
  ⟨a, a, by rw [ha.eq, ha.eq], by rw [ha.eq, ha.eq], ha.eq, ha.eq⟩

theorem _root_.LargeIndecomposable.IsoData.symm {a b : A} (h : IsoData a b) : IsoData b a := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  exact ⟨y, x, h2, h1, h4, h3⟩

theorem left_of_sandwich {a b x : A} (ha : IsIdempotentElem a) (h : a * x * b = x) :
    a * x = x := by
  rw [← h, ← mul_assoc, ← mul_assoc, ha.eq]

theorem right_of_sandwich {a b x : A} (hb : IsIdempotentElem b) (h : a * x * b = x) :
    x * b = x := by
  rw [← h, mul_assoc, hb.eq]

theorem _root_.LargeIndecomposable.IsoData.trans {a b c : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hc : IsIdempotentElem c) (h : IsoData a b) (h' : IsoData b c) : IsoData a c := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  obtain ⟨x', y', h1', h2', h3', h4'⟩ := h'
  refine ⟨x * x', y' * y, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, left_of_sandwich ha h1, mul_assoc, right_of_sandwich hc h1']
  · rw [← mul_assoc, left_of_sandwich hc h2', mul_assoc, right_of_sandwich ha h2]
  · calc x * x' * (y' * y) = x * (x' * y') * y := by simp only [mul_assoc]
      _ = a := by rw [h3', right_of_sandwich hb h1, h3]
  · calc y' * y * (x * x') = y' * (y * x) * x' := by simp only [mul_assoc]
      _ = c := by rw [h4, right_of_sandwich hb h2', h4']

variable {n : ℕ} {f : Fin n → A} (hf : CompleteOrthogonalIdempotents f)

/-- The representative of the class of `f_s`: the least `t` with `f_t A ≅ f_s A`. -/
def rep (s : Fin n) : Fin n :=
  (Finset.univ.filter fun t ↦ IsoData (f t) (f s)).min' ⟨s, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact isoData_refl (hf.idem s)⟩

include hf in
theorem rep_spec (s : Fin n) : IsoData (f (rep hf s)) (f s) := by
  have := Finset.min'_mem (Finset.univ.filter fun t ↦ IsoData (f t) (f s)) ⟨s, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact isoData_refl (hf.idem s)⟩
  exact (Finset.mem_filter.1 this).2

include hf in
theorem rep_eq {s t : Fin n} (h : IsoData (f s) (f t)) : rep hf s = rep hf t := by
  have : (Finset.univ.filter fun r ↦ IsoData (f r) (f s)) =
      Finset.univ.filter fun r ↦ IsoData (f r) (f t) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hr ↦ hr.trans (hf.idem r) (hf.idem s) (hf.idem t) h,
      fun hr ↦ hr.trans (hf.idem r) (hf.idem t) (hf.idem s) h.symm⟩
  simp only [rep, this]

include hf in
theorem rep_rep (s : Fin n) : rep hf (rep hf s) = rep hf s :=
  rep_eq hf (rep_spec hf s)

/-- The representatives. -/
def reps : Finset (Fin n) := Finset.univ.image (rep hf)

/-- `e = Σ_{r} f_r`. -/
def eB : A := ∑ r ∈ reps hf, f r

include hf in
theorem eB_idem : IsIdempotentElem (eB hf) := hf.toOrthogonalIdempotents.isIdempotentElem_sum

include hf in
theorem f_mul_eB {r : Fin n} (hr : r ∈ reps hf) : f r * eB hf = f r :=
  hf.toOrthogonalIdempotents.mul_sum_of_mem hr

include hf in
theorem eB_mul_f {r : Fin n} (hr : r ∈ reps hf) : eB hf * f r = f r := by
  unfold eB
  rw [Finset.sum_mul, Finset.sum_eq_single r (fun t _ htr ↦ hf.ortho htr) (fun h ↦ absurd hr h),
    (hf.idem r).eq]

include hf in
/-- `AeA = A`. -/
theorem isFull_eB : Morita.IsFull (eB hf) := by
  have hdata := fun s ↦ (rep_spec hf s).symm
  choose x y h1 h2 h3 h4 using hdata
  refine ⟨n, x, y, ?_⟩
  have hr : ∀ s, rep hf s ∈ reps hf := fun s ↦ Finset.mem_image_of_mem _ (Finset.mem_univ s)
  have : ∀ s, x s * eB hf * y s = f s := fun s ↦ by
    rw [← right_of_sandwich (hf.idem _) (h1 s), mul_assoc (x s), f_mul_eB hf (hr s),
      right_of_sandwich (hf.idem _) (h1 s), h3]
  simp_rw [this]
  exact hf.complete

include hf in
theorem rep_of_mem {r : Fin n} (hr : r ∈ reps hf) : rep hf r = r := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hr
  exact rep_rep hf s

/-- The idempotents `f_r` of the corner `eAe`. -/
def gB (j : Fin (reps hf).card) : (eB_idem hf).Corner :=
  Corner.mk (eB_idem hf) (f ((reps hf).equivFin.symm j).1)
    ((Corner.mem_iff (eB_idem hf)).2
      ⟨eB_mul_f hf ((reps hf).equivFin.symm j).2, f_mul_eB hf ((reps hf).equivFin.symm j).2⟩)

theorem gB_val (j : Fin (reps hf).card) :
    Corner.val (eB_idem hf) (gB hf j) = f ((reps hf).equivFin.symm j).1 := rfl

theorem gB_complete : CompleteOrthogonalIdempotents (gB hf) := by
  refine ⟨⟨fun j ↦ Corner.ext _ ?_, fun i j hij ↦ Corner.ext _ ?_⟩, Corner.ext _ ?_⟩
  · rw [Corner.val_mul, gB_val]; exact (hf.idem _).eq
  · rw [Corner.val_mul, gB_val, gB_val, Corner.val_zero]
    refine hf.ortho fun h ↦ hij ?_
    exact (reps hf).equivFin.symm.injective (Subtype.ext h)
  · have : Corner.val (eB_idem hf) (∑ j, gB hf j) = ∑ j, Corner.val (eB_idem hf) (gB hf j) :=
      map_sum (Corner.valL ℤ (eB_idem hf)) _ _
    rw [this, Corner.val_one]
    simp_rw [gB_val]
    rw [Equiv.sum_comp (reps hf).equivFin.symm (fun r ↦ f r.1),
      Finset.sum_coe_sort (reps hf) f]
    rfl

theorem gB_primitive (hprim : ∀ s, IsPrimitiveIdempotent (f s)) (j : Fin (reps hf).card) :
    IsPrimitiveIdempotent (gB hf j) := by
  have hp := hprim ((reps hf).equivFin.symm j).1
  refine ⟨(gB_complete hf).idem j, fun h ↦ hp.2.1 ?_, fun G hG h1 h2 ↦ ?_⟩
  · have := congrArg (Corner.val (eB_idem hf)) h
    rwa [gB_val, Corner.val_zero] at this
  · have hG' : IsIdempotentElem (Corner.val (eB_idem hf) G) := by
      change _ * _ = _; rw [← Corner.val_mul, hG.eq]
    have h1' := congrArg (Corner.val (eB_idem hf)) h1
    have h2' := congrArg (Corner.val (eB_idem hf)) h2
    rw [Corner.val_mul, gB_val] at h1' h2'
    rcases hp.2.2 _ hG' h1' h2' with h | h
    · left; apply Corner.ext; rw [h, Corner.val_zero]
    · right; apply Corner.ext; rw [h, gB_val]

theorem gB_basic (i j : Fin (reps hf).card) (h : IsoData (gB hf i) (gB hf j)) : i = j := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  have hiso : IsoData (f ((reps hf).equivFin.symm i).1) (f ((reps hf).equivFin.symm j).1) := by
    refine ⟨Corner.val _ x, Corner.val _ y, ?_, ?_, ?_, ?_⟩
    · have := congrArg (Corner.val (eB_idem hf)) h1
      rwa [Corner.val_mul, Corner.val_mul, gB_val, gB_val] at this
    · have := congrArg (Corner.val (eB_idem hf)) h2
      rwa [Corner.val_mul, Corner.val_mul, gB_val, gB_val] at this
    · have := congrArg (Corner.val (eB_idem hf)) h3
      rwa [Corner.val_mul, gB_val] at this
    · have := congrArg (Corner.val (eB_idem hf)) h4
      rwa [Corner.val_mul, gB_val] at this
  have := rep_eq hf hiso
  rw [rep_of_mem hf ((reps hf).equivFin.symm i).2, rep_of_mem hf ((reps hf).equivFin.symm j).2]
    at this
  exact (reps hf).equivFin.symm.injective (Subtype.ext this)

end BasicCorner

variable (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- The first step of Lemma 3.1: a full idempotent `e` with `eAe` split basic. -/
theorem exists_full_splitBasic :
    ∃ (e : A) (he : IsIdempotentElem e) (m : ℕ), Morita.IsFull e ∧
      Nonempty (SplitBasicData k he.Corner (Fin m)) := by
  obtain ⟨n, f, hf, hprim⟩ := exists_primitive_decomposition (k := k) (A := A)
  have : FiniteDimensional k (BasicCorner.eB_idem hf).Corner :=
    Corner.finiteDimensional (BasicCorner.eB_idem hf) (k := k)
  exact ⟨_, BasicCorner.eB_idem hf, _, BasicCorner.isFull_eB hf,
    ⟨splitBasicDataOf (k := k) _ (BasicCorner.gB_complete hf) (BasicCorner.gB_primitive hf hprim)
      (BasicCorner.gB_basic hf)⟩⟩

end LargeIndecomposable
