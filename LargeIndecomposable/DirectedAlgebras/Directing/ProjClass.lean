module

public import LargeIndecomposable.DirectedAlgebras.Directing.LiveOn

/-!
# Indecomposable projectives of a directed algebra

`A = ⊕_{z ∈ T} A e_z` (`decompSelf`), and free modules decompose into copies of the `P(z)`
(`decompFree`). Hence a nonzero indecomposable summand of a free module is isomorphic to some
`P(z)` (`iso_proj_of_freeSummand`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Decompositions of a power of a module. -/
def Decomp.pow {E : FDMod k A} (d : Decomp E) (m : ℕ) :
    Decomp (⟨Fin m → E⟩ : FDMod k A) where
  ι := ULift.{u} (Fin m) × d.ι
  obj p := d.obj p.2
  indec p := d.indec p.2
  nt p := d.nt p.2
  inc p := (FDMod.ofLin (show d.obj p.2 →ₗ[A] (Fin m → E) from
    LinearMap.single A (fun _ ↦ E) p.1.down ∘ₗ FDMod.lin (d.inc p.2)))
  proj p := (FDMod.ofLin (show (Fin m → E) →ₗ[A] d.obj p.2 from
    FDMod.lin (d.proj p.2) ∘ₗ LinearMap.proj p.1.down))
  sum_id := by
    classical
    apply LinearMap.ext; intro v
    funext i
    have hs : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
      simpa using LinearMap.congr_fun d.sum_id x
    rw [LinearMap.sum_apply]
    change (∑ p : ULift.{u} (Fin m) × d.ι, LinearMap.single A (fun _ ↦ E) p.1.down
      (FDMod.lin (d.inc p.2) (FDMod.lin (d.proj p.2) (v p.1.down)))) i = v i
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single (ULift.up i)]
    · simp only [Finset.sum_apply, LinearMap.single_apply, Pi.single_eq_same]
      exact hs (v i)
    · intro b _ hb
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [LinearMap.single_apply, Pi.single_eq_of_ne]
      exact fun h ↦ hb (ULift.ext h.symm)
    · simp
  retr p := by
    apply LinearMap.ext; intro x
    change FDMod.lin (d.proj p.2) (LinearMap.single A (fun _ ↦ E) p.1.down
      (FDMod.lin (d.inc p.2) x) p.1.down) = x
    rw [LinearMap.single_apply, Pi.single_eq_same]
    exact LinearMap.congr_fun (d.retr p.2) x
  orth p q h := by
    classical
    apply LinearMap.ext; intro x
    change FDMod.lin (d.proj q.2) (LinearMap.single A (fun _ ↦ E) p.1.down
      (FDMod.lin (d.inc p.2) x) q.1.down) = 0
    rw [LinearMap.single_apply]
    by_cases h1 : p.1 = q.1
    · rw [h1, Pi.single_eq_same]
      have h2 : p.2 ≠ q.2 := fun h2 ↦ h (Prod.ext h1 h2)
      exact LinearMap.congr_fun (d.orth p.2 q.2 h2) x
    · rw [Pi.single_eq_of_ne (fun h3 ↦ h1 (ULift.ext h3.symm)), map_zero]

namespace DirData

variable (D : DirData k A)

/-- **`A = ⊕_{z ∈ T} A e_z`.** -/
def decompSelf : Decomp (FDMod.self : FDMod k A) := by
  classical
  exact
  { ι := ULift.{u} {z // z ∈ D.T}
    obj z := projE (k := k) (D.idem z.down.1)
    indec z := (D.projIndNT z.down.1 z.down.2).1
    nt z := (D.projIndNT z.down.1 z.down.2).2
    inc z := (FDMod.ofLin (show leftIdeal (D.idem z.down.1) →ₗ[A] A from (leftIdeal (D.idem z.down.1)).subtype))
    proj z := (FDMod.ofLin (show A →ₗ[A] leftIdeal (D.idem z.down.1) from
      LinearMap.codRestrict _ (LinearMap.toSpanSingleton A A (D.e z.down.1)) fun a ↦ by
        change a * D.e z.down.1 * D.e z.down.1 = a * D.e z.down.1
        rw [mul_assoc, D.e_mul_e]))
    sum_id := by
      apply LinearMap.ext; intro a
      rw [LinearMap.sum_apply]
      change ∑ z : ULift.{u} {z // z ∈ D.T}, a * D.e z.down.1 = a
      have h1 : ∑ z : ULift.{u} {z // z ∈ D.T}, a * D.e z.down.1 =
          ∑ z : {z // z ∈ D.T}, a * D.e z.1 :=
        Fintype.sum_equiv Equiv.ulift _ _ fun _ ↦ rfl
      rw [h1, ← Finset.sum_subtype (Finset.univ.filter (· ∈ D.T)) (by simp) (fun z ↦ a * D.e z),
        Finset.sum_filter_of_ne (fun z _ h ↦ by
          by_contra hz; exact h (by rw [D.zero z hz, mul_zero])), ← Finset.mul_sum, D.sum,
        mul_one]
    retr z := by
      apply LinearMap.ext; intro a
      apply Subtype.ext
      change (a : A) * D.e z.down.1 = a
      exact a.2
    orth z w h := by
      apply LinearMap.ext; intro a
      apply Subtype.ext
      change (a : A) * D.e w.down.1 = 0
      have hne : z.down.1 ≠ w.down.1 := fun h' ↦ h (ULift.ext (Subtype.ext h'))
      rw [← show (a : A) * D.e z.down.1 = a from a.2, mul_assoc, D.orth _ _ hne, mul_zero] }

/-- **Indecomposable summands of free modules are vertex projectives.** -/
theorem iso_proj_of_freeSummand {Z : FDMod k A} (hZ : IndNT Z) (h : IsFreeSummand A Z) :
    ∃ z, z ∈ D.T ∧ IsoM Z (projE (k := k) (D.idem z)) := by
  obtain ⟨m, α, β, hβα⟩ := h
  obtain ⟨p, hp⟩ := iso_summand_of_splitMono hZ ((D.decompSelf).pow m)
    (show Z ⟶ (⟨Fin m → (FDMod.self : FDMod k A)⟩ : FDMod k A) from (FDMod.ofLin (α))) (FDMod.ofLin (β)) ((FDMod.comp_eq_id_iff _ _).2 (hβα))
  exact ⟨p.2.down.1, p.2.down.2, hp⟩

end DirData

end LargeIndecomposable.AR
