module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.PreprojUnbounded
public import LargeIndecomposable.Modules.Duality.DualA

/-!
# Bounded length gives finitely many indecomposables

For a connected algebra with a preprojective component, if the indecomposables have bounded
dimension then there are only finitely many of them up to isomorphism (`finite_of_bounded`, a
first Brauer–Thrall statement in this setting): every indecomposable lies in the component, maps
nonzero into an indecomposable summand of `DA`, and is therefore isomorphic to that summand or
to one of its finitely many predecessors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

variable (k A) in
/-- `DA` as an object. -/
abbrev FDMod.dualA : FDMod k A where
  carrier := DA k A
  isFD := inferInstanceAs (FiniteDimensional k (A →ₗ[k] k))

/-- **Bounded length gives finitely many indecomposables.** -/
theorem finite_of_bounded {ι : Type} [Fintype ι] (e : ι → A) (he : ∀ x, IsIdempotentElem (e x))
    (hsum : ∑ x, e x = 1) (hP : ∀ x, IndNT (projE (k := k) (he x)))
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ x y, x ∈ S → (∃ a, e x * a * e y ≠ 0) ∨ (∃ a, e y * a * e x ≠ 0) → y ∈ S) →
        S = Set.univ)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
    (hb : ∃ b, ∀ N : FDMod k A, IndNT N → finrank k N ≤ b) :
    ∃ L : List (FDMod k A), ∀ N : FDMod k A, IndNT N → ∃ Z ∈ L, IsoM N Z := by
  classical
  obtain ⟨b, hb'⟩ := hb
  have hcl := h𝒞.closedClass ⟨b, hb'⟩
  obtain ⟨M, hM⟩ := h𝒞.nonempty
  have hall : ∀ N, IndNT N → 𝒞 N := fun N hN ↦ all_of_closed e he hsum hP hconn hcl hM N hN
  obtain ⟨d⟩ := FDMod.exists_decomp (FDMod.dualA k A)
  have hdI : ∀ j, IndNT (d.obj j) := fun j ↦ ⟨d.indec j, d.nt j⟩
  choose Lj hLj using fun j ↦ h𝒞.finIso (d.obj j) (hall _ (hdI j))
  refine ⟨(Finset.univ.toList).flatMap (fun j ↦ d.obj j :: Lj j), fun N hN ↦ ?_⟩
  haveI := hN.2
  -- a nonzero map into `DA`
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual k N, l ≠ 0 := by
    obtain ⟨n, hn⟩ := exists_ne (0 : N)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero k hn
    exact ⟨l, fun h0 ↦ hl (by rw [h0]; rfl)⟩
  let φ : N →ₗ[A] DA k A := dualToHomDA (A := A) l
  have hφ : φ ≠ 0 := by
    intro h0
    apply hl
    rw [← homDAToDual_dualToHomDA (A := A) l]
    refine LinearMap.ext fun w ↦ ?_
    rw [homDAToDual_apply]
    change (φ w).ev 1 = 0
    rw [h0]
    rfl
  obtain ⟨j, hj⟩ : ∃ j, FDMod.lin (d.proj j) ∘ₗ φ ≠ 0 := by
    by_contra hall'
    push Not at hall'
    apply hφ
    refine LinearMap.ext fun w ↦ ?_
    have hs := LinearMap.congr_fun d.sum_id (φ w)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at hs
    rw [← hs]
    exact Finset.sum_eq_zero fun i _ ↦ by
      have := LinearMap.congr_fun (hall' i) w
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      rw [this, map_zero]
  let f : N ⟶ d.obj j := FDMod.lin (d.proj j) ∘ₗ φ
  have hmem : ∀ Z, Z ∈ d.obj j :: Lj j →
      Z ∈ (Finset.univ.toList).flatMap (fun j ↦ d.obj j :: Lj j) := fun Z hZ ↦
    List.mem_flatMap.2 ⟨j, Finset.mem_toList.2 (Finset.mem_univ j), hZ⟩
  by_cases hbij : Function.Bijective (FDMod.lin f)
  · exact ⟨d.obj j, hmem _ List.mem_cons_self, f, hbij⟩
  · obtain ⟨m, -, Y, hY, hiso⟩ := iso_predN_of_hom (U := d.obj j) (b := b)
      (fun n X hX ↦ hb' X hX.indNT) (PredN.zero (hdI j)) N hN.1 f hj hbij
    obtain ⟨Z, hZ, hYZ⟩ := hLj j _ _ hY
    exact ⟨Z, hmem _ (List.mem_cons_of_mem _ hZ), hiso.trans hYZ⟩

end LargeIndecomposable.AR
