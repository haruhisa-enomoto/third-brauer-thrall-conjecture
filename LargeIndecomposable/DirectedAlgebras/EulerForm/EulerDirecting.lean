module

public import LargeIndecomposable.DirectedAlgebras.Directing.Depth
public import LargeIndecomposable.DirectedAlgebras.Directing.DirectingPred

/-!
# The Euler form of a directing module

For `0 → K → P → Z → 0` with `P` Euler-projective and every extension of `Z` by `W` split,
`⟨dim Z, dim W⟩ = dim Hom(Z, W) + dim Hom(K, W) - ⟨dim K, dim W⟩` (`euler_step`). Finite products
(`FDMod.pi`) keep Euler-projectivity (`EulerProj.pi`) and depth bounds (`LivesBelow.pi`), and
extensions split summand by summand (`extVanish_pi`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- **One telescoping step.** -/
theorem euler_step {P K Z W : FDMod k A} (hP : EulerProj D P) (f : K →ₗ[A] P) (g : P →ₗ[A] Z)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (hv : ExtVanish Z W) :
    euler D (dimZ D Z) (dimZ D W) =
      (finrank k (Z →ₗ[A] W) : ℤ) + finrank k (K →ₗ[A] W) - euler D (dimZ D K) (dimZ D W) := by
  have hd := dimZ_exact D f g hf hg hex
  have hZ : dimZ D Z = dimZ D P - dimZ D K := by rw [hd]; abel
  rw [hZ, euler_sub, hP W]
  have hker : finrank k (LinearMap.ker (precomp k (Y := W) f)) = finrank k (Z →ₗ[A] W) := by
    have hinj : Function.Injective (precomp k (Y := W) g) := by
      intro φ ψ h
      refine LinearMap.ext fun z ↦ ?_
      obtain ⟨p, rfl⟩ := hg z
      exact LinearMap.congr_fun h p
    have hrange : LinearMap.range (precomp k (Y := W) g) = LinearMap.ker (precomp k (Y := W) f) := by
      ext φ
      constructor
      · rintro ⟨ψ, rfl⟩
        rw [LinearMap.mem_ker]
        refine LinearMap.ext fun p ↦ ?_
        change ψ (g (f p)) = 0
        rw [mem_ker_of_range hex, map_zero]
      · intro hφ
        obtain ⟨ψ, hψ⟩ := exists_factor f g hg hex φ hφ
        exact ⟨ψ, hψ⟩
    rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  have hsurj : LinearMap.range (precomp k (Y := W) f) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro φ
    obtain ⟨ψ, hψ⟩ := extend_of_extVanish f g hf hg hex hv φ
    exact ⟨ψ, hψ⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (precomp k (Y := W) f)
  rw [hsurj, finrank_top] at hrn
  omega

/-- A finite product of objects. -/
abbrev FDMod.pi {J : Type u} [Fintype J] (X : J → FDMod k A) : FDMod k A where
  carrier := ∀ j, X j

/-- **Finite products of Euler-projectives are Euler-projective.** -/
theorem EulerProj.pi {J : Type u} [Fintype J] [DecidableEq J] {X : J → FDMod k A}
    (h : ∀ j, EulerProj D (X j)) : EulerProj D (FDMod.pi X) := by
  intro W
  have hd : dimZ D (FDMod.pi X) = ∑ j, dimZ D (X j) := by
    funext x
    simp only [dimZ, Finset.sum_apply]
    have e : eSub (FDMod.pi X) (D.e x) ≃ₗ[k] ∀ j, eSub (X j) (D.e x) :=
      { toFun m j := ⟨(m : ∀ j, X j) j, congrFun (m.2 : D.e x • (m : ∀ j, X j) = m) j⟩
        invFun v := ⟨fun j ↦ (v j : X j), funext fun j ↦ (v j).2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [show dimv D.e (FDMod.pi X) x = finrank k (eSub (FDMod.pi X) (D.e x)) from rfl,
      e.finrank_eq, Module.finrank_pi_fintype]
    push_cast
    rfl
  let H : ((FDMod.pi X) →ₗ[A] W) ≃ₗ[k] ∀ j, (X j →ₗ[A] W) :=
    { toFun f j := f ∘ₗ LinearMap.single A (fun j ↦ X j) j
      invFun g := ∑ j, g j ∘ₗ LinearMap.proj (R := A) (φ := fun j ↦ X j) j
      map_add' f f' := by funext j; exact LinearMap.add_comp _ _ _
      map_smul' c f := by funext j; exact LinearMap.ext fun x ↦ by simp
      left_inv f := LinearMap.ext fun x ↦ by
        dsimp only
        rw [LinearMap.sum_apply]
        simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval]
        rw [← map_sum]
        congr 1
        exact (Finset.univ_sum_single x)
      right_inv g := by
        funext j
        refine LinearMap.ext fun x ↦ ?_
        dsimp only
        rw [LinearMap.comp_apply, LinearMap.sum_apply, Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          simp [Pi.single_eq_of_ne hij]
        · simp }
  rw [hd, euler_sum, H.finrank_eq, Module.finrank_pi_fintype]
  push_cast
  exact Finset.sum_congr rfl fun j _ ↦ h j W

/-- Depth bounds pass to finite products. -/
lemma LivesBelow.pi {J : Type u} [Fintype J] {X : J → FDMod k A} {d : ℕ}
    (h : ∀ j, LivesBelow D (X j) d) : LivesBelow D (FDMod.pi X) d := by
  intro x hx
  rw [eq_bot_iff]
  intro m hm
  rw [Submodule.mem_bot]
  funext j
  have hj : ((m : ∀ j, X j) j) ∈ eSub (X j) (D.e x) := congrFun (hm : D.e x • m = m) j
  rw [h j x hx] at hj
  exact (Submodule.mem_bot k).1 hj

/-- **Extensions split summand by summand.** -/
theorem extVanish_pi {J : Type u} [Fintype J] [DecidableEq J] {X : J → FDMod k A} {W : FDMod k A}
    (h : ∀ j, ExtVanish (X j) W) : ExtVanish (FDMod.pi X) W := by
  intro E i p hi hp hex
  have hs : ∀ j, ∃ s : X j →ₗ[A] E, p ∘ₗ s = LinearMap.single A (fun j ↦ X j) j := fun j ↦
    exists_lift_summand (LinearMap.single A (fun j ↦ X j) j) (LinearMap.proj j)
      (LinearMap.ext fun x ↦ by simp) (h j) i p hi hp hex
  choose s hs using hs
  refine ⟨∑ j, s j ∘ₗ LinearMap.proj (R := A) (φ := fun j ↦ X j) j, LinearMap.ext fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  conv_rhs => rw [LinearMap.id_apply, ← Finset.univ_sum_single (x : ∀ j, X j)]
  exact Finset.sum_congr rfl fun j _ ↦ LinearMap.congr_fun (hs j) _

/-- Maps out of a sum of indecomposable projectives lift along surjections. -/
theorem sumProj_lift {X Y : FDMod k A} (p : X ⟶ Y) (hp : Function.Surjective (FDMod.lin p)) :
    ∀ (l : List D.ι) (f : sumProj D l ⟶ Y), ∃ g : sumProj D l ⟶ X, g ≫ p = f
  | [], f => by
    haveI : Subsingleton (sumProj D []) := inferInstanceAs (Subsingleton PUnit)
    refine ⟨show sumProj D [] →ₗ[A] X from 0, LinearMap.ext fun x ↦ ?_⟩
    rw [Subsingleton.elim x 0]
    change FDMod.lin p ((0 : sumProj D [] →ₗ[A] X) 0) = (show sumProj D [] →ₗ[A] Y from f) 0
    simp
  | i :: l, f => by
    obtain ⟨g₁, hg₁⟩ := projE_lift (D.idem i) p hp
      (show projE (k := k) (D.idem i) →ₗ[A] Y from
        (show sumProj D (i :: l) →ₗ[A] Y from f) ∘ₗ LinearMap.inl A _ _)
    obtain ⟨g₂, hg₂⟩ := sumProj_lift p hp l
      (show sumProj D l →ₗ[A] Y from (show sumProj D (i :: l) →ₗ[A] Y from f) ∘ₗ LinearMap.inr A _ _)
    refine ⟨show sumProj D (i :: l) →ₗ[A] X from LinearMap.coprod (FDMod.lin g₁) (FDMod.lin g₂), ?_⟩
    refine LinearMap.ext fun ⟨a, b⟩ ↦ ?_
    have h1 := LinearMap.congr_fun hg₁ a
    have h2 := LinearMap.congr_fun hg₂ b
    change FDMod.lin p (FDMod.lin g₁ a + FDMod.lin g₂ b) =
      (show sumProj D (i :: l) →ₗ[A] Y from f) (a, b)
    rw [map_add]
    rw [show FDMod.lin p (FDMod.lin g₁ a) = _ from h1, show FDMod.lin p (FDMod.lin g₂ b) = _ from h2]
    exact (map_add (show sumProj D (i :: l) →ₗ[A] Y from f) (a, 0) (0, b)).symm.trans
      (congrArg _ (by simp))

/-- A direct summand of a sum of indecomposable projectives. -/
def IsProjSummand (U : FDMod k A) : Prop :=
  ∃ (l : List D.ι) (s : U ⟶ sumProj D l) (r : sumProj D l ⟶ U), s ≫ r = 𝟙 U

/-- **Extensions ending in a projective summand split.** -/
theorem IsProjSummand.extVanish {U : FDMod k A} (hU : IsProjSummand D U) (W : FDMod k A) :
    ExtVanish U W := by
  obtain ⟨l, s, r, hsr⟩ := hU
  intro E i p hi hp hex
  obtain ⟨g, hg⟩ := sumProj_lift D (show E ⟶ U from p) hp l r
  refine ⟨FDMod.lin g ∘ₗ FDMod.lin s, LinearMap.ext fun x ↦ ?_⟩
  have := LinearMap.congr_fun hg (FDMod.lin s x)
  have h2 := LinearMap.congr_fun hsr x
  change p (FDMod.lin g (FDMod.lin s x)) = x
  exact this.trans h2

/-- Decomposition of a finite product from decompositions of the factors. -/
def Decomp.pi {J : Type u} [Fintype J] [DecidableEq J] {X : J → FDMod k A}
    (d : ∀ j, Decomp (X j)) : Decomp (FDMod.pi X) where
  ι := Σ j, (d j).ι
  obj c := (d c.1).obj c.2
  indec c := (d c.1).indec c.2
  nt c := (d c.1).nt c.2
  inc c := LinearMap.single A (fun j ↦ X j) c.1 ∘ₗ FDMod.lin ((d c.1).inc c.2)
  proj c := FDMod.lin ((d c.1).proj c.2) ∘ₗ LinearMap.proj (R := A) (φ := fun j ↦ X j) c.1
  sum_id := by
    refine LinearMap.ext fun x ↦ funext fun j' ↦ ?_
    rw [LinearMap.sum_apply, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single j']
    · have h := LinearMap.congr_fun (d j').sum_id (x j')
      rw [LinearMap.sum_apply] at h
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h
      change Pi.single (M := fun j ↦ X j) j' _ j' = _
      rw [Pi.single_eq_same]
      rfl
    · intro j _ hj
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      change Pi.single (M := fun j ↦ X j) j _ j' = 0
      exact Pi.single_eq_of_ne (Ne.symm hj) _
    · simp
  retr c := LinearMap.ext fun x ↦ by
    change FDMod.lin ((d c.1).proj c.2) (Pi.single (M := fun j ↦ X j) c.1
      (FDMod.lin ((d c.1).inc c.2) x) c.1) = x
    rw [Pi.single_eq_same]
    exact LinearMap.congr_fun ((d c.1).retr c.2) x
  orth c c' h := LinearMap.ext fun x ↦ by
    change FDMod.lin ((d c'.1).proj c'.2) (Pi.single (M := fun j ↦ X j) c.1
      (FDMod.lin ((d c.1).inc c.2) x) c'.1) = 0
    by_cases hj : c'.1 = c.1
    · obtain ⟨j, i⟩ := c
      obtain ⟨j', i'⟩ := c'
      simp only at hj
      subst hj
      rw [Pi.single_eq_same]
      have hi : i ≠ i' := fun e ↦ h (by rw [e])
      exact LinearMap.congr_fun ((d _).orth i i' hi) x
    · rw [Pi.single_eq_of_ne hj, map_zero]

end LargeIndecomposable.AR
