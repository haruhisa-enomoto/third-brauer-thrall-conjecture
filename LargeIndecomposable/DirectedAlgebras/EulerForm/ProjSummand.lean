module

public import LargeIndecomposable.Modules.Homological.ProjCover
public import LargeIndecomposable.Modules.KrullSchmidt.KrullSchmidtStep
public import LargeIndecomposable.DirectedAlgebras.Directing.DirMod

/-!
# Projective modules are Euler-projective

Euler-projectivity is invariant under isomorphism (`EulerProj.of_bijective`) and holds for a
module once it holds for the summands of a decomposition (`EulerProj.of_decomp`). Sums of
indecomposable projectives decompose into them (`decompSumProj`), so by the Krull–Schmidt step
every indecomposable summand of such a sum is some `A e`, and every direct summand of a sum of
indecomposable projectives is Euler-projective (`eulerProj_of_summand`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- An isomorphism of objects from a bijective map. -/
def isoOfBijective {X Y : FDMod k A} (g : X ⟶ Y) (hg : Function.Bijective (FDMod.lin g)) :
    X ≅ Y where
  hom := g
  inv := (FDMod.ofLin ((LinearEquiv.ofBijective (FDMod.lin g) hg).symm.toLinearMap))
  hom_inv_id := (FDMod.hom_ext (LinearMap.ext fun x ↦
    (LinearEquiv.ofBijective (FDMod.lin g) hg).symm_apply_apply x))
  inv_hom_id := (FDMod.hom_ext (LinearMap.ext fun y ↦
    (LinearEquiv.ofBijective (FDMod.lin g) hg).apply_symm_apply y))

/-- **Euler-projectivity is invariant under isomorphism.** -/
theorem EulerProj.of_bijective {P P' : FDMod k A} (hP : EulerProj D P) (g : P ⟶ P')
    (hg : Function.Bijective (FDMod.lin g)) : EulerProj D P' := by
  intro W
  have hd : dimZ D P' = dimZ D P := by
    funext x
    simp only [dimZ]
    rw [dimv_congr D.e (isoOfBijective g hg)]
  let e := LinearEquiv.ofBijective (FDMod.lin g) hg
  let H : (P →ₗ[A] W) ≃ₗ[k] (P' →ₗ[A] W) :=
    { toFun f := f ∘ₗ e.symm.toLinearMap
      invFun f := f ∘ₗ e.toLinearMap
      map_add' f f' := LinearMap.add_comp _ _ _
      map_smul' c f := LinearMap.ext fun x ↦ by simp
      left_inv f := LinearMap.ext fun x ↦ by simp
      right_inv f := LinearMap.ext fun x ↦ by simp }
  rw [hd, hP W, H.finrank_eq]

lemma euler_sum {ι : Type*} (s : Finset ι) (u : ι → D.ι → ℤ) (w : D.ι → ℤ) :
    euler D (∑ j ∈ s, u j) w = ∑ j ∈ s, euler D (u j) w := by
  unfold euler
  rw [Matrix.mulVec_sum]
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Euler-projectivity from a decomposition.** -/
theorem EulerProj.of_decomp {K : FDMod k A} (d : Decomp K) (h : ∀ j, EulerProj D (d.obj j)) :
    EulerProj D K := by
  classical
  intro W
  have hinc : ∀ j x, FDMod.lin (d.proj j) (FDMod.lin (d.inc j) x) = x := fun j x ↦
    LinearMap.congr_fun (d.retr j) x
  have hsum : ∀ x, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    simpa using LinearMap.congr_fun d.sum_id x
  -- dimension vectors add up
  have hd : dimZ D K = ∑ j, dimZ D (d.obj j) := by
    funext x
    simp only [dimZ, Finset.sum_apply]
    have e : eSub K (D.e x) ≃ₗ[k] ∀ j, eSub (d.obj j) (D.e x) :=
      { toFun m j := eSubMap D.e (d.proj j) x m
        invFun v := ∑ j, eSubMap D.e (d.inc j) x (v j)
        map_add' m m' := by funext j; exact map_add _ _ _
        map_smul' c m := by funext j; exact map_smul _ _ _
        left_inv m := by
          apply Subtype.ext
          dsimp only
          rw [Submodule.coe_sum]
          exact hsum m
        right_inv v := by
          funext j
          apply Subtype.ext
          dsimp only
          change FDMod.lin (d.proj j)
            ((∑ i, eSubMap D.e (d.inc i) x (v i) : eSub K (D.e x)) : K) = v j
          rw [Submodule.coe_sum, map_sum, Finset.sum_eq_single j]
          · exact hinc j _
          · intro i _ hij
            exact LinearMap.congr_fun (d.orth i j hij) _
          · simp }
    rw [show dimv D.e K x = finrank k (eSub K (D.e x)) from rfl, e.finrank_eq,
      Module.finrank_pi_fintype]
    push_cast
    rfl
  -- maps out of `K` are families of maps out of the summands
  let H : (K →ₗ[A] W) ≃ₗ[k] ∀ j, (d.obj j →ₗ[A] W) :=
    { toFun f j := f ∘ₗ FDMod.lin (d.inc j)
      invFun g := ∑ j, g j ∘ₗ FDMod.lin (d.proj j)
      map_add' f f' := by funext j; exact LinearMap.add_comp _ _ _
      map_smul' c f := by funext j; exact LinearMap.ext fun x ↦ by simp
      left_inv f := LinearMap.ext fun x ↦ by
        dsimp only
        rw [LinearMap.sum_apply]
        simp only [LinearMap.comp_apply]
        rw [← map_sum, hsum]
      right_inv g := by
        funext j
        refine LinearMap.ext fun x ↦ ?_
        dsimp only
        rw [LinearMap.comp_apply, LinearMap.sum_apply, Finset.sum_eq_single j]
        · rw [LinearMap.comp_apply, hinc]
        · intro i _ hij
          rw [LinearMap.comp_apply, show FDMod.lin (d.proj i) (FDMod.lin (d.inc j) x) = 0 from
            LinearMap.congr_fun (d.orth j i (Ne.symm hij)) x, map_zero]
        · simp }
  rw [hd, euler_sum, H.finrank_eq, Module.finrank_pi_fintype]
  push_cast
  exact Finset.sum_congr rfl fun j _ ↦ h j W

/-- Decomposition of a product from decompositions of the factors. -/
def Decomp.prod {P Q : FDMod k A} (d₁ : Decomp P) (d₂ : Decomp Q) : Decomp (FDMod.prod P Q) where
  ι := d₁.ι ⊕ d₂.ι
  obj := Sum.elim d₁.obj d₂.obj
  indec := fun | .inl i => d₁.indec i | .inr i => d₂.indec i
  nt := fun | .inl i => d₁.nt i | .inr i => d₂.nt i
  inc := fun
    | .inl i => FDMod.ofLin (LinearMap.inl A P Q ∘ₗ FDMod.lin (d₁.inc i))
    | .inr i => FDMod.ofLin (LinearMap.inr A P Q ∘ₗ FDMod.lin (d₂.inc i))
  proj := fun
    | .inl i => FDMod.ofLin (FDMod.lin (d₁.proj i) ∘ₗ LinearMap.fst A P Q)
    | .inr i => FDMod.ofLin (FDMod.lin (d₂.proj i) ∘ₗ LinearMap.snd A P Q)
  sum_id := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.sum_apply, Fintype.sum_sum_type]
    change (∑ i, ((FDMod.lin (d₁.inc i) (FDMod.lin (d₁.proj i) x.1), (0 : Q)) : P × Q)) +
      (∑ i, (((0 : P), FDMod.lin (d₂.inc i) (FDMod.lin (d₂.proj i) x.2)) : P × Q)) = x
    have h1 := LinearMap.congr_fun d₁.sum_id x.1
    have h2 := LinearMap.congr_fun d₂.sum_id x.2
    rw [LinearMap.sum_apply] at h1 h2
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_sum, Prod.fst_sum]
      simp only [Finset.sum_const_zero, add_zero]
      exact h1
    · rw [Prod.snd_add, Prod.snd_sum, Prod.snd_sum]
      simp only [Finset.sum_const_zero, zero_add]
      exact h2
  retr := fun
    | .inl i => LinearMap.ext fun x ↦ LinearMap.congr_fun (d₁.retr i) x
    | .inr i => LinearMap.ext fun x ↦ LinearMap.congr_fun (d₂.retr i) x
  orth := fun
    | .inl i, .inl j, h => LinearMap.ext fun x ↦
        LinearMap.congr_fun (d₁.orth i j fun e ↦ h (congrArg Sum.inl e)) x
    | .inl i, .inr j, _ => LinearMap.ext fun x ↦ by
        change FDMod.lin (d₂.proj j) (0 : Q) = 0
        exact map_zero _
    | .inr i, .inl j, _ => LinearMap.ext fun x ↦ by
        change FDMod.lin (d₁.proj j) (0 : P) = 0
        exact map_zero _
    | .inr i, .inr j, h => LinearMap.ext fun x ↦
        LinearMap.congr_fun (d₂.orth i j fun e ↦ h (congrArg Sum.inr e)) x

/-- The decomposition of the zero object. -/
def Decomp.zero : Decomp (FDMod.zero k A) where
  ι := PEmpty.{u+1}
  obj := PEmpty.elim
  indec := fun i ↦ i.elim
  nt := fun i ↦ i.elim
  inc := fun i ↦ i.elim
  proj := fun i ↦ i.elim
  sum_id := LinearMap.ext fun x ↦ Subsingleton.elim _ _
  retr := fun i ↦ i.elim
  orth := fun i ↦ i.elim

/-- The decomposition of an indecomposable. -/
def Decomp.single {X : FDMod k A} (hX : IndNT X) : Decomp X where
  ι := PUnit.{u+1}
  obj := fun _ ↦ X
  indec := fun _ ↦ hX.1
  nt := fun _ ↦ hX.2
  inc := fun _ ↦ 𝟙 X
  proj := fun _ ↦ 𝟙 X
  sum_id := by simp
  retr := fun _ ↦ rfl
  orth := fun i j h ↦ absurd (Subsingleton.elim i j) h

/-- **Sums of indecomposable projectives decompose into them.** -/
def decompSumProj (hT : ∀ x, x ∈ D.T) : ∀ l : List D.ι, Decomp (sumProj D l)
  | [] => Decomp.zero
  | i :: l => (Decomp.single (D.projIndNT i (hT i))).prod (decompSumProj hT l)

lemma eulerProj_decompSumProj (hT : ∀ x, x ∈ D.T) :
    ∀ (l : List D.ι) (j : (decompSumProj D hT l).ι), EulerProj D ((decompSumProj D hT l).obj j)
  | [], j => j.elim
  | i :: l, .inl _ => eulerProj_projE D hT i
  | i :: l, .inr j => eulerProj_decompSumProj hT l j

/-- **Direct summands of sums of indecomposable projectives are Euler-projective.** -/
theorem eulerProj_of_summand (hT : ∀ x, x ∈ D.T) {K : FDMod k A} (l : List D.ι)
    (s : K ⟶ sumProj D l) (r : sumProj D l ⟶ K) (hsr : s ≫ r = 𝟙 K) : EulerProj D K := by
  obtain ⟨d⟩ := FDMod.exists_decomp K
  refine EulerProj.of_decomp D d fun j ↦ ?_
  obtain ⟨i, g, hg⟩ := iso_summand_of_splitMono (X := d.obj j) ⟨d.indec j, d.nt j⟩
    (decompSumProj D hT l) (d.inc j ≫ s) (r ≫ d.proj j) (by
      change (d.inc j ≫ (s ≫ r)) ≫ d.proj j = 𝟙 _
      rw [hsr, Category.comp_id]
      exact ((FDMod.comp_eq_id_iff _ _).2 (d.retr j)))
  let e := LinearEquiv.ofBijective (FDMod.lin g) hg
  exact (eulerProj_decompSumProj D hT l i).of_bijective D
    (show (decompSumProj D hT l).obj i ⟶ d.obj j from (FDMod.ofLin (e.symm.toLinearMap))) e.symm.bijective

end LargeIndecomposable.AR

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- **The Euler form of a rigid module of projective dimension at most one.** If the kernel of a
cover of `Z` by indecomposable projectives is a direct summand of a sum of indecomposable
projectives, and every extension of `Z` by `W` splits, then `⟨dim Z, dim W⟩ = dim Hom(Z, W)`. -/
theorem euler_eq_hom_of_pd_one (hT : ∀ x, x ∈ D.T) {Z W : FDMod k A}
    (L : List (Σ i : D.ι, eSub Z (D.e i))) (hL : Function.Surjective (sumMap D Z L))
    (l : List D.ι) (s : FDMod.ofSub (LinearMap.ker (sumMap D Z L)) ⟶ sumProj D l)
    (r : sumProj D l ⟶ FDMod.ofSub (LinearMap.ker (sumMap D Z L))) (hsr : s ≫ r = 𝟙 _)
    (hv : ExtVanish Z W) :
    euler D (dimZ D Z) (dimZ D W) = finrank k (Z →ₗ[A] W) :=
  euler_eq_hom_of_extVanish D (eulerProj_sumProj D hT _) (eulerProj_of_summand D hT l s r hsr)
    (LinearMap.ker (sumMap D Z L)).subtype (sumMap D Z L) Subtype.val_injective hL
    (Submodule.range_subtype _) W hv

end LargeIndecomposable.AR
