module

public import LargeIndecomposable.Quivers.PathAlgebras.FiniteQuiver
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Push-down of representations along a quiver morphism

For a morphism of finite quivers `p : D → Q` and a representation `X` of `D`,
the push-down `p_*X` of Construction 3.9 has `(p_*X)(q) = ⊕_{p(i) = q} X(i)`
and, along an arrow `c` of `Q`, the block `X(e) : X(i) → X(j)` for each arrow
`e : i → j` of `D` with label `c`. We realize it directly as a module over the
path algebra `kQ` on the total space `⊕_i X(i)` (`Rep.Tot`): the vertex
idempotent `e_q` acts as the projection onto `⊕_{p(i)=q} X(i)` and an arrow
`c` acts as the sum of the arrow operators of the arrows labelled `c`. For
`p` the identity this is the usual module of a representation of `Q`.

Maps of total spaces are handled through their blocks: `Rep.idm X i` is the
idempotent projection onto `X(i)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D Q : FinQuiver}

section Sums

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module k M]
  [Module k N] [Module k P] {ι : Type*}

lemma comp_finsetSum (g : N →ₗ[k] P) (s : Finset ι) (f : ι → M →ₗ[k] N) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext; simp

lemma finsetSum_comp (s : Finset ι) (f : ι → N →ₗ[k] P) (g : M →ₗ[k] N) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext; simp

end Sums

namespace Rep

/-- The total space `⊕_i X(i)` of a representation. -/
abbrev Tot (X : Rep k D) : Type u := ∀ i, X.obj i

variable (X : Rep k D)

/-- The idempotent projection of `⊕ X(i)` onto the summand `X(i)`. -/
def idm (i : D.V) : X.Tot →ₗ[k] X.Tot :=
  LinearMap.single k (fun i ↦ X.obj i) i ∘ₗ LinearMap.proj i

/-- The operator of an arrow `e : i → j`: the block `X(e) : X(i) → X(j)`. -/
def arrOp (e : D.A) : X.Tot →ₗ[k] X.Tot :=
  LinearMap.single k (fun i ↦ X.obj i) (D.tgt e) ∘ₗ (X.map e).hom ∘ₗ LinearMap.proj (D.src e)

lemma idm_apply (i : D.V) (x : X.Tot) : X.idm i x = Pi.single i (x i) := rfl

lemma arrOp_apply (e : D.A) (x : X.Tot) :
    X.arrOp e x = Pi.single (D.tgt e) ((X.map e).hom (x (D.src e))) := rfl

lemma idm_comp_idm (i j : D.V) : X.idm i ∘ₗ X.idm j = if i = j then X.idm i else 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  by_cases h : i = j
  · subst h; simp [idm_apply]
  · simp only [h, ite_false, LinearMap.comp_apply, idm_apply, LinearMap.zero_apply, Pi.zero_apply]
    rw [Pi.single_eq_of_ne h]
    simp

lemma arrOp_comp_idm (e : D.A) (i : D.V) :
    X.arrOp e ∘ₗ X.idm i = if D.src e = i then X.arrOp e else 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  by_cases h : D.src e = i
  · subst h; simp [idm_apply, arrOp_apply]
  · simp [idm_apply, arrOp_apply, h]

lemma idm_comp_arrOp (j : D.V) (e : D.A) :
    X.idm j ∘ₗ X.arrOp e = if j = D.tgt e then X.arrOp e else 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  by_cases h : j = D.tgt e
  · subst h; simp [idm_apply, arrOp_apply]
  · simp only [h, ite_false, LinearMap.comp_apply, idm_apply, arrOp_apply, LinearMap.zero_apply,
      Pi.zero_apply]
    rw [Pi.single_eq_of_ne h]
    simp

lemma sum_idm : ∑ i, X.idm i = LinearMap.id := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp [idm_apply, Pi.single_apply]

lemma idm_idm (i : D.V) : X.idm i ∘ₗ X.idm i = X.idm i := by
  simp [idm_comp_idm]

/-- A linear map of total spaces is determined by its blocks. -/
lemma ext_blocks {X Y : Rep k D} {f g : X.Tot →ₗ[k] Y.Tot}
    (h : ∀ j i, Y.idm j ∘ₗ f ∘ₗ X.idm i = Y.idm j ∘ₗ g ∘ₗ X.idm i) : f = g := by
  have e : ∀ f : X.Tot →ₗ[k] Y.Tot, f = ∑ j, ∑ i, Y.idm j ∘ₗ f ∘ₗ X.idm i := by
    intro f
    simp only [← comp_finsetSum, ← finsetSum_comp, sum_idm]
    rfl
  rw [e f, e g]
  simp only [h]

/-- A linear map of total spaces vanishes if all its columns vanish. -/
lemma eq_zero_of_comp_idm {X Y : Rep k D} {f : X.Tot →ₗ[k] Y.Tot}
    (h : ∀ i, f ∘ₗ X.idm i = 0) : f = 0 := by
  have : f = f ∘ₗ ∑ i, X.idm i := by rw [sum_idm]; rfl
  rw [this, comp_finsetSum]
  simp [h]

/-- The block of `f` from `X(i)` to `Y(j)`. -/
def blk {X Y : Rep k D} (f : X.Tot →ₗ[k] Y.Tot) (j i : D.V) : X.obj i →ₗ[k] Y.obj j :=
  LinearMap.proj j ∘ₗ f ∘ₗ LinearMap.single k (fun i ↦ X.obj i) i

lemma idm_comp_comp_idm {X Y : Rep k D} (f : X.Tot →ₗ[k] Y.Tot) (j i : D.V) :
    Y.idm j ∘ₗ f ∘ₗ X.idm i =
      LinearMap.single k (fun i ↦ Y.obj i) j ∘ₗ blk f j i ∘ₗ LinearMap.proj i := rfl

/-- A space that vanishes makes its idempotent zero. -/
lemma idm_eq_zero (i : D.V) [Subsingleton (X.obj i)] : X.idm i = 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp [idm_apply, Subsingleton.elim (x i) 0]

lemma arrOp_eq_zero_of_src (e : D.A) [Subsingleton (X.obj (D.src e))] : X.arrOp e = 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp [arrOp_apply, Subsingleton.elim (x (D.src e)) 0]

lemma arrOp_eq_zero_of_tgt (e : D.A) [Subsingleton (X.obj (D.tgt e))] : X.arrOp e = 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp [arrOp_apply, Subsingleton.elim ((X.map e).hom (x (D.src e))) 0]

end Rep

end LargeIndecomposable
