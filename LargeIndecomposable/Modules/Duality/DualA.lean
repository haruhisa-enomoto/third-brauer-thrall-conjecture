module

public import Mathlib

/-!
# The dual of a finite-dimensional algebra as a left module

For a `k`-algebra `A`, `DA k A = Hom_k(A, k)` is a left `A`-module by
`(a • λ)(b) = λ(b a)`. For a left `A`-module `W`, `Hom_A(W, DA)` is the `k`-dual of `W`
(`homDAEquiv`), and `Hom_A(W, DAⁿ)` is the dual of `Wⁿ` (`theta`, `thetaInv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

variable (k A : Type*) [Field k] [Ring A] [Algebra k A]

/-- `D A = Hom_k(A, k)`. -/
def DA : Type _ := A →ₗ[k] k

instance : AddCommGroup (DA k A) := inferInstanceAs (AddCommGroup (A →ₗ[k] k))
instance : Module k (DA k A) := inferInstanceAs (Module k (A →ₗ[k] k))

variable {k A}

/-- Evaluation of an element of `DA`. -/
def DA.ev (l : DA k A) (b : A) : k := (show A →ₗ[k] k from l) b

@[ext] lemma DA.ext {l m : DA k A} (h : ∀ b, l.ev b = m.ev b) : l = m :=
  LinearMap.ext h

/-- Build an element of `DA`. -/
def DA.mk (f : A →ₗ[k] k) : DA k A := f

@[simp] lemma DA.ev_mk (f : A →ₗ[k] k) (b : A) : (DA.mk f).ev b = f b := rfl

@[simp] lemma DA.ev_add (l m : DA k A) (b : A) : (l + m).ev b = l.ev b + m.ev b := rfl
@[simp] lemma DA.ev_zero (b : A) : (0 : DA k A).ev b = 0 := rfl
@[simp] lemma DA.ev_smul (c : k) (l : DA k A) (b : A) : (c • l).ev b = c * l.ev b := rfl
@[simp] lemma DA.ev_neg (l : DA k A) (b : A) : (-l).ev b = -l.ev b := rfl
@[simp] lemma DA.ev_sub (l m : DA k A) (b : A) : (l - m).ev b = l.ev b - m.ev b := rfl

lemma DA.ev_addB (l : DA k A) (b c : A) : l.ev (b + c) = l.ev b + l.ev c :=
  map_add (show A →ₗ[k] k from l) b c

lemma DA.ev_smulB (l : DA k A) (c : k) (b : A) : l.ev (c • b) = c * l.ev b :=
  map_smul (show A →ₗ[k] k from l) c b

lemma DA.ev_zeroB (l : DA k A) : l.ev 0 = 0 := map_zero (show A →ₗ[k] k from l)

lemma DA.ev_sum (l : DA k A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    l.ev (∑ i ∈ s, f i) = ∑ i ∈ s, l.ev (f i) :=
  map_sum (show A →ₗ[k] k from l) f s

@[simp] lemma DA.ev_finset_sum {ι : Type*} (s : Finset ι) (f : ι → DA k A) (b : A) :
    (∑ i ∈ s, f i).ev b = ∑ i ∈ s, (f i).ev b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, DA.ev_add, ih]

instance : SMul A (DA k A) where
  smul a l := DA.mk ((show A →ₗ[k] k from l).comp (LinearMap.mulRight k a))

@[simp] lemma DA.ev_smulA (a : A) (l : DA k A) (b : A) : (a • l).ev b = l.ev (b * a) := rfl

instance : Module A (DA k A) where
  one_smul l := DA.ext fun b ↦ by simp
  mul_smul a c l := DA.ext fun b ↦ by simp [mul_assoc]
  smul_zero a := DA.ext fun b ↦ by simp
  smul_add a l m := DA.ext fun b ↦ by simp
  add_smul a c l := DA.ext fun b ↦ by simp [mul_add, DA.ev_addB]
  zero_smul l := DA.ext fun b ↦ by simp [DA.ev_zeroB]

instance : IsScalarTower k A (DA k A) where
  smul_assoc c a l := DA.ext fun b ↦ by
    simp only [DA.ev_smulA, DA.ev_smul, mul_smul_comm, DA.ev_smulB]

instance : SMulCommClass A k (DA k A) where
  smul_comm a c l := DA.ext fun b ↦ by simp

instance : SMulCommClass k A (DA k A) where
  smul_comm c a l := DA.ext fun b ↦ by simp

variable {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

/-- `Hom_A(W, DA) → D W`, `φ ↦ (w ↦ φ(w)(1))`. -/
def homDAToDual (φ : W →ₗ[A] DA k A) : Module.Dual k W where
  toFun w := (φ w).ev 1
  map_add' x y := by simp
  map_smul' c x := by
    rw [LinearMap.map_smul_of_tower, DA.ev_smul]; rfl

/-- `D W → Hom_A(W, DA)`, `ℓ ↦ (w ↦ (b ↦ ℓ(b w)))`. -/
def dualToHomDA (l : Module.Dual k W) : W →ₗ[A] DA k A where
  toFun w := DA.mk
    { toFun b := l (b • w)
      map_add' b c := by rw [add_smul, map_add]
      map_smul' c b := by rw [smul_assoc, map_smul]; rfl }
  map_add' x y := DA.ext fun b ↦ by simp
  map_smul' a x := DA.ext fun b ↦ by simp [mul_smul]

@[simp] lemma dualToHomDA_ev (l : Module.Dual k W) (w : W) (b : A) :
    (dualToHomDA (A := A) l w).ev b = l (b • w) := rfl

@[simp] lemma homDAToDual_apply (φ : W →ₗ[A] DA k A) (w : W) :
    homDAToDual φ w = (φ w).ev 1 := rfl

lemma homDAToDual_dualToHomDA (l : Module.Dual k W) :
    homDAToDual (dualToHomDA (A := A) l) = l := by
  ext w; simp

lemma dualToHomDA_homDAToDual (φ : W →ₗ[A] DA k A) : dualToHomDA (homDAToDual φ) = φ := by
  ext w b
  simp only [dualToHomDA_ev, homDAToDual_apply, map_smul, DA.ev_smulA, one_mul]

end LargeIndecomposable.AR
