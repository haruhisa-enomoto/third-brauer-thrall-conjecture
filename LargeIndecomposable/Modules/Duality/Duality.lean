module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.MinimalRAS

/-!
# The `k`-dual of a finite-dimensional module

For a finite-dimensional `A`-module `M`, the dual `D M = Hom_k(M, k)` is an `Aᵐᵒᵖ`-module by
precomposition (`dualOp`), and for an `Aᵐᵒᵖ`-module `N` the dual is an `A`-module (`dualUnop`).
Evaluation identifies `M` with `D (D M)` (`evEquiv`), `A`-linearly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module MulOpposite

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Multiplication by `a`, as a `k`-linear map. -/
def smulK (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (a : A) :
    M →ₗ[k] M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := by rw [RingHom.id_apply]; exact smul_algebra_smul_comm c a m

section Op

variable (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The action of `Aᵐᵒᵖ` on `D M` by precomposition. -/
def dualActOp : Aᵐᵒᵖ →+* Module.End k (Module.Dual k M) where
  toFun a := Module.Dual.transpose (R := k) (smulK M (unop a))
  map_one' := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply]
  map_mul' a b := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply, mul_smul]
  map_zero' := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply]
  map_add' a b := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply, add_smul]

/-- `D M` as a type synonym carrying the `Aᵐᵒᵖ`-action. -/
@[nolint unusedArguments]
def DOp (_A : Type u) [Ring _A] [Algebra k _A] (M : Type u) [AddCommGroup M] [Module _A M]
    [Module k M] [IsScalarTower k _A M] : Type u := Module.Dual k M

instance : AddCommGroup (DOp (k := k) A M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (DOp (k := k) A M) := inferInstanceAs (Module k (Module.Dual k M))
instance : Module Aᵐᵒᵖ (DOp (k := k) A M) :=
  Module.compHom (Module.Dual k M) (dualActOp (k := k) (A := A) M)

lemma DOp.smul_apply (a : Aᵐᵒᵖ) (f : DOp (k := k) A M) (m : M) :
    (show Module.Dual k M from a • f) m = (show Module.Dual k M from f) (unop a • m) := rfl

instance : IsScalarTower k Aᵐᵒᵖ (DOp (k := k) A M) where
  smul_assoc c a f := by
    show (show Module.Dual k M from (c • a) • f) = c • (show Module.Dual k M from a • f)
    apply LinearMap.ext
    intro m
    rw [DOp.smul_apply, LinearMap.smul_apply, DOp.smul_apply, MulOpposite.unop_smul, smul_assoc,
      map_smul]

end Op

section Unop

variable (N : Type u) [AddCommGroup N] [Module Aᵐᵒᵖ N] [Module k N] [IsScalarTower k Aᵐᵒᵖ N]

/-- The action of `A` on `D N` for an `Aᵐᵒᵖ`-module `N`. -/
def dualActUnop : A →+* Module.End k (Module.Dual k N) where
  toFun a := Module.Dual.transpose (R := k) (smulK (A := Aᵐᵒᵖ) N (op a))
  map_one' := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply]
  map_mul' a b := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply, mul_smul]
  map_zero' := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply]
  map_add' a b := by
    ext f m
    simp [smulK, Module.Dual.transpose_apply, add_smul]

/-- `D N` as an `A`-module. -/
@[nolint unusedArguments]
def DUnop (_A : Type u) [Ring _A] [Algebra k _A] (N : Type u) [AddCommGroup N] [Module _Aᵐᵒᵖ N]
    [Module k N] [IsScalarTower k _Aᵐᵒᵖ N] : Type u := Module.Dual k N

instance : AddCommGroup (DUnop (k := k) A N) := inferInstanceAs (AddCommGroup (Module.Dual k N))
instance : Module k (DUnop (k := k) A N) := inferInstanceAs (Module k (Module.Dual k N))
instance : Module A (DUnop (k := k) A N) :=
  Module.compHom (Module.Dual k N) (dualActUnop (k := k) (A := A) N)

lemma DUnop.smul_apply (a : A) (f : DUnop (k := k) A N) (n : N) :
    (show Module.Dual k N from a • f) n = (show Module.Dual k N from f) (op a • n) := rfl

instance : IsScalarTower k A (DUnop (k := k) A N) where
  smul_assoc c a f := by
    show (show Module.Dual k N from (c • a) • f) = c • (show Module.Dual k N from a • f)
    apply LinearMap.ext
    intro m
    rw [DUnop.smul_apply, LinearMap.smul_apply, DUnop.smul_apply, MulOpposite.op_smul, smul_assoc,
      map_smul]

end Unop

section Eval

variable (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- Evaluation `M → D (D M)`, an `A`-linear map. -/
def evA : M →ₗ[A] DUnop (k := k) A (DOp (k := k) A M) where
  toFun m := show Module.Dual k (Module.Dual k M) from Module.Dual.eval k M m
  map_add' m m' := by
    show Module.Dual.eval k M (m + m') = Module.Dual.eval k M m + Module.Dual.eval k M m'
    exact map_add _ _ _
  map_smul' a m := by
    show Module.Dual.eval k M (a • m) = (show Module.Dual k (Module.Dual k M) from
      a • (show DUnop (k := k) A (DOp (k := k) A M) from Module.Dual.eval k M m))
    apply LinearMap.ext
    intro f
    rfl

lemma evA_bijective [FiniteDimensional k M] : Function.Bijective (evA (k := k) (A := A) M) :=
  (Module.evalEquiv k M).bijective

end Eval

end LargeIndecomposable.AR
