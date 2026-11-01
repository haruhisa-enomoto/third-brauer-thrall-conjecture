module

public import LargeIndecomposable.Modules.Duality.Duality

/-!
# Left almost split maps

Dual morphisms (`trOp`, `trUnop`) and the double-dual identities let us transport the existence
of right almost split maps over `Aᵐᵒᵖ` to left almost split maps over `A`
(`FDMod.exists_leftAS`): for `X` with local endomorphism ring, take a right almost split
`g : E' → D X` and put `f = D g ∘ ev : X → D E'`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module MulOpposite

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `f` is left almost split. -/
def IsLeftAS {X E : FDMod k A} (f : X ⟶ E) : Prop :=
  (¬∃ r : E ⟶ X, f ≫ r = 𝟙 X) ∧
    ∀ (W : FDMod k A) (u : X ⟶ W), (¬∃ r : W ⟶ X, u ≫ r = 𝟙 X) → ∃ v : E ⟶ W, f ≫ v = u

section Transpose

variable {M M' : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup M'] [Module A M'] [Module k M'] [IsScalarTower k A M']

/-- The dual of an `A`-linear map. -/
def trOp (f : M →ₗ[A] M') : DOp (k := k) A M' →ₗ[Aᵐᵒᵖ] DOp (k := k) A M where
  toFun φ := show Module.Dual k M from (show Module.Dual k M' from φ).comp (f.restrictScalars k)
  map_add' φ ψ := rfl
  map_smul' a φ := by
    apply LinearMap.ext
    intro m
    exact congrArg (show Module.Dual k M' from φ) (f.map_smul (unop a) m).symm

lemma trOp_apply (f : M →ₗ[A] M') (φ : DOp (k := k) A M') (m : M) :
    (show Module.Dual k M from trOp f φ) m = (show Module.Dual k M' from φ) (f m) := rfl

end Transpose

section TransposeU

variable {N N' : Type u} [AddCommGroup N] [Module Aᵐᵒᵖ N] [Module k N] [IsScalarTower k Aᵐᵒᵖ N]
  [AddCommGroup N'] [Module Aᵐᵒᵖ N'] [Module k N'] [IsScalarTower k Aᵐᵒᵖ N']

/-- The dual of an `Aᵐᵒᵖ`-linear map. -/
def trUnop (f : N →ₗ[Aᵐᵒᵖ] N') : DUnop (k := k) A N' →ₗ[A] DUnop (k := k) A N where
  toFun φ := show Module.Dual k N from (show Module.Dual k N' from φ).comp (f.restrictScalars k)
  map_add' φ ψ := rfl
  map_smul' a φ := by
    apply LinearMap.ext
    intro m
    exact congrArg (show Module.Dual k N' from φ) (f.map_smul (op a) m).symm

lemma trUnop_apply (f : N →ₗ[Aᵐᵒᵖ] N') (φ : DUnop (k := k) A N') (n : N) :
    (show Module.Dual k N from trUnop f φ) n = (show Module.Dual k N' from φ) (f n) := rfl

/-- Evaluation `N → D (D N)` for `Aᵐᵒᵖ`-modules. -/
def evOp : N →ₗ[Aᵐᵒᵖ] DOp (k := k) A (DUnop (k := k) A N) where
  toFun n := show Module.Dual k (Module.Dual k N) from Module.Dual.eval k N n
  map_add' n n' := by
    show Module.Dual.eval k N (n + n') = Module.Dual.eval k N n + Module.Dual.eval k N n'
    exact map_add _ _ _
  map_smul' a n := by
    apply LinearMap.ext
    intro f
    rfl

lemma evOp_bijective [FiniteDimensional k N] : Function.Bijective (evOp (k := k) (A := A) (N := N)) :=
  (Module.evalEquiv k N).bijective

end TransposeU

/-! ### Objects -/

/-- The dual of a finite-dimensional `A`-module, as an `Aᵐᵒᵖ`-module. -/
def FDMod.dop (X : FDMod k A) : FDMod k Aᵐᵒᵖ where
  carrier := DOp (k := k) A X
  isFD := inferInstanceAs (FiniteDimensional k (Module.Dual k X))

/-- The dual of a finite-dimensional `Aᵐᵒᵖ`-module, as an `A`-module. -/
def FDMod.dunop (Y : FDMod k Aᵐᵒᵖ) : FDMod k A where
  carrier := DUnop (k := k) A Y
  isFD := inferInstanceAs (FiniteDimensional k (Module.Dual k Y))

/-- The evaluation isomorphism `X ≅ D (D X)` as a linear equivalence. -/
def evEquivA (X : FDMod k A) : X ≃ₗ[A] (FDMod.dunop (FDMod.dop X)) :=
  LinearEquiv.ofBijective (evA (k := k) (A := A) X) (evA_bijective X)

/-- The evaluation isomorphism `Y ≅ D (D Y)` as a linear equivalence. -/
def evEquivOp (Y : FDMod k Aᵐᵒᵖ) : Y ≃ₗ[Aᵐᵒᵖ] (FDMod.dop (FDMod.dunop Y)) :=
  LinearEquiv.ofBijective (evOp (k := k) (A := A) (N := Y)) (evOp_bijective)

section Raw

variable (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [FiniteDimensional k M]

/-- Evaluation as a linear equivalence. -/
def evEq : M ≃ₗ[A] DUnop (k := k) A (DOp (k := k) A M) :=
  LinearEquiv.ofBijective (evA (k := k) (A := A) M) (evA_bijective M)

lemma evEq_apply (m : M) (ξ : DOp (k := k) A M) :
    (show Module.Dual k (Module.Dual k M) from evEq (k := k) (A := A) M m) ξ =
      (show Module.Dual k M from ξ) m := rfl

/-- Every endomorphism of `D M` is the dual of an endomorphism of `M`. -/
lemma exists_trOp_eq (ψ : DOp (k := k) A M →ₗ[Aᵐᵒᵖ] DOp (k := k) A M) :
    ∃ φ : M →ₗ[A] M, trOp φ = ψ := by
  refine ⟨(evEq M).symm.toLinearMap ∘ₗ trUnop ψ ∘ₗ (evEq (k := k) (A := A) M).toLinearMap, ?_⟩
  apply LinearMap.ext
  intro ξ
  apply LinearMap.ext
  intro m
  rw [trOp_apply]
  have h := congrArg (fun t : DUnop (k := k) A (DOp (k := k) A M) ↦
    (show Module.Dual k (Module.Dual k M) from t) ξ)
    ((evEq M).apply_symm_apply (trUnop ψ (evEq (k := k) (A := A) M m)))
  exact h

lemma isLocalRing_dop [hX : IsLocalRing (Module.End A M)] :
    IsLocalRing (Module.End Aᵐᵒᵖ (DOp (k := k) A M)) := by
  have hnt : Nontrivial M := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (one_ne_zero : (1 : Module.End A M) ≠ 0) (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  have hdual : ∃ ξ : Module.Dual k M, ξ ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff k x).1 fun φ ↦ by rw [h φ]; rfl)
  haveI : Nontrivial (Module.End Aᵐᵒᵖ (DOp (k := k) A M)) := by
    refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨ξ, hξ⟩ := hdual
    exact hξ (LinearMap.congr_fun h (show DOp (k := k) A M from ξ))
  have hunit : ∀ φ : M →ₗ[A] M, IsUnit φ → IsUnit (trOp (k := k) φ) := by
    intro φ hφ
    obtain ⟨v, hv1, hv2⟩ := isUnit_iff_exists.1 hφ
    refine isUnit_iff_exists.2 ⟨trOp v, ?_, ?_⟩
    · apply LinearMap.ext; intro ξ; apply LinearMap.ext; intro m
      change (show Module.Dual k M from ξ) ((v * φ) m) = (show Module.Dual k M from ξ) m
      rw [hv2]; rfl
    · apply LinearMap.ext; intro ξ; apply LinearMap.ext; intro m
      change (show Module.Dual k M from ξ) ((φ * v) m) = (show Module.Dual k M from ξ) m
      rw [hv1]; rfl
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun ψ ↦ ?_
  obtain ⟨φ, rfl⟩ := exists_trOp_eq M ψ
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self φ with h | h
  · exact Or.inl (hunit φ h)
  · right
    have : (1 : Module.End Aᵐᵒᵖ (DOp (k := k) A M)) - trOp φ = trOp (1 - φ) := by
      apply LinearMap.ext; intro ξ; apply LinearMap.ext; intro m
      change (show Module.Dual k M from ξ) m - (show Module.Dual k M from ξ) (φ m) =
        (show Module.Dual k M from ξ) (m - φ m)
      rw [map_sub]
    rw [this]
    exact hunit _ h

end Raw

/-- **Left almost split maps exist** for modules with local endomorphism ring. -/
theorem FDMod.exists_leftAS [FiniteDimensional k A] (X : FDMod k A)
    [IsLocalRing (Module.End A X)] : ∃ (E : FDMod k A) (f : X ⟶ E), IsLeftAS f := by
  haveI : IsLocalRing (Module.End Aᵐᵒᵖ (FDMod.dop X)) := isLocalRing_dop (k := k) X
  obtain ⟨E', g, hg⟩ := FDMod.exists_rightAS (FDMod.dop X)
  let f : X →ₗ[A] FDMod.dunop E' := trUnop (FDMod.lin g) ∘ₗ evA (k := k) (A := A) X
  have hf : ∀ (m : X) (e : E'), (show Module.Dual k E' from f m) e =
      (show Module.Dual k X from FDMod.lin g e) m := fun _ _ ↦ rfl
  refine ⟨FDMod.dunop E', f, ⟨fun ⟨r, hr⟩ ↦ hg.1 ⟨?_, ?_⟩, fun W u hu ↦ ?_⟩⟩
  · exact (evEquivOp E').symm.toLinearMap ∘ₗ trOp (FDMod.lin r)
  · apply LinearMap.ext; intro ξ; apply LinearMap.ext; intro m
    have h1 := congrArg (fun t : FDMod.dop (FDMod.dunop E') ↦
      (show Module.Dual k (FDMod.dunop E') from t) (f m))
      ((evEquivOp E').apply_symm_apply (trOp (FDMod.lin r) ξ))
    have h2 : FDMod.lin r (f m) = m := LinearMap.congr_fun hr m
    change (show Module.Dual k (FDMod.dunop E') from evOp (k := k) (A := A) (N := E')
      ((evEquivOp E').symm (trOp (FDMod.lin r) ξ))) (f m) = (show Module.Dual k X from ξ)
        (FDMod.lin r (f m)) at h1
    rw [h2] at h1
    exact h1
  · haveI : IsScalarTower k Aᵐᵒᵖ (FDMod.dop W) :=
      inferInstanceAs (IsScalarTower k Aᵐᵒᵖ (DOp (k := k) A W))
    have hnot : ¬∃ s : FDMod.dop X ⟶ FDMod.dop W, s ≫ trOp (FDMod.lin u) = 𝟙 _ := by
      rintro ⟨s, hs⟩
      refine hu ⟨(evEq (k := k) (A := A) X).symm.toLinearMap ∘ₗ
        trUnop (k := k) (A := A) (FDMod.lin s) ∘ₗ evA (k := k) (A := A) W, ?_⟩
      apply LinearMap.ext; intro m
      apply (evEq (k := k) (A := A) X).injective
      change (evEq (k := k) (A := A) X) ((evEq (k := k) (A := A) X).symm
        (trUnop (k := k) (A := A) (FDMod.lin s) (evA (k := k) (A := A) W (FDMod.lin u m)))) =
          (evEq (k := k) (A := A) X) m
      refine (LinearEquiv.apply_symm_apply _ _).trans ?_
      apply LinearMap.ext; intro ξ
      change (show Module.Dual k W from FDMod.lin s ξ) (FDMod.lin u m) =
        (show Module.Dual k X from ξ) m
      exact congrArg (fun t ↦ (show Module.Dual k X from t) m) (LinearMap.congr_fun hs ξ)
    obtain ⟨v, hv⟩ := hg.2 (FDMod.dop W) (trOp (FDMod.lin u)) hnot
    refine ⟨(evEq (k := k) (A := A) W).symm.toLinearMap ∘ₗ
      trUnop (k := k) (A := A) (FDMod.lin v), ?_⟩
    apply LinearMap.ext; intro m
    apply (evEq (k := k) (A := A) W).injective
    change (evEq (k := k) (A := A) W) ((evEq (k := k) (A := A) W).symm
      (trUnop (k := k) (A := A) (FDMod.lin v) (f m))) = (evEq (k := k) (A := A) W) (FDMod.lin u m)
    refine (LinearEquiv.apply_symm_apply _ _).trans ?_
    apply LinearMap.ext; intro ζ
    change (show Module.Dual k X from FDMod.lin g (FDMod.lin v ζ)) m =
      (show Module.Dual k W from ζ) (FDMod.lin u m)
    exact congrArg (fun t ↦ (show Module.Dual k X from t) m) (LinearMap.congr_fun hv ζ)

end LargeIndecomposable.AR
