module

public import LargeIndecomposable.Cleaving.ClosedChains.SupplementRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

/-- The target-oriented `tau`-power tail in a cyclic Hom space. -/
def targetPowerTail {X Y : C} (pi : X ⟶ Y) (tau : End Y)
    (N : ℕ) : Submodule k (X ⟶ Y) :=
  Submodule.span k {f | ∃ m : ℕ, N ≤ m ∧ ∃ e : End Y,
    f = (pi ≫ (tau ^ m).asHom) ≫ e.asHom}

theorem targetPowerTail_generator_mem
    {X Y : C} (pi : X ⟶ Y) (tau : End Y)
    {N m : ℕ} (hm : N ≤ m) (e : End Y) :
    (pi ≫ (tau ^ m).asHom) ≫ e.asHom ∈
      targetPowerTail (k := k) pi tau N := by
  apply Submodule.subset_span
  exact ⟨m, hm, e, rfl⟩

/-- The source-oriented `tau`-power tail. -/
def sourcePowerTail {X Y : C} (pi : X ⟶ Y) (tau : End X)
    (N : ℕ) : Submodule k (X ⟶ Y) :=
  Submodule.span k {f | ∃ m : ℕ, N ≤ m ∧ ∃ e : End X,
    f = e.asHom ≫ ((tau ^ m).asHom ≫ pi)}

theorem sourcePowerTail_generator_mem
    {X Y : C} (pi : X ⟶ Y) (tau : End X)
    {N m : ℕ} (hm : N ≤ m) (e : End X) :
    e.asHom ≫ ((tau ^ m).asHom ≫ pi) ∈
      sourcePowerTail (k := k) pi tau N := by
  apply Submodule.subset_span
  exact ⟨m, hm, e, rfl⟩

/-- Minimal target-oriented alignment output needed from the BGRS power
calculation for one landing arrow.  The target-radical half of the endpoint
layer is automatic from `tauData`; the remaining source-radical and cross
inclusions are the two genuine alignment statements. -/
structure TargetPowerAlignedPathData
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) where
  pi : D.obj X ⟶ D.obj Y
  tau : End (D.obj Y)
  tau_mem_jacobson : tau ∈ Ring.jacobson (End (D.obj Y))
  tauData : TransitRadicalPowerData tau
  degree : ℕ
  landing_eq : D.map (LinearPathCategory.pathHom p) =
    pi ≫ (tau ^ degree).asHom
  landing_exact : D.map (LinearPathCategory.pathHom p) ∉
    targetPowerTail (k := k) pi tau (degree + 1)
  source_radical_raises : ∀ a : End (D.obj X),
    a ∈ Ring.jacobson (End (D.obj X)) →
      a.asHom ≫ D.map (LinearPathCategory.pathHom p) ∈
        targetPowerTail (k := k) pi tau (degree + 1)
  cross_raises : forbiddenCrossSubmodule (k := k) D X Y ≤
    targetPowerTail (k := k) pi tau (degree + 1)

namespace TargetPowerAlignedPathData

variable {n : ℕ}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]
variable {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
variable {p : Quiver.Path (LinearPathCategory.vertex Y)
  (LinearPathCategory.vertex X)}

/-- The complete endpoint radical layer raises target power degree. -/
theorem endpointRadical_le_nextPowerTail
    (h : TargetPowerAlignedPathData (k := k) D p) :
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      targetPowerTail (k := k) h.pi h.tau (h.degree + 1) := by
  rintro f ⟨a, ha, b, hb, rfl⟩
  apply Submodule.add_mem _ (h.source_radical_raises a ha)
  by_cases hb0 : b = 0
  · subst b
    change D.map (LinearPathCategory.pathHom p) ≫
      (0 : D.obj Y ⟶ D.obj Y) ∈ _
    simp
  · obtain ⟨m, hm, e, _he, hbe⟩ := h.tauData.factors b hb hb0
    have hpow : (h.tau ^ h.degree).asHom ≫ (h.tau ^ m).asHom =
        (h.tau ^ (m + h.degree)).asHom := by
      rw [← End.mul_def, ← pow_add]
    have hrewrite :
        (h.pi ≫ (h.tau ^ h.degree).asHom) ≫
            ((h.tau ^ m).asHom ≫ e.asHom) =
          (h.pi ≫ (h.tau ^ (m + h.degree)).asHom) ≫ e.asHom := by
      calc
        (h.pi ≫ (h.tau ^ h.degree).asHom) ≫
              ((h.tau ^ m).asHom ≫ e.asHom) =
            h.pi ≫ ((h.tau ^ h.degree).asHom ≫
              ((h.tau ^ m).asHom ≫ e.asHom)) := by
                rw [Category.assoc]
        _ = h.pi ≫ (((h.tau ^ h.degree).asHom ≫
              (h.tau ^ m).asHom) ≫ e.asHom) := by
                rw [Category.assoc]
        _ = h.pi ≫ ((h.tau ^ (m + h.degree)).asHom ≫ e.asHom) := by
              rw [hpow]
        _ = (h.pi ≫ (h.tau ^ (m + h.degree)).asHom) ≫ e.asHom := by
              rw [Category.assoc]
    rw [h.landing_eq, hbe]
    rw [hrewrite]
    exact targetPowerTail_generator_mem (k := k) h.pi h.tau
      (N := h.degree + 1) (m := m + h.degree) (by omega) e

/-- Target power alignment implies the exact supplement nonmembership. -/
theorem separated (h : TargetPowerAlignedPathData (k := k) D p) :
    D.map (LinearPathCategory.pathHom p) ∉
      pathSupplementObstruction (k := k) D p := by
  intro hmem
  apply h.landing_exact
  apply (sup_le h.endpointRadical_le_nextPowerTail h.cross_raises)
  exact hmem

end TargetPowerAlignedPathData

/-- Source-dual power-alignment package. -/
structure SourcePowerAlignedPathData
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) where
  pi : D.obj X ⟶ D.obj Y
  tau : End (D.obj X)
  tau_mem_jacobson : tau ∈ Ring.jacobson (End (D.obj X))
  tauData : CotransitRadicalPowerData tau
  degree : ℕ
  landing_eq : D.map (LinearPathCategory.pathHom p) =
    (tau ^ degree).asHom ≫ pi
  landing_exact : D.map (LinearPathCategory.pathHom p) ∉
    sourcePowerTail (k := k) pi tau (degree + 1)
  target_radical_raises : ∀ b : End (D.obj Y),
    b ∈ Ring.jacobson (End (D.obj Y)) →
      D.map (LinearPathCategory.pathHom p) ≫ b.asHom ∈
        sourcePowerTail (k := k) pi tau (degree + 1)
  cross_raises : forbiddenCrossSubmodule (k := k) D X Y ≤
    sourcePowerTail (k := k) pi tau (degree + 1)

namespace SourcePowerAlignedPathData

variable {n : ℕ}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]
variable {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
variable {p : Quiver.Path (LinearPathCategory.vertex Y)
  (LinearPathCategory.vertex X)}

/-- Source-dual endpoint radical inclusion. -/
theorem endpointRadical_le_nextPowerTail
    (h : SourcePowerAlignedPathData (k := k) D p) :
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      sourcePowerTail (k := k) h.pi h.tau (h.degree + 1) := by
  rintro f ⟨a, ha, b, hb, rfl⟩
  apply Submodule.add_mem _
  · by_cases ha0 : a = 0
    · subst a
      change (0 : D.obj X ⟶ D.obj X) ≫
        D.map (LinearPathCategory.pathHom p) ∈ _
      simp
    · obtain ⟨m, hm, e, _he, hae⟩ := h.tauData.factors a ha ha0
      have hpow : (h.tau ^ m).asHom ≫ (h.tau ^ h.degree).asHom =
          (h.tau ^ (h.degree + m)).asHom := by
        rw [← End.mul_def, ← pow_add]
      have hrewrite :
          (e.asHom ≫ (h.tau ^ m).asHom) ≫
              ((h.tau ^ h.degree).asHom ≫ h.pi) =
            e.asHom ≫ ((h.tau ^ (h.degree + m)).asHom ≫ h.pi) := by
        calc
          (e.asHom ≫ (h.tau ^ m).asHom) ≫
                ((h.tau ^ h.degree).asHom ≫ h.pi) =
              e.asHom ≫ ((h.tau ^ m).asHom ≫
                ((h.tau ^ h.degree).asHom ≫ h.pi)) := by
                  rw [Category.assoc]
          _ = e.asHom ≫ (((h.tau ^ m).asHom ≫
                (h.tau ^ h.degree).asHom) ≫ h.pi) := by
                  rw [Category.assoc]
          _ = e.asHom ≫ ((h.tau ^ (h.degree + m)).asHom ≫ h.pi) := by
                rw [hpow]
      rw [h.landing_eq, hae]
      rw [hrewrite]
      exact sourcePowerTail_generator_mem (k := k) h.pi h.tau
        (N := h.degree + 1) (m := h.degree + m) (by omega) e
  · exact h.target_radical_raises b hb

/-- Source power alignment implies exact supplement separation. -/
theorem separated (h : SourcePowerAlignedPathData (k := k) D p) :
    D.map (LinearPathCategory.pathHom p) ∉
      pathSupplementObstruction (k := k) D p := by
  intro hmem
  apply h.landing_exact
  apply (sup_le h.endpointRadical_le_nextPowerTail h.cross_raises)
  exact hmem

end SourcePowerAlignedPathData

/-- Either oriented BGRS power calculation is sufficient. -/
theorem separated_of_powerAlignment
    {n : ℕ}
    {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    {p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)}
    (h : TargetPowerAlignedPathData (k := k) D p ⊕
      SourcePowerAlignedPathData (k := k) D p) :
    D.map (LinearPathCategory.pathHom p) ∉
      pathSupplementObstruction (k := k) D p := by
  rcases h with h | h
  · exact h.separated
  · exact h.separated

end LargeIndecomposable.ClosedZigzagTransfer
