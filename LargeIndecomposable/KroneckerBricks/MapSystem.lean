module

public import LargeIndecomposable.KroneckerBricks.Transport

/-!
# Map systems and their `R_ω`-structures

A map system on a set `X` is a countable family of partial maps `fₑ : Dₑ → X`.
A linear map `φ` on `k^(X)` commutes with it if `φ(eᵢ) ∈ k^(Dₑ)` and
`φ(e_{fₑ i}) = (fₑ)_* φ(eᵢ)` for `i ∈ Dₑ`. The `R_ω`-structure
`k^(X) ⊕ k^(X)` with the two summands, the diagonal and the graphs of the
`(fₑ)_*` has as endomorphisms exactly the `φ ⊕ φ` with `φ` commuting
(`Rigid.isRigidR_of_isRigidSys`). This is the linear form of the relations of
Shelah (1974), Theorem 2.1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u

namespace Rigid

/-- A countable family of partial maps on `X`. -/
structure MapSystem (X : Type u) where
  /-- The domains. -/
  dom : ℕ → Set X
  /-- The maps (only their values on the domains matter). -/
  map : ℕ → X → X

variable {k : Type u} [Field k] {X : Type u}

/-- `φ` commutes with the map system. -/
def Commutes (M : MapSystem X) (φ : (X →₀ k) →ₗ[k] (X →₀ k)) : Prop :=
  ∀ e, ∀ i ∈ M.dom e, φ (Finsupp.single i 1) ∈ Finsupp.supported k k (M.dom e) ∧
    φ (Finsupp.single (M.map e i) 1) = Finsupp.mapDomain (M.map e) (φ (Finsupp.single i 1))

variable (k) in
/-- Only scalars commute with the map system. -/
def IsRigidSys (M : MapSystem X) : Prop :=
  ∀ φ : (X →₀ k) →ₗ[k] (X →₀ k), Commutes M φ → ∃ c : k, φ = c • LinearMap.id

variable (k) in
/-- The subspaces of the `R_ω`-structure of a map system. -/
def subN (M : MapSystem X) : ℕ → Submodule k ((X →₀ k) × (X →₀ k))
  | 0 => ⊤
  | 1 => LinearMap.range (LinearMap.inl k _ _)
  | 2 => LinearMap.range (LinearMap.inr k _ _)
  | 3 => LinearMap.range (LinearMap.id.prod LinearMap.id)
  | e + 4 => (Finsupp.supported k k (M.dom e)).map
      (LinearMap.id.prod (Finsupp.lmapDomain k k (M.map e)))

variable (k) in
/-- The `R_ω`-structure of a map system. -/
def subs (M : MapSystem X) : Bricks.Nu → Submodule k ((X →₀ k) × (X →₀ k)) :=
  fun n ↦ subN k M n.down

lemma subs_zero (M : MapSystem X) : subs k M 0 = ⊤ := rfl

theorem isRigidR_of_isRigidSys [Infinite k] {M : MapSystem X} (h : IsRigidSys k M) :
    Bricks.IsRigidR (subs k M) := by
  intro ψ hψ
  have h1 : ∀ x, (ψ (x, 0)).2 = 0 := fun x ↦ by
    obtain ⟨y, hy⟩ := hψ ⟨1⟩ (x, 0) ⟨x, rfl⟩
    rw [← hy]
    rfl
  have h2 : ∀ y, (ψ (0, y)).1 = 0 := fun y ↦ by
    obtain ⟨x, hx⟩ := hψ ⟨2⟩ (0, y) ⟨y, rfl⟩
    rw [← hx]
    rfl
  let φ1 := LinearMap.fst k _ _ ∘ₗ ψ ∘ₗ LinearMap.inl k _ _
  let φ2 := LinearMap.snd k _ _ ∘ₗ ψ ∘ₗ LinearMap.inr k _ _
  have hdiag : ∀ x, φ1 x = φ2 x := fun x ↦ by
    obtain ⟨z, hz⟩ := hψ ⟨3⟩ (x, x) ⟨x, rfl⟩
    have hz2 : (z, z) = ψ (x, x) := hz
    have e : ψ (x, x) = ψ (x, 0) + ψ (0, x) := by rw [← map_add]; simp
    have e1 := congrArg Prod.fst hz2
    have e2 := congrArg Prod.snd hz2
    rw [e] at e1 e2
    simp only [Prod.fst_add, Prod.snd_add, h1, h2, add_zero, zero_add] at e1 e2
    change (ψ (x, 0)).1 = (ψ (0, x)).2
    rw [← e1, ← e2]
  have hψxy : ∀ x y, ψ (x, y) = (φ1 x, φ1 y) := fun x y ↦ by
    have e : ψ (x, y) = ψ (x, 0) + ψ (0, y) := by rw [← map_add]; simp
    rw [e, hdiag y]
    ext
    · simp [h2]; rfl
    · simp [h1]; rfl
  obtain ⟨c, hc⟩ := h φ1 fun e i hi ↦ by
    obtain ⟨z, hz, hz'⟩ := hψ ⟨e + 4⟩ (Finsupp.single i 1, Finsupp.single (M.map e i) 1)
      ⟨Finsupp.single i 1, Finsupp.single_mem_supported k 1 hi, by simp⟩
    rw [hψxy] at hz'
    have hz2 : (z, Finsupp.mapDomain (M.map e) z) = (φ1 (Finsupp.single i 1),
      φ1 (Finsupp.single (M.map e i) 1)) := hz'
    have e1 := congrArg Prod.fst hz2
    have e2 := congrArg Prod.snd hz2
    simp only at e1 e2
    refine ⟨e1 ▸ hz, ?_⟩
    rw [← e2, e1]
  refine ⟨c, LinearMap.ext fun ⟨x, y⟩ ↦ ?_⟩
  rw [hψxy, hc]
  simp

end Rigid

end LargeIndecomposable
