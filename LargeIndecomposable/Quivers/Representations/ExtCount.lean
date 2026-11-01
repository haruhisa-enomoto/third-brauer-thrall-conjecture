module

public import LargeIndecomposable.Quivers.Representations.RepresentationExtensions

/-!
# Counting cocycles

For a finite family of relations `ρ_r ∈ e_{t r} kD e_{s r}`, the extension blocks `crossA z ρ_r`
live in one block `X(s r) → Y(t r)` (`crossA_eq_block`). Hence the cocycles
`{z | crossA z ρ_r = 0 ∀ r}` have codimension at most `Σ_r dim X(s r) · dim Y(t r)` in the
space of extension data (`finrank_data_le`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.FinQuiver.Ext

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D : FinQuiver} {X Y : Rep k D}

lemma crossA_vertex (z : Data X Y) (v : D.V) : crossA z (FinQuiver.vertex k D v) = 0 := by
  unfold crossA
  rw [act_vertex, ← LinearMap.comp_assoc, πY_idm, LinearMap.comp_assoc, πY_ιX,
    LinearMap.comp_zero]

/-- A finite family of relations, each between two vertices. -/
structure RelFam (D : FinQuiver) (k : Type u) [Field k] where
  /-- The number of relations. -/
  m : ℕ
  /-- The relations. -/
  ρ : Fin m → D.PathAlgebra k
  /-- Their sources. -/
  s : Fin m → D.V
  /-- Their targets. -/
  t : Fin m → D.V
  corner : ∀ r, ρ r = FinQuiver.vertex k D (t r) * ρ r * FinQuiver.vertex k D (s r)

variable (F : RelFam D k)

lemma crossA_corner (z : Data X Y) (r : Fin F.m) :
    crossA z (F.ρ r) = Y.idm (F.t r) ∘ₗ crossA z (F.ρ r) ∘ₗ X.idm (F.s r) := by
  conv_lhs => rw [F.corner r]
  rw [crossA_mul, crossA_mul, crossA_vertex, crossA_vertex, act_vertex, act_vertex,
    LinearMap.zero_comp, add_zero, LinearMap.comp_zero, zero_add, LinearMap.comp_assoc]

/-- The block of `crossA z ρ_r`. -/
def blockL (r : Fin F.m) : Data X Y →ₗ[k] (X.obj (F.s r) →ₗ[k] Y.obj (F.t r)) where
  toFun z := LinearMap.proj (φ := fun i ↦ Y.obj i) (F.t r) ∘ₗ crossA z (F.ρ r) ∘ₗ
    LinearMap.single k (fun i ↦ X.obj i) (F.s r)
  map_add' z z' := by rw [crossA_add_left, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c z := by rw [crossA_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]; rfl

/-- The block map of the family. -/
def blocksL : Data X Y →ₗ[k] ∀ r : Fin F.m, X.obj (F.s r) →ₗ[k] Y.obj (F.t r) :=
  LinearMap.pi fun r ↦ blockL F r

/-- The cocycles of the family. -/
def cocycles : Submodule k (Data X Y) := LinearMap.ker (blocksL F (X := X) (Y := Y))

lemma mem_cocycles (z : Data X Y) : z ∈ cocycles F ↔ ∀ r, crossA z (F.ρ r) = 0 := by
  constructor
  · intro h r
    have hb : blockL F r z = 0 := congrFun h r
    rw [crossA_corner F z r]
    refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
    simp only [LinearMap.comp_apply, Rep.idm_apply, LinearMap.zero_apply, Pi.zero_apply]
    by_cases hj : j = F.t r
    · subst hj
      rw [Pi.single_eq_same]
      have := LinearMap.congr_fun hb (x (F.s r))
      simpa [blockL] using this
    · rw [Pi.single_eq_of_ne hj]
  · intro h
    funext r
    change blockL F r z = 0
    refine LinearMap.ext fun x ↦ ?_
    change (crossA z (F.ρ r) (Pi.single (F.s r) x)) (F.t r) = 0
    rw [h r]
    rfl

/-- The block-diagonal map of vertex maps. -/
def diagOp (h : ∀ i, X.obj i →ₗ[k] Y.obj i) : X.Tot →ₗ[k] Y.Tot :=
  LinearMap.pi fun i ↦ h i ∘ₗ LinearMap.proj (φ := fun i ↦ X.obj i) i

lemma diagOp_idm (h : ∀ i, X.obj i →ₗ[k] Y.obj i) (v : D.V) :
    diagOp h ∘ₗ X.idm v = Y.idm v ∘ₗ diagOp h := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  simp only [diagOp, LinearMap.comp_apply, Rep.idm_apply, LinearMap.pi_apply,
    LinearMap.coe_proj, Function.eval]
  by_cases hj : j = v
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

lemma zOp_cob (h : ∀ i, X.obj i →ₗ[k] Y.obj i) (e : D.A) :
    zOp (cob X Y h) e = diagOp h ∘ₗ X.arrOp e - Y.arrOp e ∘ₗ diagOp h := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  simp only [zOp, cob, diagOp, LinearMap.comp_apply, LinearMap.sub_apply, Rep.arrOp_apply,
    LinearMap.pi_apply, LinearMap.coe_proj, Function.eval, LinearMap.coe_single, Pi.sub_apply]
  by_cases hj : j = D.tgt e
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

lemma cross_cob (h : ∀ i, X.obj i →ₗ[k] Y.obj i) : ∀ le : List D.A,
    cross (cob X Y h) le = diagOp h ∘ₗ X.pathTot le - Y.pathTot le ∘ₗ diagOp h
  | [] => by simp [cross, Rep.pathTot]
  | e :: le => by
    simp only [cross, cross_cob h le, zOp_cob, Rep.pathTot, LinearMap.comp_sub,
      LinearMap.sub_comp, LinearMap.comp_assoc]
    abel

/-- **The extension block of a coboundary.** -/
lemma crossA_cob (h : ∀ i, X.obj i →ₗ[k] Y.obj i) (a : D.PathAlgebra k) :
    crossA (cob X Y h) a = diagOp h ∘ₗ act X a - act Y a ∘ₗ diagOp h := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · rw [crossA_vertex, act_vertex, act_vertex, diagOp_idm, sub_self]
    · have h1 : crossA (cob X Y h) (FinQuiver.word k D l) = cross (cob X Y h) l := by
        unfold crossA; rw [act_word, cross_eq]
      rw [h1, act_word, act_word, cross_cob]
  | zero => simp [crossA]
  | add a b _ _ ha hb =>
    have : crossA (cob X Y h) (a + b) = crossA (cob X Y h) a + crossA (cob X Y h) b := by
      simp [crossA, LinearMap.add_comp, LinearMap.comp_add]
    rw [this, ha, hb]
    simp only [act, map_add, LinearMap.comp_add, LinearMap.add_comp]
    abel
  | smul c a _ ha =>
    have : crossA (cob X Y h) (c • a) = c • crossA (cob X Y h) a := by
      simp [crossA, LinearMap.smul_comp, LinearMap.comp_smul]
    rw [this, ha]
    simp only [act, map_smul, LinearMap.comp_smul, LinearMap.smul_comp, smul_sub]

/-- **Coboundaries are cocycles** when both layers satisfy the relations. -/
lemma cob_mem_cocycles (hX : ∀ r, act X (F.ρ r) = 0) (hY : ∀ r, act Y (F.ρ r) = 0)
    (h : ∀ i, X.obj i →ₗ[k] Y.obj i) : cob X Y h ∈ cocycles F := by
  rw [mem_cocycles]
  intro r
  rw [crossA_cob, hX, hY, LinearMap.comp_zero, LinearMap.zero_comp, sub_self]

variable [∀ i, FiniteDimensional k (X.obj i)] [∀ i, FiniteDimensional k (Y.obj i)]

/-- **The cocycles have codimension at most `Σ_r dim X(s r) · dim Y(t r)`.** -/
theorem finrank_data_le :
    Module.finrank k (Data X Y) ≤ Module.finrank k (cocycles F (X := X) (Y := Y)) +
      ∑ r, Module.finrank k (X.obj (F.s r)) * Module.finrank k (Y.obj (F.t r)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (blocksL F (X := X) (Y := Y))
  have h2 := Submodule.finrank_le (LinearMap.range (blocksL F (X := X) (Y := Y)))
  rw [Module.finrank_pi_fintype] at h2
  simp only [Module.finrank_linearMap] at h2
  unfold cocycles
  have : ∑ r, Module.finrank k (X.obj (F.s r)) * Module.finrank k (Y.obj (F.t r)) =
      ∑ r, Module.finrank k (Y.obj (F.t r)) * Module.finrank k (X.obj (F.s r)) :=
    Finset.sum_congr rfl fun r _ ↦ Nat.mul_comm _ _
  omega

/-- **Hom bounded by the bilinear form when all extensions split.** If every cocycle is a
coboundary, then `dim Hom(X, Y) + Σ_α x_{s α} y_{t α} ≤ Σ_i x_i y_i + Σ_r x_{s r} y_{t r}`,
where `Hom(X, Y)` is the kernel of the coboundary map. -/
theorem finrank_ker_cob_le (hX : ∀ r, act X (F.ρ r) = 0) (hY : ∀ r, act Y (F.ρ r) = 0)
    (hsplit : cocycles F (X := X) (Y := Y) ≤ LinearMap.range (cobL (X := X) (Y := Y))) :
    Module.finrank k (LinearMap.ker (cobL (X := X) (Y := Y))) +
        ∑ α : D.A, Module.finrank k (X.obj (D.src α)) * Module.finrank k (Y.obj (D.tgt α)) ≤
      ∑ i, Module.finrank k (X.obj i) * Module.finrank k (Y.obj i) +
        ∑ r, Module.finrank k (X.obj (F.s r)) * Module.finrank k (Y.obj (F.t r)) := by
  have h1 := finrank_data_le F (X := X) (Y := Y)
  have h2 := LinearMap.finrank_range_add_finrank_ker (cobL (X := X) (Y := Y))
  have h3 := Submodule.finrank_mono hsplit
  have hdata : Module.finrank k (Data X Y) =
      ∑ α : D.A, Module.finrank k (X.obj (D.src α)) * Module.finrank k (Y.obj (D.tgt α)) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  have hdom : Module.finrank k (∀ i, X.obj i →ₗ[k] Y.obj i) =
      ∑ i, Module.finrank k (X.obj i) * Module.finrank k (Y.obj i) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  omega

end LargeIndecomposable.FinQuiver.Ext
