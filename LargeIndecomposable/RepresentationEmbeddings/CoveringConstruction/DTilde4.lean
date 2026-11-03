module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerPair
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.SimpleInjectiveFacts

/-!
# Example: the Kronecker pair of `D̃₄`

The quiver `D̃₄` with four leaves pointing into the center. The simple `P` at
the first leaf and the brick `Q₀` with `k²` at the center and the three lines
`k(1,0)`, `k(0,1)`, `k(1,1)` at the other leaves have disjoint supports, and the
two coordinate maps `k → k²` on the arrow from the first leaf are independent
extension tuples. With the trivial covering this is covering data for the path
algebra of `D̃₄` (`DTilde4.pairCoveringData`): the covering alternative of
Theorem 3.14 for a tame hereditary algebra, recovering the classical embedding
of Kronecker modules into representations of `D̃₄`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement FinQuiver Rep

universe u

namespace DTilde4

/-- The quiver `D̃₄`: vertex `0` is the center, arrow `j` goes from leaf `j + 1` to
the center. -/
abbrev quiver : FinQuiver where
  V := Fin 5
  A := Fin 4
  src j := j.succ
  tgt _ := 0

variable (k : Type u) [Field k]

/-- The dimension vector of `P`. -/
abbrev dP : Fin 5 → ℕ
  | 1 => 1
  | _ => 0

/-- The dimension vector of `Q₀`. -/
abbrev dQ : Fin 5 → ℕ
  | 0 => 2
  | 1 => 0
  | _ => 1

/-- The map of `Q₀` along an arrow. -/
def qMap : ∀ j : Fin 4, (Fin (dQ j.succ) → k) →ₗ[k] (Fin (dQ 0) → k)
  | 0 => 0
  | 1 => LinearMap.pi fun r : Fin 2 ↦ if r = 0 then LinearMap.proj (0 : Fin 1) else 0
  | 2 => LinearMap.pi fun r : Fin 2 ↦ if r = 1 then LinearMap.proj (0 : Fin 1) else 0
  | 3 => LinearMap.pi fun _ : Fin 2 ↦ LinearMap.proj (0 : Fin 1)

/-- The simple representation at the first leaf. -/
def P : Rep k quiver where
  obj i := ModuleCat.of k (Fin (dP i) → k)
  map _ := 0

/-- The brick `Q₀`. -/
def Q₀ : Rep k quiver where
  obj i := ModuleCat.of k (Fin (dQ i) → k)
  map j := ModuleCat.ofHom (qMap k j)

lemma endo_fin_one (g : (Fin 1 → k) →ₗ[k] (Fin 1 → k)) :
    g = (g (fun _ ↦ 1) 0) • LinearMap.id := by
  refine LinearMap.ext fun v ↦ funext fun r ↦ ?_
  have hv : v = v 0 • (fun _ ↦ (1 : k)) := funext fun s ↦ by fin_cases s; simp
  fin_cases r
  conv_lhs => rw [hv, map_smul]
  simp [mul_comm]

lemma endo_fin_zero (g : (Fin 0 → k) →ₗ[k] (Fin 0 → k)) (c : k) : g = c • LinearMap.id :=
  LinearMap.ext fun _ ↦ Subsingleton.elim _ _

lemma brickP (f : P k ⟶ P k) : ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id := by
  refine ⟨(f.app 1).hom (fun _ ↦ 1) 0, fun i ↦ ?_⟩
  fin_cases i
  · exact endo_fin_zero k _ _
  · exact endo_fin_one k _
  all_goals exact endo_fin_zero k _ _

/-- The unit vector of `k¹`. -/
abbrev e1 : Fin 1 → k := fun _ ↦ 1

lemma qMap_one (t : Fin 1 → k) : qMap k 1 t = ![t 0, 0] := by
  funext r; fin_cases r <;> simp [qMap]

lemma qMap_two (t : Fin 1 → k) : qMap k 2 t = ![0, t 0] := by
  funext r; fin_cases r <;> simp [qMap]

lemma qMap_three (t : Fin 1 → k) : qMap k 3 t = ![t 0, t 0] := by
  funext r; fin_cases r <;> simp [qMap]

lemma brickQ (f : Q₀ k ⟶ Q₀ k) : ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id := by
  let M : (Fin 2 → k) →ₗ[k] (Fin 2 → k) := (f.app 0).hom
  let g2 : (Fin 1 → k) →ₗ[k] (Fin 1 → k) := (f.app 2).hom
  let g3 : (Fin 1 → k) →ₗ[k] (Fin 1 → k) := (f.app 3).hom
  let g4 : (Fin 1 → k) →ₗ[k] (Fin 1 → k) := (f.app 4).hom
  have hg2 := endo_fin_one k g2
  have hg3 := endo_fin_one k g3
  have hg4 := endo_fin_one k g4
  set c2 := g2 (e1 k) 0
  set c3 := g3 (e1 k) 0
  set c4 := g4 (e1 k) 0
  have hc1 : M (qMap k 1 (e1 k)) = qMap k 1 (g2 (e1 k)) :=
    congrArg (fun φ ↦ φ.hom (e1 k)) (f.comm 1)
  have hc2 : M (qMap k 2 (e1 k)) = qMap k 2 (g3 (e1 k)) :=
    congrArg (fun φ ↦ φ.hom (e1 k)) (f.comm 2)
  have hc3 : M (qMap k 3 (e1 k)) = qMap k 3 (g4 (e1 k)) :=
    congrArg (fun φ ↦ φ.hom (e1 k)) (f.comm 3)
  have h1 : M ![1, 0] = ![c2, 0] := by
    have := hc1; rw [hg2] at this; erw [qMap_one, qMap_one] at this
    rw [this]; funext r; fin_cases r <;> simp
  have h2 : M ![0, 1] = ![0, c3] := by
    have := hc2; rw [hg3] at this; erw [qMap_two, qMap_two] at this
    rw [this]; funext r; fin_cases r <;> simp
  have h3 : M ![1, 1] = ![c4, c4] := by
    have := hc3; rw [hg4] at this; erw [qMap_three, qMap_three] at this
    rw [this]; funext r; fin_cases r <;> simp
  have hsum : M ![1, 1] = ![c2, c3] := by
    rw [show (![1, 1] : Fin 2 → k) = ![1, 0] + ![0, 1] by funext r; fin_cases r <;> simp,
      map_add, h1, h2]
    funext r; fin_cases r <;> simp
  have e2 : c2 = c4 := by simpa using congrFun (hsum.symm.trans h3) 0
  have e3 : c3 = c4 := by simpa using congrFun (hsum.symm.trans h3) 1
  have hM : M = c4 • LinearMap.id := by
    refine LinearMap.ext fun v ↦ ?_
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by funext r; fin_cases r <;> simp
    rw [hv, map_add, map_smul, map_smul, h1, h2, e2, e3]
    funext r; fin_cases r <;> simp [mul_comm]
  refine ⟨c4, fun i ↦ ?_⟩
  fin_cases i
  · exact hM
  · exact endo_fin_zero k _ _
  · change g2 = c4 • LinearMap.id
    rw [hg2, e2]
    rfl
  · change g3 = c4 • LinearMap.id
    rw [hg3, e3]
    rfl
  · exact hg4

/-- The first extension tuple: `v ↦ (v, 0)` on the arrow from the first leaf. -/
def z₁ : ∀ α : quiver.A, (P k).obj (quiver.src α) →ₗ[k] (Q₀ k).obj (quiver.tgt α)
  | 0 => LinearMap.pi fun r : Fin 2 ↦ if r = 0 then LinearMap.proj (0 : Fin 1) else 0
  | 1 => 0
  | 2 => 0
  | 3 => 0

/-- The second extension tuple: `v ↦ (0, v)` on the arrow from the first leaf. -/
def z₂ : ∀ α : quiver.A, (P k).obj (quiver.src α) →ₗ[k] (Q₀ k).obj (quiver.tgt α)
  | 0 => LinearMap.pi fun r : Fin 2 ↦ if r = 1 then LinearMap.proj (0 : Fin 1) else 0
  | 1 => 0
  | 2 => 0
  | 3 => 0

/-- The Kronecker pair of `D̃₄`. -/
def kroneckerPair : Covering.KroneckerPair k quiver where
  P := P k
  Q₀ := Q₀ k
  finP _ := inferInstanceAs (FiniteDimensional k (Fin _ → k))
  finQ _ := inferInstanceAs (FiniteDimensional k (Fin _ → k))
  disjoint i := by
    fin_cases i
    · exact Or.inl (inferInstanceAs (Subsingleton (Fin 0 → k)))
    · exact Or.inr (inferInstanceAs (Subsingleton (Fin 0 → k)))
    all_goals exact Or.inl (inferInstanceAs (Subsingleton (Fin 0 → k)))
  brickP := brickP k
  brickQ := brickQ k
  z₁ := z₁ k
  z₂ := z₂ k
  indep c₁ c₂ h := by
    have := congrArg (fun φ : (Fin 1 → k) →ₗ[k] (Fin 2 → k) ↦ φ (e1 k)) (h 0)
    simp only at this
    have h0 := congrFun this 0
    have h1 := congrFun this 1
    change c₁ * (1 : k) + c₂ * (0 : k) = 0 at h0
    change c₁ * (0 : k) + c₂ * (1 : k) = 0 at h1
    simp only [mul_one, mul_zero, add_zero, zero_add] at h0 h1
    exact ⟨h0, h1⟩
  nonzeroP := ⟨1, inferInstanceAs (Nontrivial (Fin 1 → k))⟩
  nonzeroQ := ⟨0, inferInstanceAs (Nontrivial (Fin 2 → k))⟩

/-- The trivial action. -/
instance trivialAction : MulAction PUnit quiver.V where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The trivial covering of `D̃₄`. -/
def coverData : Covering.CoverData (FinQuiver.Hom.id quiver) where
  G := PUnit
  torsionFree g hg := absurd (Subsingleton.elim g 1) hg
  R₀ := quiver.V
  free g _ _ := Subsingleton.elim g 1
  ι := id
  ι_inj := Function.injective_id
  fibre x y h := ⟨1, h.symm⟩
  arrows α β h := by
    change α = β at h
    subst h
    exact ⟨1, rfl, rfl⟩

/-- The covering alternative for the path algebra of `D̃₄`. -/
def pairCoveringData : Covering.PairCoveringData k (quiver.PathAlgebra k) where
  D := quiver
  Q := quiver
  p := FinQuiver.Hom.id quiver
  locInj := ⟨fun _ _ _ h ↦ h, fun _ _ _ h ↦ h⟩
  C := coverData
  K := kroneckerPair k
  supp i := by
    fin_cases i
    · exact Or.inr (inferInstanceAs (Nontrivial (Fin 2 → k)))
    · exact Or.inl (inferInstanceAs (Nontrivial (Fin 1 → k)))
    all_goals exact Or.inr (inferInstanceAs (Nontrivial (Fin 1 → k)))
  π := AlgHom.id k _
  surj := Function.surjective_id
  kills _ z hz := by
    rw [show z = 0 from hz]
    exact map_zero _

/-- The covering construction for the path algebra of `D̃₄` gives the data of
Theorem 5.2. -/
theorem nonempty_embeddingData : Nonempty (EmbeddingData k (quiver.PathAlgebra k)) :=
  ⟨(pairCoveringData k).toCoveringData.embeddingData⟩

end DTilde4

end LargeIndecomposable
