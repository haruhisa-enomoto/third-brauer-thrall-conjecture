module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerGlue
public import LargeIndecomposable.RayCategories.Basic.ArrSetIdeal

/-!
# The simple representation at a point of a piece

The simple representation `S(x)` (`pointRep`) is a brick (`brick_pointRep`). On a piece of the
universal cover it respects the relations (`respectsCover_pointRep`): nonempty paths act by zero,
and the composite of a nonempty path is never invertible (`not_isIso_compD`). It serves as one
member of the Kronecker pair `(S(x), V)` of Bongartz's Lemma 4.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Covering

universe u

variable {k : Type u} [Field k] {D : FinQuiver}

namespace Rep

/-- The simple representation at `x`. -/
def pointRep (x : D.V) : Rep k D where
  obj i := ModuleCat.of k (Fin (@ite ℕ (i = x) (D.decV i x) 1 0) → k)
  map _ := 0

lemma pointRep_map (x : D.V) (α : D.A) : ((pointRep (k := k) x).map α).hom = 0 := rfl

lemma endo_fin_le_one {n : ℕ} (hn : n ≤ 1) (g : (Fin n → k) →ₗ[k] (Fin n → k)) :
    ∃ c : k, g = c • LinearMap.id := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · exact ⟨0, LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
  · refine ⟨g (fun _ ↦ 1) 0, LinearMap.ext fun v ↦ funext fun r ↦ ?_⟩
    have hv : v = v 0 • (fun _ ↦ (1 : k)) := funext fun s ↦ by fin_cases s; simp
    fin_cases r
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]

lemma subsingleton_pointRep {x i : D.V} (h : i ≠ x) : Subsingleton ((pointRep (k := k) x).obj i) := by
  change Subsingleton (Fin (@ite ℕ (i = x) (D.decV i x) 1 0) → k)
  rw [if_neg h]
  infer_instance

/-- **The simple representation is a brick.** -/
lemma brick_pointRep (x : D.V) (f : pointRep (k := k) x ⟶ pointRep x) :
    ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := endo_fin_le_one (n := @ite ℕ (x = x) (D.decV x x) 1 0) (by split_ifs <;> omega)
    (f.app x).hom
  refine ⟨c, fun i ↦ ?_⟩
  by_cases h : i = x
  · subst h
    exact hc
  · haveI := subsingleton_pointRep (k := k) h
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _

lemma nontrivial_pointRep (x : D.V) : Nontrivial ((pointRep (k := k) x).obj x) := by
  change Nontrivial (Fin (@ite ℕ (x = x) (D.decV x x) 1 0) → k)
  rw [if_pos rfl]
  infer_instance

lemma pathTot_pointRep (x : D.V) : ∀ (le : List D.A), le ≠ [] → (pointRep (k := k) x).pathTot le = 0
  | [], h => absurd rfl h
  | e :: le, _ => by
    change (pointRep x).pathTot le ∘ₗ (pointRep x).arrOp e = 0
    have : (pointRep (k := k) x).arrOp e = 0 := by
      refine LinearMap.ext fun v ↦ ?_
      rw [arrOp_apply, pointRep_map]
      simp
    rw [this, LinearMap.comp_zero]

end Rep

namespace Covering

/-- **A Kronecker pair at a source**: the simple `S(x)` and a brick `V` vanishing at `x`, with two
independent extension tuples. -/
def pairAtSource (x : D.V) (V : Rep k D) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x)) (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i))
    (z₁ z₂ : ∀ α : D.A, (Rep.pointRep (k := k) x).obj (D.src α) →ₗ[k] V.obj (D.tgt α))
    (indep : ∀ c₁ c₂ : k, (∀ α, c₁ • z₁ α + c₂ • z₂ α = 0) → c₁ = 0 ∧ c₂ = 0) :
    KroneckerPair k D where
  P := Rep.pointRep x
  Q₀ := V
  finP i := by change FiniteDimensional k (Fin _ → k); infer_instance
  finQ := finV
  disjoint i := by
    by_cases h : i = x
    · subst h; exact Or.inr hVx
    · exact Or.inl (Rep.subsingleton_pointRep h)
  brickP := Rep.brick_pointRep x
  brickQ := brickV
  z₁ := z₁
  z₂ := z₂
  indep := indep
  nonzeroP := ⟨x, Rep.nontrivial_pointRep x⟩
  nonzeroQ := hV

/-- **A Kronecker pair at a sink**: a brick `V` vanishing at `x` and the simple `S(x)`. -/
def pairAtSink (x : D.V) (V : Rep k D) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x)) (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i))
    (z₁ z₂ : ∀ α : D.A, V.obj (D.src α) →ₗ[k] (Rep.pointRep (k := k) x).obj (D.tgt α))
    (indep : ∀ c₁ c₂ : k, (∀ α, c₁ • z₁ α + c₂ • z₂ α = 0) → c₁ = 0 ∧ c₂ = 0) :
    KroneckerPair k D where
  P := V
  Q₀ := Rep.pointRep x
  finP := finV
  finQ i := by change FiniteDimensional k (Fin _ → k); infer_instance
  disjoint i := by
    by_cases h : i = x
    · subst h; exact Or.inl hVx
    · exact Or.inr (Rep.subsingleton_pointRep h)
  brickP := brickV
  brickQ := Rep.brick_pointRep x
  z₁ := z₁
  z₂ := z₂
  indep := indep
  nonzeroP := hV
  nonzeroQ := ⟨x, Rep.nontrivial_pointRep x⟩

lemma sincere_of_point (x : D.V) (V : Rep k D) (hV : ∀ i, i ≠ x → Nontrivial (V.obj i)) (i : D.V) :
    Nontrivial ((Rep.pointRep (k := k) x).obj i) ∨ Nontrivial (V.obj i) := by
  by_cases h : i = x
  · subst h; exact Or.inl (Rep.nontrivial_pointRep i)
  · exact Or.inr (hV i h)

end Covering

namespace RayCat

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- The composite of a nonempty path of a piece is not invertible. -/
lemma not_isIso_compD : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : FinQuiver.PathFrom i le j), le ≠ [] → ¬IsIso (compD S le i j h)
  | [], _, _, _, hne => absurd rfl hne
  | e :: le, i, j, h, _ => fun hiso ↦ by
    change IsIso (eqToHom (congrArg (pt S) h.1.symm) ≫ e.2.2.1 ≫ compD S le _ j h.2) at hiso
    have h1 := (isIso_of_comp_isIso _ _ hiso).2
    exact e.2.2.2.2.1 (isIso_of_comp_isIso _ _ h1).1

lemma compD_nil_ne_zero (i j : (pieceQuiver S).V) (h : FinQuiver.PathFrom i [] j) :
    compD S [] i j h ≠ 0 := by
  change eqToHom (congrArg (pt S) h) ≠ 0
  change i = j at h
  subst h
  exact IsRayCategory.id_ne_zero _

/-- **The simple representation respects the relations of the cover.** -/
theorem respectsCover_pointRep (x : (pieceQuiver S).V) :
    RespectsCover (Rep.pointRep (k := k) x) := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rcases le with _ | ⟨e, le⟩
    · exact absurd h0 (compD_nil_ne_zero i j h)
    · exact Rep.pathTot_pointRep x _ (List.cons_ne_nil _ _)
  · rcases le with _ | ⟨e, le⟩ <;> rcases le' with _ | ⟨e', le'⟩
    · rfl
    · exfalso
      change i = j at h
      subst h
      apply not_isIso_compD _ i i h' (List.cons_ne_nil _ _)
      rw [← he]
      change IsIso (eqToHom _)
      infer_instance
    · exfalso
      change i = j at h'
      subst h'
      apply not_isIso_compD _ i i h (List.cons_ne_nil _ _)
      rw [he]
      change IsIso (eqToHom _)
      infer_instance
    · rw [Rep.pathTot_pointRep x _ (List.cons_ne_nil _ _),
        Rep.pathTot_pointRep x _ (List.cons_ne_nil _ _)]

end RayCat

end LargeIndecomposable
