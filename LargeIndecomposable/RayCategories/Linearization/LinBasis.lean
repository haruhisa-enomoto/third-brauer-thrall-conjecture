module

public import LargeIndecomposable.RayCategories.Linearization.RegularRepresentation
public import LargeIndecomposable.Quivers.PathAlgebras.PathAlgebraLemmas

/-!
# The nonzero morphisms form a basis of the linearization

For a finite ray category `P`, the classes in `k(P)` of the nonzero morphisms
(a vertex idempotent for an identity, the class of any path with the given
value otherwise) form a basis (`RayQuiver.linBasis`; Gabriel–Roiter 13.5).
They span because the span is stable under multiplication by vertices and
arrows, and they are independent because the regular representation sends
them to the standard basis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] (k : Type*) [Field k]

omit [Fintype P] [DecidableEq P] in
/-- An isomorphism of a ray category is an identity. -/
lemma eq_id_of_isIso {x y : P} (f : x ⟶ y) [IsIso f] : ∃ h : x = y, f = eqToHom h := by
  have hxy : x = y := IsRayCategory.skeletal ⟨asIso f⟩
  subst hxy
  refine ⟨rfl, ?_⟩
  have e : 𝟙 x = f ≫ 𝟙 x ≫ inv f := by simp
  exact (IsRayCategory.eq_id_of_two_sided _ (IsRayCategory.id_ne_zero x) f (inv f) e).1

/-- A nonzero non-isomorphism is the value of a nonempty path. -/
lemma exists_path_cons {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (hiso : ¬IsIso f) :
    ∃ (c : (quiver P).A) (l : List (quiver P).A) (h : PathFrom (D := quiver P) x (c :: l) y),
      pathMor (c :: l) x y h = f := by
  obtain ⟨l, h, he⟩ := exists_path f hf hiso
  cases l with
  | nil =>
    change x = y at h
    subst h
    exact absurd (he ▸ (inferInstance : IsIso (eqToHom (rfl : x = x)))) hiso
  | cons c l => exact ⟨c, l, h, he⟩

open Classical in
/-- The element of `k(P)` of a nonzero morphism. -/
def rayElt (μ : NZ P) : Linearization P k :=
  if hiso : IsIso μ.2.2.1 then linPres P k (vertex k (quiver P) μ.1)
  else linPres P k (word k (quiver P)
    ((exists_path_cons μ.2.2.1 μ.2.2.2 hiso).choose ::
      (exists_path_cons μ.2.2.1 μ.2.2.2 hiso).choose_spec.choose))

/-- The class of a nonempty path with nonzero value is the element of the value. -/
lemma linPres_word (c : (quiver P).A) (l : List (quiver P).A) (x y : P)
    (h : PathFrom (D := quiver P) x (c :: l) y) (h0 : pathMor (c :: l) x y h ≠ 0) :
    linPres P k (word k (quiver P) (c :: l)) = rayElt k ⟨x, y, pathMor (c :: l) x y h, h0⟩ := by
  have hiso : ¬IsIso (pathMor (c :: l) x y h) := by
    intro hI
    obtain ⟨hxy, he⟩ := eq_id_of_isIso (pathMor (c :: l) x y h)
    subst hxy
    exact pathMor_ne_id c l x h (he.trans (eqToHom_refl _ _))
  rw [rayElt, dif_neg hiso]
  have hs := exists_path_cons (pathMor (c :: l) x y h) h0 hiso
  obtain ⟨h', he'⟩ := (exists_path_cons (pathMor (c :: l) x y h) h0 hiso).choose_spec.choose_spec
  exact RingQuot.mkAlgHom_rel k (LinRel.eq _ _ x y h h' he'.symm)

/-- The class of a nonempty path is zero or the element of its value. -/
lemma linPres_word_mem (c : (quiver P).A) (l : List (quiver P).A) (x y : P)
    (h : PathFrom (D := quiver P) x (c :: l) y) :
    linPres P k (word k (quiver P) (c :: l)) ∈ Submodule.span k (Set.range (rayElt (P := P) k)) := by
  by_cases h0 : pathMor (c :: l) x y h = 0
  · rw [show linPres P k (word k (quiver P) (c :: l)) = 0 by
      rw [← map_zero (linPres P k)]
      exact RingQuot.mkAlgHom_rel k (LinRel.zero _ x y h h0)]
    exact Submodule.zero_mem _
  · rw [linPres_word k c l x y h h0]
    exact Submodule.subset_span ⟨_, rfl⟩

lemma rayElt_id (x : P) :
    rayElt k ⟨x, x, 𝟙 x, IsRayCategory.id_ne_zero x⟩ = linPres P k (vertex k (quiver P) x) := by
  rw [rayElt, dif_pos (inferInstance : IsIso (𝟙 x))]

/-- The span of the elements of nonzero morphisms. -/
abbrev raySpan : Submodule k (Linearization P k) := Submodule.span k (Set.range (rayElt (P := P) k))

lemma vertex_mem (x : P) : linPres P k (vertex k (quiver P) x) ∈ raySpan (P := P) k := by
  rw [← rayElt_id]
  exact Submodule.subset_span ⟨_, rfl⟩

lemma arrow_mem (a : (quiver P).A) : linPres P k (arrow k (quiver P) a) ∈ raySpan (P := P) k := by
  have : arrow k (quiver P) a = word k (quiver P) [a] := by simp [word]
  rw [this]
  exact linPres_word_mem k a [] a.1 a.2.1 ⟨rfl, rfl⟩

/-- The span is stable under left multiplication by vertices and arrows. -/
lemma gen_mul_rayElt (g : (quiver P).V ⊕ (quiver P).A) (μ : NZ P) :
    linPres P k (RingQuot.mkAlgHom k (PathRel k (quiver P)) (FreeAlgebra.ι k g)) * rayElt k μ ∈
      raySpan (P := P) k := by
  by_cases hiso : IsIso μ.2.2.1
  · rw [rayElt, dif_pos hiso, ← map_mul]
    rcases g with v | a
    · change linPres P k (vertex k (quiver P) v * vertex k (quiver P) μ.1) ∈ _
      rw [vertex_mul_vertex]
      split_ifs
      · exact vertex_mem k v
      · rw [map_zero]; exact Submodule.zero_mem _
    · change linPres P k (arrow k (quiver P) a * vertex k (quiver P) μ.1) ∈ _
      rw [arrow_mul_vertex]
      split_ifs
      · exact arrow_mem k a
      · rw [map_zero]; exact Submodule.zero_mem _
  · rw [rayElt, dif_neg hiso, ← map_mul]
    obtain ⟨h, -⟩ := (exists_path_cons μ.2.2.1 μ.2.2.2 hiso).choose_spec.choose_spec
    set c := (exists_path_cons μ.2.2.1 μ.2.2.2 hiso).choose
    set l := (exists_path_cons μ.2.2.1 μ.2.2.2 hiso).choose_spec.choose
    rw [← vertex_mul_word k c l _ _ h, ← mul_assoc]
    rcases g with v | a
    · change linPres P k (vertex k (quiver P) v * vertex k (quiver P) μ.2.1 * _) ∈ _
      rw [vertex_mul_vertex]
      split_ifs with hv
      · subst hv
        rw [vertex_mul_word k c l _ _ h]
        exact linPres_word_mem k c l _ _ h
      · rw [zero_mul, map_zero]; exact Submodule.zero_mem _
    · change linPres P k (arrow k (quiver P) a * vertex k (quiver P) μ.2.1 * _) ∈ _
      rw [arrow_mul_vertex]
      split_ifs with ha
      · rw [← word_append_arrow, List.cons_append]
        exact linPres_word_mem k c (l ++ [a]) μ.1 a.2.1
          (pathFrom_append (c :: l) [a] μ.1 μ.2.1 a.2.1 h ⟨ha.symm, rfl⟩)
      · rw [zero_mul, map_zero]; exact Submodule.zero_mem _

lemma mul_mem_raySpan (z : (quiver P).PathAlgebra k) :
    ∀ t ∈ raySpan (P := P) k, linPres P k z * t ∈ raySpan (P := P) k := by
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective k (PathRel k (quiver P)) z
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    intro t ht
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ r ht
  | grade1 g =>
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨μ, rfl⟩ := ht
      exact gen_mul_rayElt k g μ
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add t t' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul r t _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h1
  | mul a b ha hb =>
    intro t ht
    rw [map_mul, map_mul, mul_assoc]
    exact ha _ (hb t ht)
  | add a b ha hb =>
    intro t ht
    rw [map_add, map_add, add_mul]
    exact Submodule.add_mem _ (ha t ht) (hb t ht)

lemma raySpan_eq_top : raySpan (P := P) k = ⊤ := by
  refine eq_top_iff.2 fun w _ ↦ ?_
  obtain ⟨z, rfl⟩ := linPres_surjective P k w
  have h1 : (1 : Linearization P k) ∈ raySpan (P := P) k := by
    have : (1 : Linearization P k) = ∑ x : P, linPres P k (vertex k (quiver P) x) := by
      rw [← map_sum, ← map_one (linPres P k)]
      congr 1
      have := RingQuot.mkAlgHom_rel k (PathRel.one (k := k) (Q := quiver P))
      rw [map_sum] at this
      exact (this.trans (map_one _)).symm
    rw [this]
    exact Submodule.sum_mem _ fun x _ ↦ vertex_mem k x
  simpa using mul_mem_raySpan k z 1 h1

variable (P) in
/-- The sum of the identities in `k^(P*)`. -/
def unitVec : NZ P →₀ k := ∑ x : P, Finsupp.single ⟨x, x, 𝟙 x, IsRayCategory.id_ne_zero x⟩ 1

lemma morAct_unitVec {x y : P} (f : x ⟶ y) (hf : f ≠ 0) :
    morAct k f (unitVec P k) = Finsupp.single ⟨x, y, f, hf⟩ 1 := by
  rw [unitVec, map_sum, Finset.sum_eq_single x]
  · rw [morAct_single, actRay_mk_eq]
    unfold compRay
    rw [dif_neg (by rwa [Category.id_comp])]
    congr 1
    simp
  · intro x' _ hx'
    rw [morAct_single]
    exact actRay_mk_ne k _ _ f hx'
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The regular representation sends the element of `μ` to the basis vector `μ`. -/
lemma linRep_rayElt (μ : NZ P) : linRep P k (rayElt k μ) (unitVec P k) = Finsupp.single μ 1 := by
  obtain ⟨x, y, f, hf⟩ := μ
  by_cases hiso : IsIso f
  · obtain ⟨hxy, rfl⟩ := eq_id_of_isIso f
    subst hxy
    rw [rayElt, dif_pos hiso, linRep_linPres, regRep_vertex]
    exact morAct_unitVec k _ _
  · rw [rayElt, dif_neg hiso, linRep_linPres]
    obtain ⟨h, he⟩ := (exists_path_cons f hf hiso).choose_spec.choose_spec
    rw [regRep_word k _ _ x y h]
    simp only [he]
    exact morAct_unitVec k f hf

lemma linearIndependent_rayElt : LinearIndependent k (rayElt (P := P) k) := by
  let Φ : Linearization P k →ₗ[k] (NZ P →₀ k) :=
    LinearMap.applyₗ (unitVec P k) ∘ₗ (linRep P k).toLinearMap
  refine LinearIndependent.of_comp Φ ?_
  have : Φ ∘ rayElt k = fun μ ↦ Finsupp.single μ (1 : k) := funext fun μ ↦ linRep_rayElt k μ
  rw [this]
  exact Finsupp.linearIndependent_single_one k (NZ P)

/-- The nonzero morphisms form a basis of `k(P)` (Gabriel–Roiter 13.5). -/
def linBasis : Module.Basis (NZ P) k (Linearization P k) :=
  Module.Basis.mk (linearIndependent_rayElt k) (raySpan_eq_top k).ge

lemma linBasis_apply (μ : NZ P) : linBasis k μ = rayElt (P := P) k μ := Module.Basis.mk_apply _ _ _

end RayQuiver

end LargeIndecomposable
