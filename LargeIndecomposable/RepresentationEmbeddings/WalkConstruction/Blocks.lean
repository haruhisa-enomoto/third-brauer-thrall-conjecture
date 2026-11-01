module

public import LargeIndecomposable.Quivers.PushDown.PushDownModule

/-!
# Block equations of maps between push-downs

Proof of Proposition 4.7, first paragraph. For a quiver morphism `p : D → Q`
and representations `X, Y` of `D`, a linear map `f : ⊕ X(i) → ⊕ Y(i)` commutes
with the push-down actions (`IsPdHom`) if and only if its blocks
`bl f j i = e_j f e_i` satisfy the equations (`BlockEqs`): blocks between
different fibres vanish, and for each arrow `c` of `Q`,
`∑_β f_{j,t(β)} X(β) = ∑_α Y(α) f_{s(α),i}` over the arrows `β` labelled `c`
leaving `i` and `α` labelled `c` entering `j`.

When `p` is injective on arrows with a fixed source and on those with a fixed
target, each equation involves only blocks at the two ends of one edge of the
matching quiver. Hence retaining the blocks on a set of positions closed under
these edges (`Saturated`) preserves the equations (`blockEqs_restr`), and the
diagonal blocks of a map satisfying the equations form a morphism of
representations (`diagHom`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D Q : FinQuiver} (p : FinQuiver.Hom D Q)

namespace Rep

variable {X Y Z : Rep k D}

/-- The block `e_j f e_i` of a map of total spaces, as a map of total spaces. -/
def bl (f : X.Tot →ₗ[k] Y.Tot) (j i : D.V) : X.Tot →ₗ[k] Y.Tot := Y.idm j ∘ₗ f ∘ₗ X.idm i

lemma bl_apply_single (f : X.Tot →ₗ[k] Y.Tot) (j i : D.V) (v : X.obj i) :
    bl f j i (Pi.single i v) = Pi.single j (blk f j i v) := by
  simp [bl, idm_apply, blk]

lemma arrOp_eq_idm_comp (e : D.A) : X.arrOp e = X.idm (D.tgt e) ∘ₗ X.arrOp e := by
  rw [idm_comp_arrOp, ite_eq_left rfl]

lemma arrOp_eq_comp_idm (e : D.A) : X.arrOp e = X.arrOp e ∘ₗ X.idm (D.src e) := by
  rw [arrOp_comp_idm, ite_eq_left rfl]

lemma pdVert_comp_idm (q : Q.V) (i : D.V) :
    X.pdVert p q ∘ₗ X.idm i = if p.vert i = q then X.idm i else 0 := by
  by_cases h : p.vert i = q
  · simp only [h, ite_true]
    refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
    simp only [LinearMap.comp_apply, pdVert_apply, idm_apply]
    by_cases hl : l = i <;> simp [hl, h]
  · simp only [h, ite_false]
    refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
    simp only [LinearMap.comp_apply, pdVert_apply, idm_apply,
      LinearMap.zero_apply, Pi.zero_apply]
    by_cases hl : l = i <;> simp [hl, h]

lemma idm_comp_pdVert (j : D.V) (q : Q.V) :
    X.idm j ∘ₗ X.pdVert p q = if p.vert j = q then X.idm j else 0 := by
  by_cases h : p.vert j = q
  · simp only [h, ite_true]
    refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
    simp only [LinearMap.comp_apply, pdVert_apply, idm_apply]
    by_cases hl : l = j <;> simp [hl, h]
  · simp only [h, ite_false]
    refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
    simp only [LinearMap.comp_apply, pdVert_apply, idm_apply,
      LinearMap.zero_apply, Pi.zero_apply]
    by_cases hl : l = j <;> simp [hl, h]

/-- The arrows labelled `c` leaving `i`. -/
abbrev outArr (c : Q.A) (i : D.V) : Finset D.A :=
  Finset.univ.filter fun β ↦ p.arr β = c ∧ D.src β = i

/-- The arrows labelled `c` entering `j`. -/
abbrev inArr (c : Q.A) (j : D.V) : Finset D.A :=
  Finset.univ.filter fun α ↦ p.arr α = c ∧ D.tgt α = j

lemma pdArr_comp_idm (c : Q.A) (i : D.V) :
    X.pdArr p c ∘ₗ X.idm i = ∑ β ∈ outArr p c i, X.arrOp β := by
  rw [pdArr, finsetSum_comp, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [arrOp_comp_idm]
  by_cases h1 : p.arr β = c <;> by_cases h2 : D.src β = i <;> simp [h1, h2]

lemma idm_comp_pdArr (j : D.V) (c : Q.A) :
    X.idm j ∘ₗ X.pdArr p c = ∑ α ∈ inArr p c j, X.arrOp α := by
  rw [pdArr, comp_finsetSum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [idm_comp_arrOp]
  by_cases h1 : p.arr α = c <;> by_cases h2 : D.tgt α = j
  · simp [h1, h2]
  · simp [h1, h2, Ne.symm h2]
  · simp [h1]
  · simp [h1]

lemma idm_comp_comp_pdArr_comp_idm (f : X.Tot →ₗ[k] Y.Tot) (c : Q.A) (j i : D.V) :
    Y.idm j ∘ₗ (f ∘ₗ X.pdArr p c) ∘ₗ X.idm i = ∑ β ∈ outArr p c i, bl f j (D.tgt β) ∘ₗ X.arrOp β := by
  rw [LinearMap.comp_assoc, pdArr_comp_idm, comp_finsetSum, comp_finsetSum]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [arrOp_eq_idm_comp β]
  simp only [bl, LinearMap.comp_assoc]
  rw [← arrOp_eq_idm_comp β, ← arrOp_eq_idm_comp β]

lemma idm_comp_pdArr_comp_comp_idm (f : X.Tot →ₗ[k] Y.Tot) (c : Q.A) (j i : D.V) :
    Y.idm j ∘ₗ (Y.pdArr p c ∘ₗ f) ∘ₗ X.idm i = ∑ α ∈ inArr p c j, Y.arrOp α ∘ₗ bl f (D.src α) i := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, idm_comp_pdArr, finsetSum_comp,
    finsetSum_comp]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  simp only [bl, ← LinearMap.comp_assoc, ← arrOp_eq_comp_idm]

/-- `f` commutes with the push-down actions of the vertices and arrows of `Q`. -/
def IsPdHom (f : X.Tot →ₗ[k] Y.Tot) : Prop :=
  (∀ q, f ∘ₗ X.pdVert p q = Y.pdVert p q ∘ₗ f) ∧ ∀ c, f ∘ₗ X.pdArr p c = Y.pdArr p c ∘ₗ f

/-- The block form of `IsPdHom`. -/
def BlockEqs (f : X.Tot →ₗ[k] Y.Tot) : Prop :=
  (∀ j i, p.vert j ≠ p.vert i → bl f j i = 0) ∧
    ∀ c j i, ∑ β ∈ outArr p c i, bl f j (D.tgt β) ∘ₗ X.arrOp β =
      ∑ α ∈ inArr p c j, Y.arrOp α ∘ₗ bl f (D.src α) i

theorem isPdHom_iff (f : X.Tot →ₗ[k] Y.Tot) : IsPdHom p f ↔ BlockEqs p f := by
  constructor
  · rintro ⟨hv, ha⟩
    refine ⟨fun j i hji ↦ ?_, fun c j i ↦ ?_⟩
    · have e1 : X.idm i = X.pdVert p (p.vert i) ∘ₗ X.idm i := by rw [pdVert_comp_idm, ite_eq_left rfl]
      have e2 : Y.idm j ∘ₗ Y.pdVert p (p.vert i) = 0 := by rw [idm_comp_pdVert, ite_eq_right hji]
      calc bl f j i = Y.idm j ∘ₗ (f ∘ₗ X.pdVert p (p.vert i)) ∘ₗ X.idm i := by
            conv_lhs => rw [bl, e1]
            rfl
        _ = (Y.idm j ∘ₗ Y.pdVert p (p.vert i)) ∘ₗ f ∘ₗ X.idm i := by rw [hv]; rfl
        _ = 0 := by rw [e2, LinearMap.zero_comp]
    · rw [← idm_comp_comp_pdArr_comp_idm, ← idm_comp_pdArr_comp_comp_idm, ha]
  · rintro ⟨hv, ha⟩
    refine ⟨fun q ↦ ext_blocks fun j i ↦ ?_, fun c ↦ ext_blocks fun j i ↦ ?_⟩
    · have L : Y.idm j ∘ₗ (f ∘ₗ X.pdVert p q) ∘ₗ X.idm i =
          Y.idm j ∘ₗ f ∘ₗ (X.pdVert p q ∘ₗ X.idm i) := rfl
      have R : Y.idm j ∘ₗ (Y.pdVert p q ∘ₗ f) ∘ₗ X.idm i =
          (Y.idm j ∘ₗ Y.pdVert p q) ∘ₗ f ∘ₗ X.idm i := rfl
      rw [L, R, pdVert_comp_idm, idm_comp_pdVert]
      by_cases hi : p.vert i = q <;> by_cases hj : p.vert j = q
      · simp [hi, hj]
      · simp only [hi, hj, ite_true, ite_false, LinearMap.zero_comp]
        exact hv j i (fun h ↦ hj (h.trans hi))
      · simp only [hi, hj, ite_true, ite_false, LinearMap.comp_zero]
        exact (hv j i (fun h ↦ hi (h.symm.trans hj))).symm
      · simp [hi, hj]
    · rw [idm_comp_comp_pdArr_comp_idm, idm_comp_pdArr_comp_comp_idm, ha]

lemma IsPdHom.comp {f : X.Tot →ₗ[k] Y.Tot} {g : Y.Tot →ₗ[k] Z.Tot} (hf : IsPdHom p f)
    (hg : IsPdHom p g) : IsPdHom p (g ∘ₗ f) := by
  refine ⟨fun q ↦ ?_, fun c ↦ ?_⟩
  · rw [LinearMap.comp_assoc, hf.1, ← LinearMap.comp_assoc, hg.1]; rfl
  · rw [LinearMap.comp_assoc, hf.2, ← LinearMap.comp_assoc, hg.2]; rfl

lemma IsPdHom.add {f g : X.Tot →ₗ[k] Y.Tot} (hf : IsPdHom p f) (hg : IsPdHom p g) :
    IsPdHom p (f + g) := by
  refine ⟨fun q ↦ ?_, fun c ↦ ?_⟩
  · rw [LinearMap.add_comp, LinearMap.comp_add, hf.1, hg.1]
  · rw [LinearMap.add_comp, LinearMap.comp_add, hf.2, hg.2]

lemma isPdHom_id : IsPdHom p (LinearMap.id : X.Tot →ₗ[k] X.Tot) :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma BlockEqs.comp {f : X.Tot →ₗ[k] Y.Tot} {g : Y.Tot →ₗ[k] Z.Tot} (hf : BlockEqs p f)
    (hg : BlockEqs p g) : BlockEqs p (g ∘ₗ f) :=
  (isPdHom_iff p _).1 (((isPdHom_iff p f).2 hf).comp p ((isPdHom_iff p g).2 hg))

/-! ### Restriction to a set of positions -/

section Restr

open Classical

/-- The map retaining the blocks at the positions in `S`. -/
def restr (S : Set (D.V × D.V)) (f : X.Tot →ₗ[k] Y.Tot) : X.Tot →ₗ[k] Y.Tot :=
  ∑ a ∈ Finset.univ.filter (· ∈ S), bl f a.1 a.2

lemma bl_bl (f : X.Tot →ₗ[k] Y.Tot) (j i j' i' : D.V) :
    bl (bl f j' i') j i = if j = j' ∧ i' = i then bl f j i else 0 := by
  simp only [bl]
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, idm_comp_idm, LinearMap.comp_assoc,
    LinearMap.comp_assoc, idm_comp_idm]
  by_cases h1 : j = j' <;> by_cases h2 : i' = i
  · subst h1; subst h2; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma bl_add (f g : X.Tot →ₗ[k] Y.Tot) (j i : D.V) : bl (f + g) j i = bl f j i + bl g j i := by
  simp [bl, LinearMap.add_comp, LinearMap.comp_add]

lemma bl_sum {ι : Type*} (s : Finset ι) (f : ι → X.Tot →ₗ[k] Y.Tot) (j i : D.V) :
    bl (∑ x ∈ s, f x) j i = ∑ x ∈ s, bl (f x) j i := by
  simp only [bl, finsetSum_comp, comp_finsetSum]

lemma bl_zero (j i : D.V) : bl (0 : X.Tot →ₗ[k] Y.Tot) j i = 0 := by simp [bl]

lemma bl_restr (S : Set (D.V × D.V)) (f : X.Tot →ₗ[k] Y.Tot) (j i : D.V) :
    bl (restr S f) j i = if (j, i) ∈ S then bl f j i else 0 := by
  classical
  rw [restr, bl_sum]
  simp only [bl_bl]
  by_cases h : (j, i) ∈ S
  · rw [ite_eq_left h, Finset.sum_eq_single (j, i)]
    · simp
    · rintro ⟨j', i'⟩ _ hne
      rw [ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    · intro h'; simp [h] at h'
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun a ha ↦ ?_
    rw [ite_eq_right]
    rintro ⟨rfl, rfl⟩
    simp only [Finset.mem_filter] at ha
    exact h ha.2

/-- A set of positions closed under the edges of the matching quiver. -/
def Saturated (S : Set (D.V × D.V)) : Prop :=
  ∀ α β, p.arr α = p.arr β → ((D.src α, D.src β) ∈ S ↔ (D.tgt α, D.tgt β) ∈ S)

lemma sum_ite_iff {ι M : Type*} [AddCommMonoid M] {s : Finset ι} {P : ι → Prop}
    [DecidablePred P] {P₀ : Prop} [Decidable P₀] (h : ∀ x ∈ s, P x ↔ P₀) (t : ι → M) :
    ∑ x ∈ s, (if P x then t x else 0) = if P₀ then ∑ x ∈ s, t x else 0 := by
  split_ifs with h₀
  · exact Finset.sum_congr rfl fun x hx ↦ ite_eq_left ((h x hx).2 h₀)
  · exact Finset.sum_eq_zero fun x hx ↦ ite_eq_right fun h' ↦ h₀ ((h x hx).1 h')

variable {p}

/-- Restricting to a saturated set preserves the block equations. -/
theorem blockEqs_restr (hloc : p.LocallyInjective) {S : Set (D.V × D.V)} (hS : Saturated p S)
    {f : X.Tot →ₗ[k] Y.Tot} (hf : BlockEqs p f) : BlockEqs p (restr S f) := by
  classical
  refine ⟨fun j i hji ↦ by rw [bl_restr, hf.1 j i hji, ite_self], fun c j i ↦ ?_⟩
  have hL : ∀ β ∈ outArr p c i, bl (restr S f) j (D.tgt β) ∘ₗ X.arrOp β =
      if (j, D.tgt β) ∈ S then bl f j (D.tgt β) ∘ₗ X.arrOp β else 0 := by
    intro β _; rw [bl_restr]; split_ifs <;> simp
  have hR : ∀ α ∈ inArr p c j, Y.arrOp α ∘ₗ bl (restr S f) (D.src α) i =
      if (D.src α, i) ∈ S then Y.arrOp α ∘ₗ bl f (D.src α) i else 0 := by
    intro α _; rw [bl_restr]; split_ifs <;> simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  have heq := hf.2 c j i
  by_cases hA : ∃ α₀ ∈ inArr p c j, True
  · obtain ⟨α₀, hα₀, -⟩ := hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα₀
    have h1 : ∀ α ∈ inArr p c j, (D.src α, i) ∈ S ↔ (D.src α₀, i) ∈ S := by
      intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
      rw [hloc.2 α α₀ (hα.2.trans hα₀.2.symm) (hα.1.trans hα₀.1.symm)]
    have h2 : ∀ β ∈ outArr p c i, (j, D.tgt β) ∈ S ↔ (D.src α₀, i) ∈ S := by
      intro β hβ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
      have := hS α₀ β (hα₀.1.trans hβ.1.symm)
      rw [hβ.2, hα₀.2] at this
      exact this.symm
    rw [sum_ite_iff h1, sum_ite_iff h2, heq]
  · push Not at hA
    have h0 : ∑ α ∈ inArr p c j, Y.arrOp α ∘ₗ bl f (D.src α) i = 0 :=
      Finset.sum_eq_zero fun α hα ↦ (hA α hα).elim
    have h0' : ∑ α ∈ inArr p c j, (if (D.src α, i) ∈ S then Y.arrOp α ∘ₗ bl f (D.src α) i
        else 0) = 0 :=
      Finset.sum_eq_zero fun α hα ↦ (hA α hα).elim
    rw [h0']
    by_cases hB : ∃ β₀ ∈ outArr p c i, True
    · obtain ⟨β₀, hβ₀, -⟩ := hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ₀
      have h2 : ∀ β ∈ outArr p c i, (j, D.tgt β) ∈ S ↔ (j, D.tgt β₀) ∈ S := by
        intro β hβ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
        rw [hloc.1 β β₀ (hβ.2.trans hβ₀.2.symm) (hβ.1.trans hβ₀.1.symm)]
      rw [sum_ite_iff h2, heq, h0, ite_self]
    · push Not at hB
      exact Finset.sum_eq_zero fun β hβ ↦ (hB β hβ).elim

omit [Field k] in
lemma Saturated.compl {S : Set (D.V × D.V)} (hS : Saturated p S) : Saturated p Sᶜ :=
  fun α β h ↦ not_congr (hS α β h)

lemma Saturated.inter {S T : Set (D.V × D.V)} (hS : Saturated p S) (hT : Saturated p T) :
    Saturated p (S ∩ T) :=
  fun α β h ↦ and_congr (hS α β h) (hT α β h)

/-- The diagonal is saturated. -/
lemma saturated_diag (hloc : p.LocallyInjective) : Saturated p {a | a.1 = a.2} := by
  intro α β h
  constructor
  · intro hs
    rw [hloc.1 α β hs h]; rfl
  · intro ht
    rw [hloc.2 α β ht h]; rfl

/-! ### Columns -/

lemma comp_idm_eq_sum (g : X.Tot →ₗ[k] Y.Tot) (i : D.V) : g ∘ₗ X.idm i = ∑ j, bl g j i := by
  simp only [bl, ← finsetSum_comp, sum_idm]; rfl

/-- A map retaining at most one position in each column maps each summand into a
single summand. -/
lemma restr_col (S : Set (D.V × D.V)) (hS : ∀ j j' i, (j, i) ∈ S → (j', i) ∈ S → j = j')
    (f : X.Tot →ₗ[k] Y.Tot) (i : D.V) :
    ∃ j, restr S f ∘ₗ X.idm i = Y.idm j ∘ₗ restr S f ∘ₗ X.idm i := by
  classical
  by_cases h : ∃ j, (j, i) ∈ S
  · obtain ⟨j, hj⟩ := h
    refine ⟨j, ?_⟩
    conv_lhs => rw [comp_idm_eq_sum]
    rw [Finset.sum_eq_single j]
    · rfl
    · intro j' _ hj'
      rw [bl_restr, ite_eq_right fun h' ↦ hj' (hS j' j i h' hj)]
    · simp
  · push Not at h
    have : restr S f ∘ₗ X.idm i = 0 := by
      rw [comp_idm_eq_sum]
      exact Finset.sum_eq_zero fun j _ ↦ by rw [bl_restr, ite_eq_right (h j)]
    exact ⟨i, by rw [this, LinearMap.comp_zero]⟩

lemma restr_comp_idm_eq_zero (S : Set (D.V × D.V)) (f : X.Tot →ₗ[k] Y.Tot) {c : D.V}
    (hc : ∀ j, (j, c) ∉ S) : restr S f ∘ₗ X.idm c = 0 := by
  classical
  rw [comp_idm_eq_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [bl_restr, ite_eq_right (hc j)]

end Restr

variable {p}

/-! ### The diagonal part -/

lemma outArr_eq (hloc : p.LocallyInjective) (e : D.A) : outArr p (p.arr e) (D.src e) = {e} := by
  ext β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h ↦ hloc.1 β e h.2 h.1, fun h ↦ h ▸ ⟨rfl, rfl⟩⟩

lemma inArr_eq (hloc : p.LocallyInjective) (e : D.A) : inArr p (p.arr e) (D.tgt e) = {e} := by
  ext α
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h ↦ hloc.2 α e h.2 h.1, fun h ↦ h ▸ ⟨rfl, rfl⟩⟩

/-- The diagonal blocks of a map satisfying the block equations form a
morphism of representations. -/
def diagHom (hloc : p.LocallyInjective) (f : X.Tot →ₗ[k] Y.Tot) (hf : BlockEqs p f) : X ⟶ Y where
  app i := ModuleCat.ofHom (blk f i i)
  comm e := by
    ext v
    have h := hf.2 (p.arr e) (D.tgt e) (D.src e)
    rw [outArr_eq hloc, inArr_eq hloc, Finset.sum_singleton, Finset.sum_singleton] at h
    have h' := congrArg (fun φ ↦ φ (Pi.single (D.src e) v) (D.tgt e)) h
    simp only [LinearMap.comp_apply, arrOp_apply, bl_apply_single] at h'
    simpa [blk] using h'

lemma diagHom_app (hloc : p.LocallyInjective) (f : X.Tot →ₗ[k] Y.Tot) (hf : BlockEqs p f) (i : D.V) :
    (diagHom hloc f hf).app i = ModuleCat.ofHom (blk f i i) := rfl

lemma bl_eq_zero_of_blk {f : X.Tot →ₗ[k] Y.Tot} {j i : D.V} (h : blk f j i = 0) : bl f j i = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  have : f (Pi.single i (x i)) j = 0 := by
    have := congrArg (fun φ ↦ φ (x i)) h
    simpa [blk] using this
  simp only [bl, LinearMap.comp_apply, idm_apply, LinearMap.zero_apply, this, Pi.single_zero]

lemma blk_bl_self (f : X.Tot →ₗ[k] Y.Tot) (i : D.V) : blk (bl f i i) i i = blk f i i := by
  ext v; simp [blk, bl, idm_apply]

end Rep

end LargeIndecomposable
