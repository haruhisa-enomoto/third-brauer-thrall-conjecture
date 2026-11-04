module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Blocks
public import LargeIndecomposable.KroneckerModules.Basic

/-!
# Control of push-down constructions on total spaces

Propositions 4.5, 4.7 and 4.8, for maps between the total spaces
`⊕_i L(T)(i)` satisfying the block equations of a push-down along a quiver
morphism `p : D → Q` injective on the arrows with a fixed source and on those
with a fixed target. Here `L : D → Rep D` is fully faithful and a morphism
`φ : T → U` with `T ∈ C` whose image `L(φ)` vanishes at one vertex is zero
(`ZeroAtVertex`, Lemmas 2.2(1) and 4.2). The positions `(j, i)` of blocks are
partitioned into classes (`BlockClasses`): components of the matching quiver
for walks, elements of the group for coverings. The classes are closed under
the edges of the matching quiver, the diagonal is a union of classes, and on
each class off the diagonal the second coordinate determines the first and
some column is missing.

* `bl_self_eq_zero`: a map `p_*L(T) → p_*L(U)`, `T ∈ C`, with a zero column
  has zero diagonal blocks.
* `bl_comp_self`: the diagonal part is multiplicative.
* `eq_zero_of_mem_closure_good`: a composite of `|D₀|` maps with zero diagonal
  parts vanishes (the argument of Lemma 4.4).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

variable {k : Type u} [Field k]

namespace Rep

variable {D : FinQuiver} {X Y Z : Rep k D}

/-- The map of total spaces of a morphism of representations. -/
def Hom.tot (φ : X ⟶ Y) : X.Tot →ₗ[k] Y.Tot :=
  LinearMap.pi fun i ↦ (φ.app i).hom ∘ₗ LinearMap.proj i

@[simp]
lemma Hom.tot_apply (φ : X ⟶ Y) (x : X.Tot) (i : D.V) : φ.tot x i = (φ.app i).hom (x i) := rfl

lemma Hom.tot_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) : (φ ≫ ψ).tot = ψ.tot ∘ₗ φ.tot := by
  ext x i; simp [comp_app]

lemma Hom.tot_id : (𝟙 X : X ⟶ X).tot = LinearMap.id := by
  ext x i; simp [id_app]

lemma Hom.blk_tot (φ : X ⟶ Y) (i : D.V) : blk φ.tot i i = (φ.app i).hom := by
  ext v; simp [blk]

lemma Hom.tot_comp_arrOp (φ : X ⟶ Y) (e : D.A) : φ.tot ∘ₗ X.arrOp e = Y.arrOp e ∘ₗ φ.tot := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, tot_apply, arrOp_apply]
  by_cases hl : l = D.tgt e
  · subst hl
    simp only [Pi.single_eq_same]
    have := congrArg (fun f ↦ f.hom (x (D.src e))) (φ.comm e)
    simpa using this
  · simp [Pi.single_eq_of_ne hl]

lemma Hom.isPdHom_tot {Q : FinQuiver} (p : FinQuiver.Hom D Q) (φ : X ⟶ Y) : IsPdHom p φ.tot := by
  refine ⟨fun q ↦ LinearMap.ext fun x ↦ funext fun i ↦ ?_, fun c ↦ ?_⟩
  · simp only [LinearMap.comp_apply, tot_apply, pdVert_apply]
    split_ifs <;> simp
  · simp only [pdArr, comp_finsetSum, finsetSum_comp, tot_comp_arrOp]

/-- A block of a composite. -/
lemma bl_comp (f : X.Tot →ₗ[k] Y.Tot) (g : Y.Tot →ₗ[k] Z.Tot) (j i : D.V) :
    bl (g ∘ₗ f) j i = ∑ l, bl g j l ∘ₗ bl f l i := by
  have e : ∀ l (h : X.Tot →ₗ[k] Y.Tot), Y.idm l ∘ₗ Y.idm l ∘ₗ h = Y.idm l ∘ₗ h :=
    fun l h ↦ by rw [← LinearMap.comp_assoc, idm_idm]
  simp only [bl, LinearMap.comp_assoc, e]
  rw [← comp_finsetSum, ← comp_finsetSum, ← finsetSum_comp, sum_idm]
  rfl

end Rep

namespace PushDown

variable {D Q : FinQuiver} (p : FinQuiver.Hom D Q)

/-- A partition of the positions `(j, i)` of blocks into classes, as needed for
Propositions 4.5 and 4.7. -/
structure BlockClasses where
  /-- The classes. -/
  ι : Type
  [fin : Fintype ι]
  /-- The class of a position. -/
  cls : D.V × D.V → ι
  sat : ∀ α β, p.arr α = p.arr β → cls (D.src α, D.src β) = cls (D.tgt α, D.tgt β)
  diag : ∀ a b, cls a = cls b → a.1 = a.2 → b.1 = b.2
  col : ∀ j j' i, j ≠ i → j' ≠ i → cls (j, i) = cls (j', i) → j = j'
  zeroCol : ∀ κ : ι, ∃ c, ∀ j, cls (j, c) = κ → j = c

attribute [instance] BlockClasses.fin

variable {p} (B : BlockClasses p)

namespace BlockClasses

/-- The off-diagonal positions in a class. -/
def piece (κ : B.ι) : Set (D.V × D.V) := {a | a.1 = a.2}ᶜ ∩ {a | B.cls a = κ}

lemma saturated_piece (hloc : p.LocallyInjective) (κ : B.ι) : Saturated p (B.piece κ) := by
  refine (saturated_diag hloc).compl.inter fun α β h ↦ ?_
  simp only [Set.mem_ofPred_eq, B.sat α β h]

lemma piece_col (κ : B.ι) (j j' i : D.V) (hj : (j, i) ∈ B.piece κ) (hj' : (j', i) ∈ B.piece κ) :
    j = j' :=
  B.col j j' i hj.1 hj'.1 (hj.2.trans hj'.2.symm)

lemma piece_zeroCol (κ : B.ι) : ∃ c, ∀ j, (j, c) ∉ B.piece κ := by
  obtain ⟨c, hc⟩ := B.zeroCol κ
  exact ⟨c, fun j hj ↦ hj.1 (hc j hj.2)⟩

open Classical in
/-- The off-diagonal part of a map is the sum of its pieces. -/
lemma restr_offdiag_eq_sum {X Y : Rep k D} (f : X.Tot →ₗ[k] Y.Tot) :
    restr {a | a.1 = a.2}ᶜ f = ∑ κ, restr (B.piece κ) f := by
  refine ext_blocks fun j i ↦ ?_
  change bl _ j i = bl _ j i
  rw [bl_sum, bl_restr]
  simp only [bl_restr, piece, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
  by_cases h : j = i
  · simp [h]
  · simp only [h, not_false_eq_true, true_and]
    rw [Finset.sum_ite_eq]
    simp

end BlockClasses

/-! ### Chains of maps with zero diagonal part (the argument of Lemma 4.4)

The nilpotence argument only needs a family of representations `Xf o` of `D`,
a notion of admissible column `Adm o c`, the vanishing of the diagonal blocks of
a map with a zero admissible column (`DiagZero`), and an admissible zero column
for each piece of a map (`ColAdm`). -/

namespace Chain

variable {𝒪 : Type*} (Xf : 𝒪 → Rep k D) (Adm : 𝒪 → D.V → Prop)

/-- A map satisfying the block equations with a zero admissible column has
zero diagonal blocks. -/
def DiagZero : Prop :=
  ∀ (o o' : 𝒪) (h : (Xf o).Tot →ₗ[k] (Xf o').Tot), BlockEqs p h → ∀ c, Adm o c →
    h ∘ₗ (Xf o).idm c = 0 → ∀ i, bl h i i = 0

/-- Every piece of a map satisfying the block equations has a zero admissible
column. -/
def ColAdm : Prop :=
  ∀ (o o' : 𝒪) (κ : B.ι), ∃ c, Adm o c ∧ ∀ f : (Xf o).Tot →ₗ[k] (Xf o').Tot, BlockEqs p f →
    restr (B.piece κ) f ∘ₗ (Xf o).idm c = 0

variable {Xf Adm} (hloc : p.LocallyInjective) (hZ : DiagZero (p := p) Xf Adm) (hC : ColAdm B Xf Adm)
include hloc hZ hC

/-- The diagonal part is multiplicative. -/
theorem bl_comp_self {o o' o'' : 𝒪} {f : (Xf o).Tot →ₗ[k] (Xf o').Tot}
    {g : (Xf o').Tot →ₗ[k] (Xf o'').Tot} (hf : BlockEqs p f) (hg : BlockEqs p g) (i : D.V) :
    bl (g ∘ₗ f) i i = bl g i i ∘ₗ bl f i i := by
  classical
  set g' := restr {a | a.1 = a.2}ᶜ g
  set f' := restr {a | a.1 = a.2}ᶜ f
  have hg' : BlockEqs p g' := blockEqs_restr hloc (saturated_diag hloc).compl hg
  have h0 : bl (g' ∘ₗ f') i i = 0 := by
    rw [show f' = ∑ κ, restr (B.piece κ) f from B.restr_offdiag_eq_sum f, comp_finsetSum, bl_sum]
    refine Finset.sum_eq_zero fun κ _ ↦ ?_
    obtain ⟨c, hcA, hc⟩ := hC o o' κ
    refine hZ o o'' _ ((blockEqs_restr hloc (B.saturated_piece hloc κ) hf).comp p hg') c hcA ?_ i
    rw [LinearMap.comp_assoc, hc f hf, LinearMap.comp_zero]
  have hii : (i, i) ∉ ({a | a.1 = a.2}ᶜ : Set (D.V × D.V)) := by simp
  have e1 : bl (g ∘ₗ f) i i = bl g i i ∘ₗ bl f i i +
      ∑ l ∈ Finset.univ.erase i, bl g i l ∘ₗ bl f l i := by
    rw [bl_comp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have e2 : bl (g' ∘ₗ f') i i = ∑ l ∈ Finset.univ.erase i, bl g i l ∘ₗ bl f l i := by
    rw [bl_comp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), bl_restr, ite_eq_right hii,
      LinearMap.zero_comp, zero_add]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' : l ≠ i := Finset.ne_of_mem_erase hl
    rw [bl_restr, bl_restr, ite_eq_left (by simpa using Ne.symm hl'),
      ite_eq_left (by simpa using hl')]
  rw [e1, ← e2, h0, add_zero]

omit hloc hZ hC in
variable (Xf Adm) in
/-- `Good m g`: `g` satisfies the block equations, and on each summand `X(i₀)`
it is zero or follows an injective path `tr` of `m` steps of summand indices,
in the sense that every map with a zero admissible column, composed with `g`,
has zero block at the summands `X(i₀) → ⋯(tr k)`. -/
def Good (m : ℕ) {o o' : 𝒪} (g : (Xf o).Tot →ₗ[k] (Xf o').Tot) : Prop :=
  BlockEqs p g ∧ ∀ i₀, g ∘ₗ (Xf o).idm i₀ = 0 ∨
    ∃ tr : Fin (m + 1) → D.V, Function.Injective tr ∧ tr 0 = i₀ ∧
      g ∘ₗ (Xf o).idm i₀ = (Xf o').idm (tr (Fin.last m)) ∘ₗ g ∘ₗ (Xf o).idm i₀ ∧
      ∀ (k' : Fin (m + 1)) (o'' : 𝒪) (h : (Xf o').Tot →ₗ[k] (Xf o'').Tot), BlockEqs p h →
        (∃ c, Adm o' c ∧ h ∘ₗ (Xf o').idm c = 0) →
          (Xf o'').idm (tr k') ∘ₗ h ∘ₗ g ∘ₗ (Xf o).idm i₀ = 0

omit hloc hC in
/-- The identity is good with `m = 0`. -/
lemma good_id (o : 𝒪) : Good (p := p) Xf Adm 0 (LinearMap.id : (Xf o).Tot →ₗ[k] (Xf o).Tot) := by
  refine ⟨(isPdHom_iff p _).1 (isPdHom_id p), fun i₀ ↦ Or.inr ⟨fun _ ↦ i₀,
    fun a b _ ↦ Fin.ext (by have := a.2; have := b.2; omega), rfl, ?_, ?_⟩⟩
  · simp [idm_idm]
  · intro k' o'' h hh ⟨c, hcA, hc⟩
    exact hZ o o'' h hh c hcA hc i₀

/-- Composing a good map with a piece of a map. -/
lemma good_piece_comp {m : ℕ} {o o' o'' : 𝒪} {g : (Xf o).Tot →ₗ[k] (Xf o').Tot}
    (hg : Good (p := p) Xf Adm m g) {f : (Xf o').Tot →ₗ[k] (Xf o'').Tot} (hf : BlockEqs p f)
    (κ : B.ι) : Good (p := p) Xf Adm (m + 1) (restr (B.piece κ) f ∘ₗ g) := by
  set z := restr (B.piece κ) f
  have hz : BlockEqs p z := blockEqs_restr hloc (B.saturated_piece hloc κ) hf
  obtain ⟨c₀, hc₀A, hc₀⟩ := hC o' o'' κ
  have hzc : z ∘ₗ (Xf o').idm c₀ = 0 := hc₀ f hf
  refine ⟨hg.1.comp p hz, fun i₀ ↦ ?_⟩
  rcases hg.2 i₀ with h0 | ⟨tr, htr, htr0, hend, hprop⟩
  · left; rw [LinearMap.comp_assoc, h0, LinearMap.comp_zero]
  obtain ⟨j, hj⟩ := restr_col (B.piece κ) (B.piece_col κ) f (tr (Fin.last m))
  have hE : (z ∘ₗ g) ∘ₗ (Xf o).idm i₀ = (Xf o'').idm j ∘ₗ (z ∘ₗ g) ∘ₗ (Xf o).idm i₀ := by
    calc (z ∘ₗ g) ∘ₗ (Xf o).idm i₀
        = (z ∘ₗ (Xf o').idm (tr (Fin.last m))) ∘ₗ g ∘ₗ (Xf o).idm i₀ := by
          conv_lhs => rw [LinearMap.comp_assoc, hend]
          rfl
      _ = ((Xf o'').idm j ∘ₗ z ∘ₗ (Xf o').idm (tr (Fin.last m))) ∘ₗ g ∘ₗ (Xf o).idm i₀ := by
          rw [← hj]
      _ = (Xf o'').idm j ∘ₗ (z ∘ₗ g) ∘ₗ (Xf o).idm i₀ := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← hend]; rfl
  by_cases hrep : ∃ k', tr k' = j
  · obtain ⟨k', rfl⟩ := hrep
    left
    rw [hE]
    have := hprop k' o'' z hz ⟨c₀, hc₀A, hzc⟩
    rw [← this]; rfl
  · push Not at hrep
    right
    refine ⟨Fin.snoc tr j, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact absurd hab.symm (hrep b)
      | cast a =>
        induction b using Fin.lastCases with
        | last => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact absurd hab (hrep a)
        | cast b =>
          simp only [Fin.snoc_castSucc] at hab
          rw [htr hab]
    · rw [show (0 : Fin (m + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc, htr0]
    · rw [Fin.snoc_last]; exact hE
    · intro k' o₃ h hh ⟨c, hcA, hc⟩
      induction k' using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        have hb := hZ o'' o₃ h hh c hcA hc j
        calc (Xf o₃).idm j ∘ₗ h ∘ₗ (z ∘ₗ g) ∘ₗ (Xf o).idm i₀
            = (Xf o₃).idm j ∘ₗ h ∘ₗ (Xf o'').idm j ∘ₗ (z ∘ₗ g) ∘ₗ (Xf o).idm i₀ := by rw [← hE]
          _ = bl h j j ∘ₗ (z ∘ₗ g) ∘ₗ (Xf o).idm i₀ := rfl
          _ = 0 := by rw [hb, LinearMap.zero_comp]
      | cast k'' =>
        rw [Fin.snoc_castSucc]
        have := hprop k'' o₃ (h ∘ₗ z) (hz.comp p hh)
          ⟨c₀, hc₀A, by rw [LinearMap.comp_assoc, hzc, LinearMap.comp_zero]⟩
        rw [← this]; rfl

/-- Composing a sum of good maps with a map with zero diagonal blocks. -/
lemma closure_good_comp {m : ℕ} {o o' o'' : 𝒪} {G : (Xf o).Tot →ₗ[k] (Xf o').Tot}
    (hG : G ∈ AddSubmonoid.closure {g | Good (p := p) Xf Adm m g})
    {f : (Xf o').Tot →ₗ[k] (Xf o'').Tot} (hf : BlockEqs p f) (hdiag : ∀ i, bl f i i = 0) :
    f ∘ₗ G ∈ AddSubmonoid.closure {g | Good (p := p) Xf Adm (m + 1) g} := by
  classical
  have hf' : f = ∑ κ, restr (B.piece κ) f := by
    rw [← B.restr_offdiag_eq_sum]
    refine ext_blocks fun j i ↦ ?_
    change bl f j i = bl _ j i
    rw [bl_restr]
    by_cases h : j = i
    · subst h; simp [hdiag]
    · simp [h]
  induction hG using AddSubmonoid.closure_induction with
  | mem g hg =>
    rw [hf', finsetSum_comp]
    exact AddSubmonoid.sum_mem _ fun κ _ ↦
      AddSubmonoid.subset_closure (good_piece_comp B hloc hZ hC hg hf κ)
  | zero => rw [LinearMap.comp_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [LinearMap.comp_add]; exact add_mem ha hb

omit hloc hZ hC in
/-- A sum of maps good with `m` the number of vertices vanishes. -/
lemma eq_zero_of_mem_closure_good {o o' : 𝒪} {G : (Xf o).Tot →ₗ[k] (Xf o').Tot}
    (hG : G ∈ AddSubmonoid.closure {g | Good (p := p) Xf Adm (Fintype.card D.V) g}) : G = 0 := by
  have hgood : ∀ g : (Xf o).Tot →ₗ[k] (Xf o').Tot,
      Good (p := p) Xf Adm (Fintype.card D.V) g → g = 0 := by
    intro g hg
    refine eq_zero_of_comp_idm fun i₀ ↦ ?_
    rcases hg.2 i₀ with h0 | ⟨tr, htr, -⟩
    · exact h0
    · have := Fintype.card_le_of_injective tr htr
      rw [Fintype.card_fin] at this
      omega
  induction hG using AddSubmonoid.closure_induction with
  | mem g hg => exact hgood g hg
  | zero => rfl
  | add a b _ _ ha hb => rw [ha, hb, add_zero]

end Chain

/-- A morphism `φ : T → U` with `T ∈ C` whose image under `L` vanishes at some
vertex is zero. -/
def ZeroAtVertex (L : Statement.D k ⥤ Rep k D) : Prop :=
  ∀ {T U : Statement.D k}, InC T.obj → ∀ (φ : T ⟶ U) (c : D.V), (L.map φ).app c = 0 → φ = 0

variable (hloc : p.LocallyInjective) {L : Statement.D k ⥤ Rep k D} [L.Additive] (hL : L.FullyFaithful)
  (hZ : ZeroAtVertex L)
include hloc hL hZ

/-- For `T ∈ C`, a map `p_*L(T) → p_*L(U)` satisfying the block equations and
vanishing on one summand has zero diagonal blocks. -/
theorem bl_self_eq_zero {T U : Statement.D k} (hT : InC T.obj) {h : (L.obj T).Tot →ₗ[k] (L.obj U).Tot}
    (hh : BlockEqs p h) {c : D.V} (hc : h ∘ₗ (L.obj T).idm c = 0) (i : D.V) : bl h i i = 0 := by
  set ψ := diagHom hloc h hh
  have hcc : blk h c c = 0 := by
    ext v
    have := congrArg (fun g ↦ g (Pi.single c v) c) hc
    simpa [blk, idm_apply] using this
  have hφ : hL.preimage ψ = 0 := hZ hT _ c (by
    rw [hL.map_preimage]
    change ModuleCat.ofHom (blk h c c) = 0
    rw [hcc]; rfl)
  have key : ψ.app i = 0 := by
    rw [← hL.map_preimage ψ, hφ, L.map_zero]; rfl
  refine bl_eq_zero_of_blk ?_
  have := congrArg (fun φ ↦ φ.hom) key
  simpa [ψ, diagHom_app] using this

omit hZ in
/-- The diagonal blocks of a map in the image of `L` are its components. -/
lemma diagHom_eq_preimage {T U : Statement.D k} {h : (L.obj T).Tot →ₗ[k] (L.obj U).Tot}
    (hh : BlockEqs p h) (h0 : hL.preimage (diagHom hloc h hh) = 0) (i : D.V) : bl h i i = 0 := by
  have key : (diagHom hloc h hh).app i = 0 := by
    rw [← hL.map_preimage (diagHom hloc h hh), h0, L.map_zero]; rfl
  refine bl_eq_zero_of_blk ?_
  have := congrArg (fun φ ↦ φ.hom) key
  simpa [diagHom_app] using this

include B in
/-- The diagonal part is multiplicative: for `T ∈ C`, the diagonal block of a
composite `p_*L(T) → p_*L(U) → p_*L(V)` is the composite of the diagonal
blocks. -/
theorem bl_comp_self {T U V : Statement.D k} (hT : InC T.obj) {f : (L.obj T).Tot →ₗ[k] (L.obj U).Tot}
    {g : (L.obj U).Tot →ₗ[k] (L.obj V).Tot} (hf : BlockEqs p f) (hg : BlockEqs p g) (i : D.V) :
    bl (g ∘ₗ f) i i = bl g i i ∘ₗ bl f i i := by
  classical
  set g' := restr {a | a.1 = a.2}ᶜ g
  set f' := restr {a | a.1 = a.2}ᶜ f
  have hg' : BlockEqs p g' := blockEqs_restr hloc (saturated_diag hloc).compl hg
  have h0 : bl (g' ∘ₗ f') i i = 0 := by
    rw [show f' = ∑ κ, restr (B.piece κ) f from B.restr_offdiag_eq_sum f, comp_finsetSum, bl_sum]
    refine Finset.sum_eq_zero fun κ _ ↦ ?_
    obtain ⟨c, hc⟩ := B.piece_zeroCol κ
    refine bl_self_eq_zero hloc hL hZ hT
      ((blockEqs_restr hloc (B.saturated_piece hloc κ) hf).comp p hg') (c := c) ?_ i
    rw [LinearMap.comp_assoc, restr_comp_idm_eq_zero _ _ hc, LinearMap.comp_zero]
  have hii : (i, i) ∉ ({a | a.1 = a.2}ᶜ : Set (D.V × D.V)) := by simp
  have e1 : bl (g ∘ₗ f) i i = bl g i i ∘ₗ bl f i i +
      ∑ l ∈ Finset.univ.erase i, bl g i l ∘ₗ bl f l i := by
    rw [bl_comp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have e2 : bl (g' ∘ₗ f') i i = ∑ l ∈ Finset.univ.erase i, bl g i l ∘ₗ bl f l i := by
    rw [bl_comp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), bl_restr, ite_eq_right hii,
      LinearMap.zero_comp, zero_add]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' : l ≠ i := Finset.ne_of_mem_erase hl
    rw [bl_restr, bl_restr, ite_eq_left (by simpa using Ne.symm hl'),
      ite_eq_left (by simpa using hl')]
  rw [e1, ← e2, h0, add_zero]


/-! ### The chain argument for `L` on `C` -/

/-- The family `T ↦ L(T)` on `C`. -/
abbrev LX (L : Statement.D k ⥤ Rep k D) : {T : Statement.D k // InC T.obj} → Rep k D :=
  fun o ↦ L.obj o.1

lemma diagZero_LX : Chain.DiagZero (p := p) (LX L) (fun _ _ ↦ True) :=
  fun o _ _ hh _ _ hc i ↦ bl_self_eq_zero hloc hL hZ o.2 hh hc i

omit hloc hL hZ [L.Additive] in
lemma colAdm_LX : Chain.ColAdm B (LX L) (fun _ _ ↦ True) := fun _ _ κ ↦
  let ⟨c, hc⟩ := B.piece_zeroCol κ
  ⟨c, trivial, fun _ _ ↦ restr_comp_idm_eq_zero _ _ hc⟩

end PushDown

end LargeIndecomposable
