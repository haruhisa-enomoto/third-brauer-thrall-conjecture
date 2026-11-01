module

public import LargeIndecomposable.Coverings.GradedModules.GradedPieceAct

/-!
# Graded modules and push-downs of piece representations

If the piece representation `grRep S` of a graded `k(P)`-module `M` is isomorphic to a
representation `Y` of a convex piece `S`, then `M` is isomorphic to the push-down
`pdMod S Y` (`exists_bijective_pdMod`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}
variable (k : Type u) [Field k]
variable {ℓ : ∀ y : P, vtx x₀ ⟶ vtx y}
variable {M : Type u} [AddCommGroup M] [Module (Linearization P k) M] [Module k M]
  [IsScalarTower k (Linearization P k) M] {μ : GrMod (rayGrAlg ℓ k) M} {S : Finset (Cover x₀)}

/-- **A graded module is the push-down of any representation isomorphic to its piece
representation.** -/
theorem exists_bijective_pdMod (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S)
    (hconv : Convex (S : Set (Cover x₀))) (Y : Rep k (pieceQuiver S)) (hY : RespectsCover Y)
    [∀ i, FiniteDimensional k (Y.obj i)] (φ : grRep ℓ k μ S ≅ Y) :
    ∃ f : M →ₗ[Linearization P k] pdMod hconv Y hY, Function.Bijective f := by
  let F : M →ₗ[k] Y.Tot := φ.hom.tot ∘ₗ mToTot ℓ k μ S
  have hFsmul : ∀ (b : Linearization P k) (m : M), F (b • m) = linAct hconv hY b (F m) := by
    intro b m
    obtain ⟨z, rfl⟩ := linPres_surjective P k b
    simp only [F, LinearMap.coe_comp, Function.comp_apply]
    rw [mToTot_smul k hS, linAct_linPres]
    have hc := Rep.commute_pdAct (pieceProj S) (grRep ℓ k μ S) φ.hom.tot
      (Rep.Hom.isPdHom_tot _ φ.hom).1 (Rep.Hom.isPdHom_tot _ φ.hom).2 z
    exact LinearMap.congr_fun hc _
  refine ⟨{ toFun := F, map_add' := map_add F, map_smul' := hFsmul }, ?_, ?_⟩
  · intro m m' h
    have h1 : φ.inv.tot (F m) = φ.inv.tot (F m') := congrArg _ h
    simp only [F, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [← LinearMap.comp_apply φ.inv.tot, ← LinearMap.comp_apply φ.inv.tot,
      ← Rep.Hom.tot_comp, φ.hom_inv_id, Rep.Hom.tot_id] at h1
    have h2 := congrArg (totToM ℓ k μ S) h1
    simpa [totToM_mToTot ℓ k μ S hS] using h2
  · intro y
    refine ⟨totToM ℓ k μ S (φ.inv.tot y), ?_⟩
    change φ.hom.tot (mToTot ℓ k μ S (totToM ℓ k μ S (φ.inv.tot y))) = y
    rw [mToTot_totToM]
    have h : (φ.inv ≫ φ.hom).tot y = (𝟙 Y : Y ⟶ Y).tot y := by rw [φ.inv_hom_id]
    rw [Rep.Hom.tot_comp, Rep.Hom.tot_id] at h
    exact h

/-- A ray starting at `a.y` maps `W a` into `W` of the target of its lift at `a`. -/
lemma morElt_smul_W_src {a : Cover x₀} {w : M} (hw : w ∈ W ℓ k μ a) {z : P} (f : a.y ⟶ z)
    (hf : f ≠ 0) : morElt k f • w ∈ W ℓ k μ ⟨z, a.u ≫ cls f hf⟩ :=
  smul_mem_W ℓ k μ (liftAt a f hf) (Option.some_ne_none _) hf hw

/-- A ray not starting at `a.y` kills `W a`. -/
lemma morElt_smul_W_ne {a : Cover x₀} {w : M} (hw : w ∈ W ℓ k μ a) {y z : P} (f : y ⟶ z)
    (hy : y ≠ a.y) : morElt k f • w = 0 := by
  rw [← hw.1, ← mul_smul, morElt_mul_ne k (𝟙 a.y) f (Ne.symm hy), zero_smul]

/-- The cover objects carrying `M`. -/
def SuppC (μ : GrMod (rayGrAlg ℓ k) M) : Set (Cover x₀) := {a | W ℓ k μ a ≠ ⊥}

lemma mem_suppC_of_ne {a : Cover x₀} {w : M} (hw : w ∈ W ℓ k μ a) (h0 : w ≠ 0) :
    a ∈ SuppC k μ := fun h ↦ h0 (by rw [h] at hw; exact (Submodule.mem_bot k).1 hw)

/-- `projW` commutes with the homogeneous projections. -/
lemma projW_proj (a : Cover x₀) (g : Pi1 x₀) (m : M) :
    projW ℓ k μ a (μ.proj g m) = if gOf ℓ a = g then projW ℓ k μ a m else 0 := by
  change morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) (μ.proj g m) = _
  split_ifs with h
  · subst h; rw [Grading.proj_proj]; rfl
  · rw [μ.orth _ _ h, smul_zero]

variable (μ) in
/-- Rays from `T` to outside `T` act by zero. -/
def PiecesHyp (T : Set (Cover x₀)) : Prop :=
  ∀ a c, a ∈ T → c ∉ T → ∀ {w : M}, w ∈ W ℓ k μ a → ∀ (f : a.y ⟶ c.y) (hf : f ≠ 0),
    (⟨c.y, a.u ≫ cls f hf⟩ : Cover x₀) = c → morElt k f • w = 0

variable (μ) in
/-- The set of vectors whose pieces outside `T` vanish. -/
def piecesIn (T : Set (Cover x₀)) (hT : PiecesHyp k μ T) :
    Submodule (Linearization P k) M where
  carrier := {m | ∀ c ∉ T, projW ℓ k μ c m = 0}
  add_mem' hm hn c hc := by rw [map_add, hm c hc, hn c hc, add_zero]
  zero_mem' c _ := map_zero _
  smul_mem' b m hm c hc := by
    rw [← (linBasisR k P).sum_repr b, Finset.sum_smul, map_sum]
    refine Finset.sum_eq_zero fun ν _ ↦ ?_
    rw [smul_assoc, map_smul, linBasisR_apply]
    obtain ⟨y, z, f, hf⟩ := ν
    rw [← sum_projW ℓ k μ m, Finset.smul_sum, map_sum]
    have hz : ∀ a ∈ suppSet ℓ k μ,
        projW ℓ k μ c (morElt k f • projW ℓ k μ a m) = 0 := by
      intro a _
      by_cases haT : a ∈ T
      · have hwa := projW_mem ℓ k μ a m
        by_cases hy : y = a.y
        · subst hy
          have hmem := morElt_smul_W_src k hwa f hf
          rw [projW_of_mem ℓ k μ hmem]
          split_ifs with hc'
          · subst hc'
            exact hT a _ haT hc hwa f hf rfl
          · rfl
        · rw [morElt_smul_W_ne k hwa f hy, map_zero]
      · rw [hm a haT, smul_zero, map_zero]
    rw [Finset.sum_eq_zero hz, smul_zero]

lemma isGrSub_piecesIn (T : Set (Cover x₀)) (hT : PiecesHyp k μ T) :
    IsGrSub μ (piecesIn k μ T hT) := by
  intro m hm g c hc
  rw [projW_proj]
  split_ifs
  · exact hm c hc
  · rfl

/-- Projections of a sum of pieces. -/
lemma projW_sum_pieces (s : Finset (Cover x₀)) (c : Cover x₀) (m : M) :
    projW ℓ k μ c (∑ a ∈ s, projW ℓ k μ a m) = if c ∈ s then projW ℓ k μ c m else 0 := by
  rw [map_sum]
  simp_rw [projW_of_mem ℓ k μ (projW_mem ℓ k μ _ m)]
  rw [Finset.sum_ite_eq]

/-- **The support of a graded-indecomposable module is connected** through nonzero morphisms
of the cover. -/
theorem suppC_connected (hind : IsGrIndec μ) (T : Set (Cover x₀))
    (hT : ∀ a b, a ∈ T → b ∈ SuppC k μ → ((∃ f : a ⟶ b, f ≠ 0) ∨ (∃ f : b ⟶ a, f ≠ 0)) →
      b ∈ T) :
    (∀ a ∈ SuppC k μ, a ∈ T) ∨ (∀ a ∈ SuppC k μ, a ∉ T) := by
  have hlift : ∀ (a c : Cover x₀) (f : a.y ⟶ c.y) (hf : f ≠ 0),
      (⟨c.y, a.u ≫ cls f hf⟩ : Cover x₀) = c → ∃ g : a ⟶ c, g ≠ 0 := by
    intro a c f hf hcov
    have : ∃ g : a ⟶ (⟨c.y, a.u ≫ cls f hf⟩ : Cover x₀), g ≠ 0 :=
      ⟨liftAt a f hf, Option.some_ne_none _⟩
    rwa [hcov] at this
  have h1 : PiecesHyp k μ T := by
    intro a c ha hc w hw f hf hcov
    by_contra h0
    have hmem := morElt_smul_W_src k hw f hf
    rw [hcov] at hmem
    exact hc (hT a c ha (mem_suppC_of_ne k hmem h0) (Or.inl (hlift a c f hf hcov)))
  have h2 : PiecesHyp k μ Tᶜ := by
    intro a c ha hc w hw f hf hcov
    by_contra h0
    have hw0 : w ≠ 0 := fun h ↦ h0 (by rw [h, smul_zero])
    rw [Set.notMem_compl_iff] at hc
    exact ha (hT c a hc (mem_suppC_of_ne k hw hw0) (Or.inr (hlift a c f hf hcov)))
  set U := piecesIn k μ T h1
  set V := piecesIn k μ Tᶜ h2
  have hcompl : IsCompl U V := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro m ⟨hmU, hmV⟩
      rw [Submodule.mem_bot, ← sum_projW ℓ k μ m]
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      by_cases ha : a ∈ T
      · exact hmV a (Set.notMem_compl_iff.2 ha)
      · exact hmU a ha
    · rw [codisjoint_iff, eq_top_iff]
      intro m _
      classical
      have hsplit : m = ∑ a ∈ (suppSet ℓ k μ).filter (· ∈ T), projW ℓ k μ a m +
          ∑ a ∈ (suppSet ℓ k μ).filter (· ∉ T), projW ℓ k μ a m := by
        rw [Finset.sum_filter_add_sum_filter_not, sum_projW]
      rw [hsplit]
      refine Submodule.add_mem_sup (fun c hc ↦ ?_) (fun c hc ↦ ?_)
      · rw [projW_sum_pieces, if_neg (fun h ↦ hc (Finset.mem_filter.1 h).2)]
      · rw [projW_sum_pieces, if_neg]
        intro h
        exact absurd (Set.notMem_compl_iff.1 hc) (Finset.mem_filter.1 h).2
  rcases hind U V (isGrSub_piecesIn k T h1) (isGrSub_piecesIn k Tᶜ h2) hcompl with h | h
  · right
    intro a ha haT
    apply ha
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ U := fun c hc ↦ by
      rw [projW_of_mem ℓ k μ hw, if_neg (fun (e : c = a) ↦ hc (e ▸ haT))]
    rw [h] at this; exact this
  · left
    intro a ha
    by_contra haT
    apply ha
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ V := fun c hc ↦ by
      rw [Set.notMem_compl_iff] at hc
      rw [projW_of_mem ℓ k μ hw, if_neg (fun (e : c = a) ↦ haT (e ▸ hc))]
    rw [h] at this; exact this

end LargeIndecomposable.RayCat
