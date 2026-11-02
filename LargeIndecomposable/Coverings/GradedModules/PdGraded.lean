module

public import LargeIndecomposable.Coverings.GradedModules.GradedPieceAct
public import LargeIndecomposable.Coverings.GradedModules.RayGrading
public import LargeIndecomposable.Coverings.GradedModules.PushDownIndecomposable
public import LargeIndecomposable.BongartzTheorem.ContourExclusion.NoContour
public import LargeIndecomposable.BongartzTheorem.Reduction.CoverDichotomy

/-!
# The grading of a push-down

The total space of a representation of a convex piece of the cover is graded by the degrees of
the points (`pdGr`). The push-down of an indecomposable representation is graded-indecomposable
(`isGrIndec_pdGr`), hence indecomposable when the fundamental group is torsion-free
(`isIndecMod_pdMod`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y)
  {k : Type u} [Field k] {S : Finset (Cover x₀)}

/-- The degree of a vertex of a piece. -/
def vDeg (i : (pieceQuiver S).V) : Pi1 x₀ := gOf ℓ (pt S i)

variable (X : Rep k (pieceQuiver S))

/-- The degree part of the total space. -/
def degProj (g : Pi1 x₀) : X.Tot →ₗ[k] X.Tot :=
  LinearMap.pi fun i ↦ if vDeg ℓ i = g then LinearMap.proj i else 0

lemma degProj_apply (g : Pi1 x₀) (x : X.Tot) (i : (pieceQuiver S).V) :
    degProj ℓ X g x i = if vDeg ℓ i = g then x i else 0 := by
  simp only [degProj, LinearMap.pi_apply]
  split_ifs <;> rfl

/-- The grading of the total space. -/
def totGrading : Grading (Pi1 x₀) k X.Tot where
  proj := degProj ℓ X
  supp := Finset.univ.image (vDeg ℓ)
  orth g h hgh v := by
    funext i
    rw [degProj_apply]
    split_ifs with h1
    · rw [degProj_apply, if_neg fun h2 ↦ hgh (h1.symm.trans h2)]
      rfl
    · rfl
  out g hg v := by
    funext i
    rw [degProj_apply, if_neg fun h ↦ hg (by
      rw [← h]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rfl
  sum_eq v := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single (vDeg ℓ i)]
    · rw [degProj_apply, if_pos rfl]
    · intro g _ hg
      rw [degProj_apply, if_neg fun h ↦ hg h.symm]
    · intro h
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ i)) h

lemma mem_totGrading {g : Pi1 x₀} {x : X.Tot} :
    (totGrading ℓ X).Mem g x ↔ ∀ i, vDeg ℓ i ≠ g → x i = 0 := by
  constructor
  · intro h i hi
    have := congrFun h i
    change degProj ℓ X g x i = x i at this
    rw [degProj_apply, if_neg hi] at this
    exact this.symm
  · intro h
    funext i
    change degProj ℓ X g x i = x i
    rw [degProj_apply]
    split_ifs with h1
    · rfl
    · exact (h i h1).symm

/-- A path of the piece moves degrees by the degree of its value. -/
lemma vDeg_path {le : List (pieceQuiver S).A} {i j : (pieceQuiver S).V} (h : PathFrom i le j)
    (hv : val (compD S le i j h) ≠ 0) :
    vDeg ℓ j = rayDeg ℓ ⟨(pt S i).y, (pt S j).y, val (compD S le i j h), hv⟩ * vDeg ℓ i := by
  refine gOf_target ℓ (compD S le i j h) (fun h0 ↦ hv ?_) hv
  rw [h0, val_zero]

variable {X}
variable (hS : Convex (S : Set (Cover x₀))) (hX : RespectsCover X)
  [∀ i, FiniteDimensional k (X.obj i)]

/-- A path word moves homogeneous elements by the degree of its value. -/
lemma pathTot_mem {c : (quiver P).A} {l : List (quiver P).A} {x y : P}
    (hp : PathFrom (D := quiver P) x (c :: l) y) (hf : pathMor (c :: l) x y hp ≠ 0)
    {le : List (pieceQuiver S).A} (hle : le.map (pieceProj S).arr = c :: l) {h : Pi1 x₀}
    {m : X.Tot} (hm : (totGrading ℓ X).Mem h m) :
    (totGrading ℓ X).Mem (rayDeg ℓ ⟨x, y, _, hf⟩ * h) (X.pathTot le m) := by
  have hne : le ≠ [] := by
    rintro rfl
    simp at hle
  by_cases hc : ∃ i j, PathFrom i le j
  · obtain ⟨i, j, hij⟩ := hc
    have h1 : X.idm j ∘ₗ X.pathTot le ∘ₗ X.idm i = X.pathTot le := by
      rw [blk_term X le hne i j, if_pos hij]
    have hmap := pathFrom_map (pieceProj S) le i j hij
    rw [hle] at hmap
    obtain rfl : x = (pieceProj S).vert i :=
      pathFrom_src_unique _ _ _ _ _ (List.cons_ne_nil _ _) hp hmap
    obtain rfl : y = (pieceProj S).vert j := pathFrom_tgt_unique _ _ _ _ hp hmap
    have hvv : val (compD S le i j hij) = pathMor (c :: l) _ _ hp :=
      (val_compD S le i j hij).trans (pathMor_congr hle _ hp)
    have hv : val (compD S le i j hij) ≠ 0 := hvv ▸ hf
    have hdeg := vDeg_path ℓ hij hv
    have hsig : (⟨(pt S i).y, (pt S j).y, val (compD S le i j hij), hv⟩ : NZ P) =
        ⟨_, _, pathMor (c :: l) _ _ hp, hf⟩ :=
      Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext hvv))))
    rw [hsig] at hdeg
    rw [mem_totGrading]
    intro j' hj'
    rw [← h1]
    change X.idm j (X.pathTot le (X.idm i m)) j' = 0
    by_cases hjj : j' = j
    · subst hjj
      have him : X.idm i m = 0 := by
        have hi : m i = 0 := by
          refine (mem_totGrading ℓ X).1 hm i fun h2 ↦ hj' ?_
          rw [hdeg, h2]
        refine funext fun z ↦ ?_
        by_cases hz : z = i
        · subst hz
          simp [Rep.idm_apply, hi]
        · simp [Rep.idm_apply, Pi.single_eq_of_ne hz]
      rw [him, map_zero, map_zero]
      rfl
    · simp [Rep.idm_apply, Pi.single_eq_of_ne hjj]
  · push Not at hc
    rw [Rep.pathTot_eq_zero X le hc hne]
    exact (totGrading ℓ X).mem_zero _

/-- The basis elements of `k(P)` move degrees. -/
lemma smul_basis (ν : NZ P) {h : Pi1 x₀} {m : X.Tot}
    (hm : (totGrading ℓ X).Mem h m) :
    (totGrading ℓ X).Mem (rayDeg ℓ ν * h) (linAct hS hX (linBasisR k P ν) m) := by
  obtain ⟨x, y, f, hf⟩ := ν
  rw [linBasisR_apply]
  change (totGrading ℓ X).Mem _ (linAct hS hX (morElt k f) m)
  rw [morElt_of_ne k f hf]
  by_cases hiso : IsIso f
  · obtain ⟨rfl, he⟩ := eq_id_of_isIso f
    subst he
    change (totGrading ℓ X).Mem (rayDeg ℓ (idNZ x) * h) _
    rw [rayDeg_id, one_mul]
    have e1 : rayElt k ⟨x, x, eqToHom rfl, hf⟩ = linPres P k (vertex k (quiver P) x) :=
      rayElt_id k x
    rw [e1, linAct_linPres, Rep.pdAct_vertex, mem_totGrading]
    intro i hi
    rw [Rep.pdVert_apply]
    split_ifs
    · exact (mem_totGrading ℓ X).1 hm i hi
    · rfl
  · obtain ⟨c, l, hp, he⟩ := exists_path_cons f hf hiso
    subst he
    rw [← linPres_word k c l x y hp hf, linAct_linPres, Rep.pdAct_word_eq_sum, LinearMap.sum_apply]
    exact (totGrading ℓ X).mem_sum _ _ fun le hle ↦
      pathTot_mem ℓ hp hf ((Rep.mem_lab _ _ _).1 hle) hm

/-- **The grading of a push-down.** -/
def pdGr : GrMod (rayGrAlg ℓ k) (pdMod hS X hX) where
  toGrading := totGrading ℓ X
  smul_mem g h a m hg hm := by
    change (rayGrading ℓ k).Mem g a at hg
    rw [rayGrading_mem_iff] at hg
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ν, rfl, rfl⟩ := hz
      exact smul_basis ℓ hS hX ν hm
    | zero =>
      rw [zero_smul]
      exact (totGrading ℓ X).mem_zero _
    | add a b _ _ ha hb =>
      rw [add_smul]
      exact (totGrading ℓ X).mem_add ha hb
    | smul c a _ ha =>
      rw [smul_assoc]
      exact (totGrading ℓ X).mem_smul c ha


/-- A point is determined by its underlying object and its degree. -/
lemma eq_of_vert_vDeg {i j : (pieceQuiver S).V} (h1 : (pieceProj S).vert i = (pieceProj S).vert j)
    (h2 : vDeg ℓ i = vDeg ℓ j) : i = j :=
  Subtype.ext (eq_of_y_gOf ℓ h1 h2)

/-- **The push-down of an indecomposable is graded-indecomposable.** -/
theorem isGrIndec_pdGr (hind : X.IsIndec) : IsGrIndec (pdGr ℓ hS hX) := by
  intro U V hU hV hcompl
  let A := Linearization P k
  let M := pdMod hS X hX
  let e : M →ₗ[A] M := U.subtype ∘ₗ Submodule.projectionOnto U V hcompl
  have heU : ∀ u ∈ U, e u = u := fun u hu ↦
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hcompl ⟨u, hu⟩)
  have heV : ∀ v ∈ V, e v = 0 := fun v hv ↦
    congrArg Subtype.val (Submodule.projectionOnto_apply_right hcompl ⟨v, hv⟩)
  have hee : ∀ m, e (e m) = e m := fun m ↦ heU _ (Submodule.coe_mem _)
  have hsplit : ∀ m : M, ∃ u ∈ U, ∃ v ∈ V, m = u + v := fun m ↦ by
    have : m ∈ U ⊔ V := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, h⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, v, hv, h.symm⟩
  have hdeg : ∀ g (m : M), e ((pdGr ℓ hS hX).proj g m) = (pdGr ℓ hS hX).proj g (e m) := by
    intro g m
    obtain ⟨u, hu, v, hv, rfl⟩ := hsplit m
    rw [map_add, map_add, map_add, heU u hu, heV v hv, add_zero, heU _ (hU u hu g),
      heV _ (hV v hv g), add_zero]
  let f : X.Tot →ₗ[k] X.Tot := e.restrictScalars k
  have hact : ∀ a : A, ∀ x : X.Tot, f (linAct hS hX a x) = linAct hS hX a (f x) := fun a x ↦
    e.map_smul a x
  have hpd : Rep.IsPdHom (pieceProj S) f := by
    refine ⟨fun q ↦ LinearMap.ext fun x ↦ ?_, fun c ↦ LinearMap.ext fun x ↦ ?_⟩
    · have h := hact (linPres P k (vertex k (quiver P) q)) x
      rw [linAct_linPres, Rep.pdAct_vertex] at h
      exact h
    · have h := hact (linPres P k (arrow k (quiver P) c)) x
      rw [linAct_linPres, Rep.pdAct_arrow] at h
      exact h
  have hidm : ∀ i x, f (X.idm i x) = X.idm i (f x) := by
    intro i x
    have e1 : ∀ z : X.Tot, X.idm i z = degProj ℓ X (vDeg ℓ i)
        (X.pdVert (pieceProj S) ((pieceProj S).vert i) z) := fun z ↦ by
      funext j
      rw [degProj_apply, Rep.pdVert_apply]
      by_cases hj : j = i
      · subst hj
        simp [Rep.idm_apply]
      · have : ¬(vDeg ℓ j = vDeg ℓ i ∧ (pieceProj S).vert j = (pieceProj S).vert i) := fun h ↦
          hj (eq_of_vert_vDeg ℓ h.2 h.1)
        rw [Rep.idm_apply, Pi.single_eq_of_ne hj]
        by_cases h1 : vDeg ℓ j = vDeg ℓ i
        · rw [if_pos h1, if_neg fun h2 ↦ this ⟨h1, h2⟩]
        · rw [if_neg h1]
    rw [e1, e1]
    have h1 := hdeg (vDeg ℓ i) (X.pdVert (pieceProj S) ((pieceProj S).vert i) x)
    have h2 := LinearMap.congr_fun (hpd.1 ((pieceProj S).vert i)) x
    change f (X.pdVert (pieceProj S) _ x) = X.pdVert (pieceProj S) _ (f x) at h2
    change f (degProj ℓ X _ _) = degProj ℓ X _ (f _) at h1
    rw [h1, h2]
  have hblock := (Rep.isPdHom_iff _ f).1 hpd
  let φ : X ⟶ X := Rep.diagHom (pieceProj_locInj S) f hblock
  have hsingle : ∀ i (v : X.obj i), f (Pi.single i v) = Pi.single i (Rep.blk f i i v) := by
    intro i v
    have h1 : X.idm i (Pi.single i v) = Pi.single i v := by simp [Rep.idm_apply]
    have h2 := hidm i (Pi.single i v)
    rw [h1] at h2
    rw [h2]
    simp [Rep.idm_apply, Rep.blk]
  have hcoord : ∀ x i, f x i = Rep.blk f i i (x i) := by
    intro x i
    have h1 := hidm i x
    have h2 : X.idm i x = Pi.single i (x i) := by simp [Rep.idm_apply]
    rw [h2, hsingle] at h1
    have h3 := congrFun h1 i
    simpa [Rep.idm_apply] using h3.symm
  have hφφ : φ ≫ φ = φ := by
    refine Rep.hom_ext fun i ↦ ?_
    ext v
    change Rep.blk f i i (Rep.blk f i i v) = Rep.blk f i i v
    have h1 := hee (show M from (Pi.single i v : X.Tot))
    have h2 : f (f (Pi.single i v)) = f (Pi.single i v) := h1
    rw [hsingle, hsingle] at h2
    have h3 := congrFun h2 i
    simpa using h3
  rcases hind.2 φ hφφ with h | h
  · left
    have hf0 : ∀ x, f x = 0 := fun x ↦ funext fun i ↦ by
      rw [hcoord]
      have h1 := h i
      have h2 : Rep.blk f i i = 0 := by
        have := congrArg ModuleCat.Hom.hom h1
        exact this
      rw [h2]
      rfl
    refine eq_bot_iff.2 fun u hu ↦ (Submodule.mem_bot _).2 ?_
    rw [← heU u hu]
    exact hf0 u
  · right
    have hf1 : ∀ x, f x = x := fun x ↦ funext fun i ↦ by
      rw [hcoord]
      have h1 := congrArg (fun ψ : X ⟶ X ↦ (ψ.app i).hom (x i)) h
      exact h1
    refine eq_bot_iff.2 fun v hv ↦ (Submodule.mem_bot _).2 ?_
    have h1 := heV v hv
    have h2 : f v = v := hf1 v
    exact h2.symm.trans h1

include ℓ in
/-- **The push-down of an indecomposable is indecomposable.** -/
theorem isIndecMod_pdMod (htf : TorsionFree (Pi1 x₀)) (hind : X.IsIndec) :
    IsIndecMod (Linearization P k) (pdMod hS X hX) :=
  Graded.isIndecMod htf (isGrIndec_pdGr ℓ hS hX hind)

end LargeIndecomposable.RayCat
