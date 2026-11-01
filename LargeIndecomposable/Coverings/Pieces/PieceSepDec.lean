module

public import LargeIndecomposable.Coverings.Pieces.PieceRad

/-!
# The class decomposition of the radical of a piece projective

For a class `F` of points (under `Cl`), summing the idempotents `e_y`, `y ∈ F`, is an
endomorphism of `rad P(x)` (`classOp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} (hpar : ParEq S)
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)
  {x : (pieceQuiver S).V}

/-- The underlying algebra element of a radical element. -/
def rv (r : (pieceDirData (k := k) hacyc).RadP x) : PieceAlg k S := r.1.1

lemma rv_mul_e (r : (pieceDirData (k := k) hacyc).RadP x) : rv hacyc r * pev x = rv hacyc r :=
  r.1.2

lemma e_mul_rv (r : (pieceDirData (k := k) hacyc).RadP x) : pev x * rv hacyc r = 0 :=
  r.2

lemma rv_smul (a : PieceAlg k S) (r : (pieceDirData (k := k) hacyc).RadP x) :
    rv hacyc (a • r) = a * rv hacyc r := rfl

lemma rv_add (r s : (pieceDirData (k := k) hacyc).RadP x) :
    rv hacyc (r + s) = rv hacyc r + rv hacyc s := rfl

lemma rv_sum {ι : Type*} (F : Finset ι) (r : ι → (pieceDirData (k := k) hacyc).RadP x) :
    rv hacyc (∑ i ∈ F, r i) = ∑ i ∈ F, rv hacyc (r i) := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rv_add, ih]

lemma rv_injective : Function.Injective (rv (k := k) hacyc (x := x)) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

/-- **The class operator.** -/
def classOp (hpar : ParEq S) (F : Finset (pieceQuiver S).V) (hxF : x ∉ F)
    (hF : ∀ y z, y ∈ F → (z ∈ F ↔ Cl x y z)) :
    (pieceDirData (k := k) hacyc).RadP x →ₗ[PieceAlg k S] (pieceDirData (k := k) hacyc).RadP x where
  toFun r := ∑ y ∈ F, pev (k := k) y • r
  map_add' r s := by simp only [smul_add, Finset.sum_add_distrib]
  map_smul' a r := by
    refine rv_injective (k := k) (x := x) hacyc ?_
    rw [RingHom.id_apply, rv_smul, rv_sum, rv_sum]
    simp only [rv_smul]
    exact classSum_smul hpar hacyc (rv_mul_e hacyc r) (e_mul_rv hacyc r) F hxF hF a

lemma rv_classOp (F : Finset (pieceQuiver S).V) (hxF : x ∉ F)
    (hF : ∀ y z, y ∈ F → (z ∈ F ↔ Cl x y z)) (r : (pieceDirData (k := k) hacyc).RadP x) :
    rv hacyc (classOp hacyc hpar F hxF hF r) = ∑ y ∈ F, pev (k := k) y * rv hacyc r := by
  change rv hacyc (∑ y ∈ F, pev (k := k) y • r) = _
  rw [rv_sum]
  rfl

variable (x) in
open Classical in
/-- The class of `y`. -/
def classOf (y : (pieceQuiver S).V) : Finset (pieceQuiver S).V := Finset.univ.filter (Cl x y)

omit [Fintype P] [DecidableEq P] in
lemma mem_classOf {y z : (pieceQuiver S).V} : z ∈ classOf x y ↔ Cl x y z := by
  classical
  simp [classOf]

omit [Fintype P] [DecidableEq P] in
lemma x_not_mem_classOf {y : (pieceQuiver S).V} (hy : y ≠ x) : x ∉ classOf x y := fun h ↦
  ne_x_of_cl (mem_classOf.1 h) hy rfl

omit [Fintype P] [DecidableEq P] in
lemma classOf_spec (y : (pieceQuiver S).V) :
    ∀ a b, a ∈ classOf x y → (b ∈ classOf x y ↔ Cl x a b) := by
  intro a b ha
  rw [mem_classOf] at ha ⊢
  exact ⟨fun hb ↦ cl_trans (cl_symm ha) hb, fun hb ↦ cl_trans ha hb⟩

omit [Fintype P] [DecidableEq P] in
lemma classOf_eq_of_mem {y z : (pieceQuiver S).V} (h : z ∈ classOf x y) :
    classOf x z = classOf x y := by
  ext w
  rw [mem_classOf, mem_classOf]
  have h' := mem_classOf.1 h
  exact ⟨fun hw ↦ cl_trans h' hw, fun hw ↦ cl_trans (cl_symm h') hw⟩

/-- Idempotence of class sums. -/
lemma classSum_idem (F : Finset (pieceQuiver S).V) (v : PieceAlg k S) :
    ∑ y ∈ F, pev (k := k) y * ∑ z ∈ F, pev z * v = ∑ y ∈ F, pev y * v := by
  classical
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single y]
  · rw [← mul_assoc, ev_mul_ev, if_pos rfl]
  · intro z _ hz
    rw [← mul_assoc, ev_mul_ev, if_neg (Ne.symm hz), zero_mul]
  · intro h; exact absurd hy h

/-- Orthogonality of class sums over disjoint sets. -/
lemma classSum_orth {F G : Finset (pieceQuiver S).V} (h : Disjoint F G) (v : PieceAlg k S) :
    ∑ y ∈ G, pev (k := k) y * ∑ z ∈ F, pev z * v = 0 := by
  classical
  refine Finset.sum_eq_zero fun y hy ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun z hz ↦ ?_
  have hyz : y ≠ z := fun e ↦ Finset.disjoint_left.1 h (e ▸ hz) hy
  rw [← mul_assoc, ev_mul_ev, if_neg hyz, zero_mul]

include hpar in
lemma pbvec_word {y : (pieceQuiver S).V} (hy : RPt x y) :
    ∃ l, l ≠ [] ∧ PathFrom x l y ∧ pbvec (k := k) x y = pmk (word k (pieceQuiver S) l) := by
  obtain ⟨l, hl⟩ := exists_path_of_gval hy.2
  refine ⟨l, ?_, hl, (pmk_word_eq_bvec hpar hl).symm⟩
  rintro rfl
  exact hy.1 (show x = y from hl).symm

include hpar in
lemma pbvec_mul_e {y : (pieceQuiver S).V} (hy : RPt x y) :
    pbvec (k := k) x y * pev x = pbvec x y := by
  obtain ⟨l, hl0, hl, he⟩ := pbvec_word (k := k) hpar hy
  rw [he, ← map_mul, word_mul_vertex_path k hl0 hl x, if_pos rfl]

include hpar in
lemma e_mul_pbvec {y : (pieceQuiver S).V} (hy : RPt x y) (z : (pieceQuiver S).V) :
    pev (k := k) z * pbvec x y = if z = y then pbvec x y else 0 := by
  obtain ⟨l, hl0, hl, he⟩ := pbvec_word (k := k) hpar hy
  rw [he, ← map_mul, vertex_mul_word_path k hl0 hl z]
  split_ifs <;> simp

/-- The radical element of a basis vector. -/
def relt {y : (pieceQuiver S).V} (hy : RPt x y) : (pieceDirData (k := k) hacyc).RadP x :=
  ⟨⟨pbvec x y, pbvec_mul_e hpar hy⟩, by
    change pev x * pbvec x y = 0
    rw [e_mul_pbvec hpar hy, if_neg (Ne.symm hy.1)]⟩

lemma rv_relt {y : (pieceQuiver S).V} (hy : RPt x y) :
    rv hacyc (relt hpar hacyc hy) = pbvec (k := k) x y := rfl

lemma relt_ne_zero {y : (pieceQuiver S).V} (hy : RPt x y) : relt (k := k) hpar hacyc hy ≠ 0 := by
  intro h
  have := congrArg (rv hacyc) h
  rw [rv_relt] at this
  exact bvec_ne_zero hpar hy.1 hy.2 this

section Brick

variable {y₀ : (pieceQuiver S).V} (hy₀ : RPt x y₀)

/-- The class operator of the class of `y₀`. -/
abbrev cop := classOp (k := k) hacyc hpar (classOf x y₀) (x_not_mem_classOf hy₀.1) (classOf_spec y₀)

include hpar hy₀ in
lemma rpt_of_mem {y : (pieceQuiver S).V} (hy : y ∈ classOf x y₀) : RPt x y :=
  (rpt_iff_of_cl hpar (mem_classOf.1 hy)).1 hy₀

lemma cop_relt {y : (pieceQuiver S).V} (hy : y ∈ classOf x y₀) :
    cop hpar hacyc hy₀ (relt hpar hacyc (rpt_of_mem hpar hy₀ hy)) =
      relt (k := k) hpar hacyc (rpt_of_mem hpar hy₀ hy) := by
  apply rv_injective (k := k) (x := x) hacyc
  rw [rv_classOp, rv_relt]
  rw [Finset.sum_eq_single y]
  · rw [e_mul_pbvec hpar (rpt_of_mem hpar hy₀ hy), if_pos rfl]
  · intro z _ hz
    rw [e_mul_pbvec hpar (rpt_of_mem hpar hy₀ hy), if_neg hz]
  · intro h; exact absurd hy h

/-- The basis vector as an element of the image. -/
def celt {y : (pieceQuiver S).V} (hy : y ∈ classOf x y₀) :
    LinearMap.range (cop (k := k) hpar hacyc hy₀) :=
  ⟨relt hpar hacyc (rpt_of_mem hpar hy₀ hy), ⟨_, cop_relt hpar hacyc hy₀ hy⟩⟩

lemma celt_ne_zero {y : (pieceQuiver S).V} (hy : y ∈ classOf x y₀) :
    celt (k := k) hpar hacyc hy₀ hy ≠ 0 := fun h ↦
  relt_ne_zero hpar hacyc (rpt_of_mem hpar hy₀ hy) (congrArg Subtype.val h)

lemma cop_idem (r : (pieceDirData (k := k) hacyc).RadP x) :
    cop hpar hacyc hy₀ (cop hpar hacyc hy₀ r) = cop (k := k) hpar hacyc hy₀ r := by
  apply rv_injective (k := k) (x := x) hacyc
  rw [rv_classOp, rv_classOp]
  exact classSum_idem _ _

lemma rv_celt {y : (pieceQuiver S).V} (hy : y ∈ classOf x y₀) :
    rv hacyc (celt (k := k) hpar hacyc hy₀ hy).1 = pbvec x y := rfl

/-- Every element of the image is a combination of the basis vectors. -/
lemma image_eq_sum (m : LinearMap.range (cop (k := k) hpar hacyc hy₀)) :
    ∃ c : (pieceQuiver S).V → k, m = ∑ y ∈ (classOf x y₀).attach,
      algebraMap k (PieceAlg k S) (c y.1) • celt (k := k) hpar hacyc hy₀ y.2 := by
  classical
  obtain ⟨r, hr⟩ := m.2
  have hfix : m.1 = cop hpar hacyc hy₀ m.1 := by rw [← hr, cop_idem]
  have hm : rv hacyc m.1 = ∑ z ∈ classOf x y₀, pev (k := k) z * rv hacyc m.1 := by
    conv_lhs => rw [hfix]
    rw [rv_classOp]
  have hc : ∀ z, ∃ c : k, z ∈ classOf x y₀ → pev (k := k) z * rv hacyc m.1 = c • pbvec x z := by
    intro z
    by_cases hz : z ∈ classOf x y₀
    · obtain ⟨c, hc⟩ := corner_rad hpar (rv_mul_e hacyc m.1) (rpt_of_mem hpar hy₀ hz).1
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨0, fun h ↦ absurd h hz⟩
  choose c hc using hc
  refine ⟨c, Subtype.ext (rv_injective (k := k) (x := x) hacyc ?_)⟩
  rw [hm, Submodule.coe_sum, rv_sum]
  rw [← Finset.sum_attach (classOf x y₀)]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [hc y.1 y.2]
  exact Algebra.smul_def _ _

set_option maxHeartbeats 1600000 in
/-- **The image of a class operator is a brick.** -/
theorem cop_brick (φ : AR.FDMod.ofSub (P := (pieceDirData (k := k) hacyc).RadP x) (LinearMap.range (cop (k := k) hpar hacyc hy₀)) ⟶
    AR.FDMod.ofSub (P := (pieceDirData (k := k) hacyc).RadP x) (LinearMap.range (cop (k := k) hpar hacyc hy₀))) :
    ∃ c : k, AR.FDMod.lin φ = c • LinearMap.id := by
  classical
  -- `φ` is a scalar on each basis vector
  have hloc : ∀ y (hy : y ∈ classOf x y₀), ∃ c : k,
      AR.FDMod.lin φ (celt (k := k) hpar hacyc hy₀ hy) =
        algebraMap k (PieceAlg k S) c • celt (k := k) hpar hacyc hy₀ hy := by
    intro y hy
    have hRy := rpt_of_mem hpar hy₀ hy
    have hfix : pev (k := k) y • celt (k := k) hpar hacyc hy₀ hy =
        celt (k := k) hpar hacyc hy₀ hy := by
      apply Subtype.ext; apply rv_injective (k := k) (x := x) hacyc
      change pev (k := k) y * pbvec x y = pbvec x y
      rw [e_mul_pbvec hpar hRy, if_pos rfl]
    have h1 : AR.FDMod.lin φ (celt (k := k) hpar hacyc hy₀ hy) =
        pev (k := k) y • AR.FDMod.lin φ (celt (k := k) hpar hacyc hy₀ hy) := by
      conv_lhs => rw [← hfix]
      exact map_smul _ _ _
    obtain ⟨c, hc⟩ := corner_rad hpar
      (rv_mul_e hacyc (AR.FDMod.lin φ (celt (k := k) hpar hacyc hy₀ hy)).1) hRy.1
    refine ⟨c, Subtype.ext (rv_injective (k := k) (x := x) hacyc ?_)⟩
    have h2 := congrArg (fun m : LinearMap.range (cop (k := k) hpar hacyc hy₀) ↦ rv hacyc m.1) h1
    simp only at h2
    rw [h2]
    change pev (k := k) y * rv hacyc _ = algebraMap k (PieceAlg k S) c * pbvec x y
    rw [hc, Algebra.smul_def]
  choose cf hcf using hloc
  have hy₀F : y₀ ∈ classOf x y₀ := mem_classOf.2 (Relation.EqvGen.refl _)
  have hrvc : ∀ y (hy : y ∈ classOf x y₀),
      rv hacyc (AR.FDMod.lin φ (celt (k := k) hpar hacyc hy₀ hy)).1 =
        algebraMap k (PieceAlg k S) (cf y hy) * pbvec x y := fun y hy ↦ by
    rw [hcf y hy]; rfl
  -- the scalars agree along the class
  have hstep : ∀ a b (ha : a ∈ classOf x y₀) (hb : b ∈ classOf x y₀), ExtR x a b →
      cf a ha = cf b hb := by
    intro a b ha hb hab
    obtain ⟨-, -, w, hw, -⟩ := hab
    obtain ⟨l, -, hl, hla⟩ := pbvec_word (k := k) hpar (rpt_of_mem hpar hy₀ ha)
    have hpb : pbvec (k := k) x b = pmk (word k (pieceQuiver S) w) * pbvec x a := by
      rw [hla, ← map_mul, ← word_append, pmk_word_eq_bvec hpar (pathFrom_append l w hl hw)]
    have hcb : celt (k := k) hpar hacyc hy₀ hb =
        pmk (word k (pieceQuiver S) w) • celt (k := k) hpar hacyc hy₀ ha := by
      apply Subtype.ext; apply rv_injective (k := k) (x := x) hacyc
      exact hpb
    have h1 := hrvc b hb
    rw [hcb, map_smul] at h1
    change pmk (word k (pieceQuiver S) w) * rv hacyc (AR.FDMod.lin φ _).1 = _ at h1
    rw [hrvc a ha, ← mul_assoc, ← Algebra.commutes, mul_assoc, ← hpb] at h1
    have h2 : (cf a ha - cf b hb) • pbvec (k := k) x b = 0 := by
      have hsm : ∀ p q r : PieceAlg k S, (p - q) * r = p * r - q * r := fun p q r ↦ sub_mul p q r
      rw [Algebra.smul_def, map_sub, hsm, h1]
      exact sub_self (algebraMap k (PieceAlg k S) (cf b hb) * pbvec x b)
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (bvec_ne_zero hpar (rpt_of_mem hpar hy₀ hb).1 (rpt_of_mem hpar hy₀ hb).2)
  have hconst : ∀ a b, Cl x a b → ∀ (ha : a ∈ classOf x y₀) (hb : b ∈ classOf x y₀),
      cf a ha = cf b hb := by
    intro a b h
    induction h with
    | rel a b hab => exact fun ha hb ↦ hstep a b ha hb hab
    | refl => exact fun _ _ ↦ rfl
    | symm a b _ ih => exact fun ha hb ↦ (ih hb ha).symm
    | trans a b c hab _ ih1 ih2 =>
      intro ha hc
      have hb : b ∈ classOf x y₀ := (classOf_spec y₀ a b ha).2 hab
      exact (ih1 ha hb).trans (ih2 hb hc)
  refine ⟨cf y₀ hy₀F, LinearMap.ext fun m ↦ ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul (PieceAlg k S)]
  obtain ⟨c, rfl⟩ := image_eq_sum hpar hacyc hy₀ m
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [map_smul, hcf y.1 y.2, hconst y.1 y₀ (cl_symm (mem_classOf.1 y.2)) y.2 hy₀F, smul_smul,
    smul_smul, ← map_mul, ← map_mul, mul_comm]

set_option maxHeartbeats 1600000 in
lemma cop_indec : AR.IsIndecMod (PieceAlg k S) (LinearMap.range (cop (k := k) hpar hacyc hy₀)) :=
  AR.isIndecMod_of_brick (M := AR.FDMod.ofSub (P := (pieceDirData (k := k) hacyc).RadP x)
    (LinearMap.range (cop (k := k) hpar hacyc hy₀))) (cop_brick hpar hacyc hy₀)

end Brick

section Assemble

variable (x) in
open Classical in
/-- The classes of points reached from `x`. -/
def classes : Finset (Finset (pieceQuiver S).V) :=
  (Finset.univ.filter (RPt x)).image (classOf x)

variable (x) in
/-- The index type of the class decomposition. -/
abbrev CIdx : Type u := ULift.{u} {F // F ∈ classes (S := S) x}

lemma cidx_spec (i : CIdx (S := S) x) : ∃ y, RPt x y ∧ classOf x y = i.down.1 := by
  classical
  obtain ⟨y, hy, he⟩ := Finset.mem_image.1 i.down.2
  exact ⟨y, (Finset.mem_filter.1 hy).2, he⟩

/-- A representative of a class. -/
def crep (i : CIdx (S := S) x) : (pieceQuiver S).V := (cidx_spec i).choose

lemma crep_rpt (i : CIdx (S := S) x) : RPt x (crep i) := (cidx_spec i).choose_spec.1

lemma classOf_crep (i : CIdx (S := S) x) : classOf x (crep i) = i.down.1 :=
  (cidx_spec i).choose_spec.2

lemma classes_disjoint {i j : CIdx (S := S) x} (h : i ≠ j) :
    Disjoint (classOf x (crep i)) (classOf x (crep j)) := by
  rw [Finset.disjoint_left]
  intro z hzi hzj
  apply h
  have h1 := classOf_eq_of_mem hzi
  have h2 := classOf_eq_of_mem hzj
  rw [classOf_crep] at h1 h2
  exact ULift.ext (Subtype.ext (h1.symm.trans h2))

include hpar in
lemma sum_classes {v : PieceAlg k S} (hv : v * pev x = v) (hvx : pev (k := k) x * v = 0) :
    ∑ i : CIdx (S := S) x, ∑ y ∈ classOf x (crep i), pev (k := k) y * v = v := by
  classical
  have h1 : ∑ i : CIdx (S := S) x, ∑ y ∈ classOf x (crep i), pev (k := k) y * v =
      ∑ F ∈ classes (S := S) x, ∑ y ∈ F, pev (k := k) y * v := by
    rw [← Finset.sum_coe_sort (classes (S := S) x)]
    refine Fintype.sum_equiv Equiv.ulift _ _ fun i ↦ ?_
    rw [classOf_crep]
    rfl
  have hdisj : (classes (S := S) x : Set (Finset (pieceQuiver S).V)).PairwiseDisjoint id := by
    intro F hF G hG hFG
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro z hzF hzG
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hG
    exact hFG ((classOf_eq_of_mem hzF).symm.trans (classOf_eq_of_mem hzG))
  have hbU : (classes (S := S) x).biUnion id = Finset.univ.filter (RPt x) := by
    ext y
    simp only [Finset.mem_biUnion, id, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨F, hF, hyF⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hF
      exact (rpt_iff_of_cl hpar (mem_classOf.1 hyF)).1 (Finset.mem_filter.1 ha).2
    · intro hy
      exact ⟨classOf x y, Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, rfl⟩,
        mem_classOf.2 (Relation.EqvGen.refl _)⟩
  rw [h1]
  have h2 := Finset.sum_biUnion hdisj (f := fun y ↦ pev (k := k) y * v)
  simp only [id] at h2
  rw [← h2]
  change ∑ y ∈ (classes (S := S) x).biUnion id, pev (k := k) y * v = v
  rw [hbU]
  rw [Finset.sum_filter_of_ne fun y _ hy ↦ ?_]
  · rw [← Finset.sum_mul, sum_ev, one_mul]
  · by_contra hR
    apply hy
    by_cases hyx : y = x
    · rw [hyx, hvx]
    · have hg : gval x y = 0 := by
        by_contra hg; exact hR ⟨hyx, hg⟩
      obtain ⟨c, hc⟩ := corner_rad hpar hv hyx
      rw [hc, bvec_eq_zero hpar hg, smul_zero]

set_option maxHeartbeats 1600000 in
/-- **The class decomposition of `rad P(x)`.** -/
def radDecomp : AR.Decomp ((pieceDirData (k := k) hacyc).RadP x) :=
  AR.Decomp.ofIdem (ι := CIdx (S := S) x) (fun i ↦ cop hpar hacyc (crep_rpt i))
    (fun i r ↦ cop_idem hpar hacyc (crep_rpt i) r)
    (fun i j h r ↦ by
      apply rv_injective (k := k) (x := x) hacyc
      rw [rv_classOp, rv_classOp]
      exact classSum_orth (classes_disjoint h) _)
    (fun r ↦ by
      apply rv_injective (k := k) (x := x) hacyc
      rw [rv_sum]
      simp only [rv_classOp]
      convert sum_classes hpar (rv_mul_e hacyc r) (e_mul_rv hacyc r) using 2 with i
      exact rv_classOp (k := k) (hacyc := hacyc) (hpar := hpar) _ _ _ r)
    (fun i ↦ cop_indec hpar hacyc (crep_rpt i))
    (fun i ↦ ⟨⟨celt (k := k) hpar hacyc (crep_rpt i) (mem_classOf.2 (Relation.EqvGen.refl _)), 0,
      celt_ne_zero hpar hacyc (crep_rpt i) _⟩⟩)

lemma supp_radDecomp (i : CIdx (S := S) x) {u : (pieceQuiver S).V}
    (hu : u ∈ (pieceDirData (k := k) hacyc).Supp ((radDecomp hpar hacyc).obj i)) :
    u ∈ classOf x (crep i) := by
  classical
  obtain ⟨m, hm⟩ := hu
  by_contra huF
  apply hm
  obtain ⟨r, hr⟩ := m.2
  have hfix : m.1 = cop hpar hacyc (crep_rpt i) m.1 := by rw [← hr, cop_idem]
  apply Subtype.ext; apply rv_injective (k := k) (x := x) hacyc
  change pev (k := k) u * rv hacyc m.1 = rv hacyc 0
  rw [hfix, rv_classOp, Finset.mul_sum]
  refine (Finset.sum_eq_zero fun y hy ↦ ?_).trans rfl
  have huy : u ≠ y := fun h ↦ huF (h ▸ hy)
  rw [← mul_assoc, ev_mul_ev, if_neg huy, zero_mul]

/-- **The class decomposition separates `x`** once connectivity among the non-predecessors of
`x` implies lying in one class. -/
theorem sepDecomp_radDecomp
    (hcl : ∀ u v, RPt x u → RPt x v →
      (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x) u v → Cl x u v) :
    (pieceDirData (k := k) hacyc).SepDecomp x (radDecomp hpar hacyc) := by
  intro i j hij u v hu hv hc
  have hu' := supp_radDecomp hpar hacyc i hu
  have hv' := supp_radDecomp hpar hacyc j hv
  have huv := hcl u v (rpt_iff_of_cl hpar (mem_classOf.1 hu') |>.1 (crep_rpt i))
    (rpt_iff_of_cl hpar (mem_classOf.1 hv') |>.1 (crep_rpt j)) hc
  have h1 := classOf_eq_of_mem hu'
  have h2 := classOf_eq_of_mem hv'
  have h3 : classOf x u = classOf x v := by
    ext w
    exact ⟨fun h ↦ mem_classOf.2 (cl_trans (cl_symm huv) (mem_classOf.1 h)),
      fun h ↦ mem_classOf.2 (cl_trans huv (mem_classOf.1 h))⟩
  apply hij
  exact ULift.ext (Subtype.ext ((classOf_crep i).symm.trans
    ((h1.symm.trans (h3.trans h2)).trans (classOf_crep j))))

end Assemble

end LargeIndecomposable.RayCat
