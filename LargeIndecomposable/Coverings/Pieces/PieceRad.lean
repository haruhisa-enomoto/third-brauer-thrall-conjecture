module

public import LargeIndecomposable.Coverings.Pieces.PieceThin
public import LargeIndecomposable.Modules.Idempotents.IdemDecomp

/-!
# The radical of a vertex projective of a piece

Assume Lemma 4.2 for the piece (`ParEq`). For a point `x` and `y`, `pbvec x y` is the value of
the composite `x → y` in the piece algebra; every path word from `x` to `y` equals it
(`pmk_word_eq_bvec`), it is nonzero iff the composite is (`bvec_ne_zero`), and
`e_y a b_z` vanishes unless `y` is reached from `z` with nonzero composite (`corner_bvec`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} (hpar : ParEq S) {x : (pieceQuiver S).V}

variable (x) in
/-- The value of the composite from `x` to `y`. -/
def pbvec (y : (pieceQuiver S).V) : PieceAlg k S := compVal ⟨x, y, gval x y⟩

include hpar in
lemma pmk_word_eq_bvec {y : (pieceQuiver S).V} {l : List (pieceQuiver S).A}
    (h : PathFrom x l y) : pmk (k := k) (word k (pieceQuiver S) l) = pbvec (k := k) x y := by
  rw [pmk, mk_word_eq_compVal l x y h, pbvec, gval_eq hpar h]

include hpar in
lemma bvec_ne_zero {y : (pieceQuiver S).V} (hy : y ≠ x) (h : gval x y ≠ 0) :
    pbvec (k := k) x y ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_path_of_gval h
  have hne : l ≠ [] := by
    rintro rfl
    exact hy (show x = y from hl).symm
  rw [← pmk_word_eq_bvec hpar hl]
  exact pmk_word_ne_zero hpar hne hl (by rwa [← gval_eq hpar hl])

include hpar in
lemma bvec_eq_zero {y : (pieceQuiver S).V} (h : gval x y = 0) : pbvec (k := k) x y = 0 := by
  by_cases hp : ∃ l, PathFrom x l y
  · obtain ⟨l, hl⟩ := hp
    rw [← pmk_word_eq_bvec hpar hl]
    exact mk_rel_zero (Or.inl ⟨l, x, y, hl, by rw [← gval_eq hpar hl, h], rfl⟩)
  · unfold pbvec compVal
    rw [dif_neg]
    rintro ⟨l, hl, -⟩
    exact hp ⟨l, hl⟩

variable (x) in
/-- `y` is reached from `z` by a path with nonzero composite from `x`. -/
def Ext (z y : (pieceQuiver S).V) : Prop :=
  ∃ w, ∃ h : PathFrom z w y, gval x z ≫ compD S w z y h ≠ 0

include hpar in
lemma gval_append {z y : (pieceQuiver S).V} {l w : List (pieceQuiver S).A} (hl : PathFrom x l z)
    (hw : PathFrom z w y) : gval x y = gval x z ≫ compD S w z y hw := by
  rw [gval_eq hpar (pathFrom_append l w hl hw), compD_append l w hl hw, gval_eq hpar hl]

include hpar in
/-- **Corners against a basis element.** -/
lemma corner_pbvec {z : (pieceQuiver S).V} (hz : z ≠ x) (a : PieceAlg k S)
    (y : (pieceQuiver S).V) :
    pev (k := k) y * a * pbvec x z ∈ Submodule.span k {r | Ext x z y ∧ r = pbvec (k := k) x y} := by
  classical
  by_cases hgz : gval x z = 0
  · rw [bvec_eq_zero hpar hgz, mul_zero]; exact Submodule.zero_mem _
  obtain ⟨l, hl⟩ := exists_path_of_gval hgz
  have hlne : l ≠ [] := by
    rintro rfl
    exact hz (show x = z from hl).symm
  have hbz : pbvec (k := k) x z = pmk (word k (pieceQuiver S) l) := (pmk_word_eq_bvec hpar hl).symm
  have hez : pev (k := k) z * pbvec x z = pbvec x z := by
    rw [hbz, ← map_mul]
    congr 1
    rw [vertex_mul_word_path k hlne hl z, if_pos rfl]
  have h1 : pev (k := k) y * a * pbvec x z = (pev y * a * pev z) * pbvec x z := by
    rw [mul_assoc (pev y * a), hez]
  rw [h1]
  have hmap := Submodule.mem_map_of_mem (f := LinearMap.mulRight k (pbvec (k := k) x z))
    (corner_piece a z y)
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.2 ?_) hmap
  rintro _ ⟨_, ⟨r, (⟨rfl, rfl⟩ | ⟨w, hw, hpw, rfl⟩), rfl⟩, rfl⟩
  · refine Submodule.subset_span ⟨⟨[], rfl, ?_⟩, ?_⟩
    · change gval x z ≫ eqToHom rfl ≠ 0
      rwa [eqToHom_refl, Category.comp_id]
    · exact hez
  · have hval : pmk (k := k) (word k (pieceQuiver S) w) * pbvec x z = pbvec x y := by
      rw [hbz, ← map_mul, ← word_append, pmk_word_eq_bvec hpar (pathFrom_append l w hl hpw)]
    change pmk (k := k) (word k (pieceQuiver S) w) * pbvec x z ∈ _
    rw [hval]
    by_cases hE : gval x z ≫ compD S w z y hpw = 0
    · have hgy : gval x y = 0 := by rw [gval_append hpar hl hpw, hE]
      have h0 : pbvec (k := k) x y = 0 := bvec_eq_zero hpar hgy
      nth_rw 2 [h0]
      exact (Submodule.span k {r | Ext x z y ∧ r = pbvec (k := k) x y}).zero_mem
    · exact Submodule.subset_span (show Ext x z y ∧ pbvec (k := k) x y = pbvec x y from
        ⟨⟨w, hpw, hE⟩, rfl⟩)

variable (x) in
/-- The class relation on points other than `x`. -/
def ExtR (z y : (pieceQuiver S).V) : Prop := z ≠ x ∧ y ≠ x ∧ Ext x z y

variable (x) in
/-- Two points are in the same class. -/
def Cl (y z : (pieceQuiver S).V) : Prop := Relation.EqvGen (ExtR x) y z

include hpar in
/-- Corners of radical elements at `z ≠ x` are multiples of `b_z`. -/
lemma corner_rad {v : PieceAlg k S} (hv : v * pev x = v) {z : (pieceQuiver S).V} (hz : z ≠ x) :
    ∃ c : k, pev (k := k) z * v = c • pbvec x z := by
  have h := corner_piece v x z
  rw [mul_assoc, hv] at h
  have hsub : pmk (k := k) '' cornerSet k x z ⊆ {pbvec (k := k) x z} := by
    rintro _ ⟨r, (⟨h1, -⟩ | ⟨l, -, hl, rfl⟩), rfl⟩
    · exact absurd h1.symm hz
    · exact pmk_word_eq_bvec hpar hl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (Submodule.span_mono hsub h)
  exact ⟨c, hc.symm⟩

variable (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] →
  ¬PathFrom i l i)

include hpar hacyc in
lemma not_ext_to_x {z : (pieceQuiver S).V} (hz : z ≠ x) : ¬Ext x z x := by
  rintro ⟨w, hw, h0⟩
  have hgz : gval x z ≠ 0 := fun h ↦ h0 (by rw [h, Limits.zero_comp])
  obtain ⟨l, hl⟩ := exists_path_of_gval hgz
  have hlne : l ≠ [] := by rintro rfl; exact hz (show x = z from hl).symm
  exact hacyc x (l ++ w) (by simp [hlne]) (pathFrom_append l w hl hw)

include hpar hacyc in
/-- **Cross terms between classes vanish.** -/
lemma cross_zero {v : PieceAlg k S} (hv : v * pev x = v) (hvx : pev (k := k) x * v = 0)
    (a : PieceAlg k S) {y z : (pieceQuiver S).V} (hyz : ¬Cl x y z ∨ (y = x ∧ z ≠ x)) :
    pev (k := k) y * a * (pev z * v) = 0 := by
  by_cases hzx : z = x
  · subst hzx; rw [hvx, mul_zero]
  obtain ⟨c, hc⟩ := corner_rad hpar hv hzx
  rw [hc, mul_smul_comm]
  have h := corner_pbvec hpar hzx a y
  have hsub : {r | Ext x z y ∧ r = pbvec (k := k) x y} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hE
    rcases hyz with hyz | ⟨rfl, -⟩
    · by_cases hyx : y = x
      · subst hyx; exact absurd hE (not_ext_to_x hpar hacyc hzx)
      · exact absurd (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hzx, hyx, hE⟩)) hyz
    · exact absurd hE (not_ext_to_x hpar hacyc hzx)
  rw [hsub, Submodule.span_empty, Submodule.mem_bot] at h
  rw [h, smul_zero]

include hpar hacyc in
/-- **Summing over a class commutes with the algebra action on the radical.** -/
lemma classSum_smul {v : PieceAlg k S} (hv : v * pev x = v) (hvx : pev (k := k) x * v = 0)
    (F : Finset (pieceQuiver S).V) (hxF : x ∉ F)
    (hF : ∀ y z, y ∈ F → (z ∈ F ↔ Cl x y z)) (a : PieceAlg k S) :
    ∑ y ∈ F, pev (k := k) y * (a * v) = a * ∑ y ∈ F, pev y * v := by
  classical
  have hv1 : v = ∑ z, pev (k := k) z * v := by rw [← Finset.sum_mul, sum_ev, one_mul]
  have hT : ∀ y z, y ∈ F → z ∉ F → pev (k := k) y * a * (pev z * v) = 0 := fun y z hy hz ↦
    cross_zero hpar hacyc hv hvx a (Or.inl fun h ↦ hz ((hF y z hy).2 h))
  have hT' : ∀ y z, z ∈ F → y ∉ F → pev (k := k) y * a * (pev z * v) = 0 := fun y z hz hy ↦ by
    by_cases hyx : y = x
    · exact cross_zero hpar hacyc hv hvx a (Or.inr ⟨hyx, fun h ↦ hxF (h ▸ hz)⟩)
    · exact cross_zero hpar hacyc hv hvx a (Or.inl fun h ↦ hy ((hF z y hz).2
        (Relation.EqvGen.symm _ _ h)))
  calc ∑ y ∈ F, pev (k := k) y * (a * v)
      = ∑ y ∈ F, ∑ z ∈ F, pev (k := k) y * a * (pev z * v) := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        conv_lhs => rw [hv1, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_subset (Finset.subset_univ F) fun z _ hz ↦ ?_]
        · exact Finset.sum_congr rfl fun z _ ↦ by rw [mul_assoc]
        · rw [← mul_assoc]; exact hT y z hy hz
    _ = ∑ z ∈ F, ∑ y ∈ F, pev (k := k) y * a * (pev z * v) := Finset.sum_comm
    _ = a * ∑ y ∈ F, pev y * v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz ↦ ?_
        conv_rhs => rw [← one_mul (a * (pev z * v)), ← sum_ev (k := k) (S := S), Finset.sum_mul]
        rw [← Finset.sum_subset (Finset.subset_univ F) fun y _ hy ↦ ?_]
        · exact Finset.sum_congr rfl fun y _ ↦ by rw [mul_assoc]
        · rw [← mul_assoc]; exact hT' y z hz hy

omit [Fintype P] [DecidableEq P] in
lemma cl_symm {y z : (pieceQuiver S).V} (h : Cl x y z) : Cl x z y := Relation.EqvGen.symm _ _ h

omit [Fintype P] [DecidableEq P] in
lemma cl_trans {y z w : (pieceQuiver S).V} (h : Cl x y z) (h' : Cl x z w) : Cl x y w :=
  Relation.EqvGen.trans _ _ _ h h'

/-- The points other than `x` reached with nonzero composite. -/
def RPt (x y : (pieceQuiver S).V) : Prop := y ≠ x ∧ gval x y ≠ 0

include hpar in
lemma rpt_of_extR {a b : (pieceQuiver S).V} (h : ExtR x a b) : RPt x a ∧ RPt x b := by
  obtain ⟨hax, hbx, w, hw, h0⟩ := h
  have hga : gval x a ≠ 0 := fun h ↦ h0 (by rw [h, Limits.zero_comp])
  refine ⟨⟨hax, hga⟩, hbx, fun hb ↦ h0 ?_⟩
  obtain ⟨l, hl⟩ := exists_path_of_gval hga
  rw [← gval_append hpar hl hw, hb]

include hpar in
lemma rpt_iff_of_cl {y z : (pieceQuiver S).V} (h : Cl x y z) : RPt x y ↔ RPt x z := by
  induction h with
  | rel a b hab => exact ⟨fun _ ↦ (rpt_of_extR hpar hab).2, fun _ ↦ (rpt_of_extR hpar hab).1⟩
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

omit [Fintype P] [DecidableEq P] in
lemma ne_x_of_cl {y z : (pieceQuiver S).V} (h : Cl x y z) (hy : y ≠ x) : z ≠ x := by
  have key : ∀ a b, Cl x a b → (a = x ↔ b = x) := by
    intro a b h
    induction h with
    | rel a b hab => exact ⟨fun h ↦ absurd h hab.1, fun h ↦ absurd h hab.2.1⟩
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact fun hz ↦ hy ((key y z h).2 hz)

end LargeIndecomposable.RayCat
