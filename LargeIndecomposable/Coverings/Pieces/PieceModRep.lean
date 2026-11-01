module

public import LargeIndecomposable.Coverings.Pieces.PieceAlgebra

/-!
# Modules over the piece algebra are representations

For a finite-dimensional module `M` over the piece algebra, the spaces `e_i M` with the arrows
acting form a representation of the piece (`repOf`), the total space is `M` again (`totEquiv`,
compatible with the arrows), and the representation respects the cover (`respectsCover_repOf`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- The vertex idempotent in the piece algebra. -/
abbrev pev (v : (pieceQuiver S).V) : PieceAlg k S :=
  RingQuot.mkAlgHom k _ (FinQuiver.vertex k (pieceQuiver S) v)

/-- An arrow in the piece algebra. -/
abbrev ea (α : (pieceQuiver S).A) : PieceAlg k S :=
  RingQuot.mkAlgHom k _ (FinQuiver.arrow k (pieceQuiver S) α)

lemma ev_mul_ev (v w : (pieceQuiver S).V) :
    pev (k := k) v * pev w = if v = w then pev v else 0 := by
  rw [← map_mul, FinQuiver.vertex_mul_vertex]
  split_ifs <;> simp

lemma sum_ev : ∑ v, pev (k := k) (S := S) v = 1 := by
  rw [← map_sum, FinQuiver.sum_vertex, map_one]

lemma ea_mul_ev (α : (pieceQuiver S).A) (v : (pieceQuiver S).V) :
    ea (k := k) α * pev v = if v = (pieceQuiver S).src α then ea α else 0 := by
  rw [← map_mul, FinQuiver.arrow_mul_vertex]
  split_ifs <;> simp

lemma ev_tgt_mul_ea (α : (pieceQuiver S).A) :
    pev (k := k) ((pieceQuiver S).tgt α) * ea α = ea α := by
  rw [← map_mul, FinQuiver.tgt_mul_arrow]

variable (M : AR.FDMod k (PieceAlg k S))

include M

/-- Multiplication by an element of the piece algebra, as a `k`-linear map. -/
def actK (a : PieceAlg k S) : M →ₗ[k] M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := by
    rw [RingHom.id_apply]
    exact (smul_algebra_smul_comm c a m)

lemma ea_mem (α : (pieceQuiver S).A) (m : M) :
    ea (k := k) α • m ∈ LinearMap.range (actK M (pev ((pieceQuiver S).tgt α))) :=
  ⟨ea α • m, by
    change pev (k := k) ((pieceQuiver S).tgt α) • (ea (k := k) α • m) = ea α • m
    rw [← mul_smul, ev_tgt_mul_ea]⟩

/-- The representation `i ↦ e_i M`. -/
def repOf : Rep k (pieceQuiver S) where
  obj i := ModuleCat.of k (LinearMap.range (actK M (pev i)))
  map α := ModuleCat.ofHom (LinearMap.codRestrict _
    ((actK M (ea α)).comp (LinearMap.range (actK M (pev ((pieceQuiver S).src α)))).subtype)
    fun m ↦ ea_mem M α (m : M))

/-- The element of `M` underlying an element of `e_i M`. -/
def val {i : (pieceQuiver S).V} (m : (repOf M).obj i) : M :=
  ((show LinearMap.range (actK M (pev (k := k) i)) from m) : M)

lemma val_add {i : (pieceQuiver S).V} (m m' : (repOf M).obj i) :
    val M (m + m') = val M m + val M m' := rfl

lemma val_smul {i : (pieceQuiver S).V} (c : k) (m : (repOf M).obj i) :
    val M (c • m) = c • val M m := rfl

lemma val_zero {i : (pieceQuiver S).V} : val M (0 : (repOf M).obj i) = 0 := rfl

lemma val_injective {i : (pieceQuiver S).V} : Function.Injective (val M (i := i)) :=
  fun _ _ h ↦ Subtype.ext h

lemma ev_smul_val {i : (pieceQuiver S).V} (m : (repOf M).obj i) :
    pev (k := k) i • val M m = val M m := by
  obtain ⟨_, ⟨y, rfl⟩⟩ := (show LinearMap.range (actK M (pev (k := k) i)) from m)
  change pev (k := k) i • (pev (k := k) i • y) = pev (k := k) i • y
  rw [← mul_smul, ev_mul_ev, if_pos rfl]

lemma val_map (α : (pieceQuiver S).A) (m : (repOf M).obj ((pieceQuiver S).src α)) :
    val M (((repOf M).map α).hom m) = ea (k := k) α • val M m := rfl

/-- The total space to `M`. -/
def totToMod : (repOf M).Tot →ₗ[k] M where
  toFun x := ∑ i : (pieceQuiver S).V, val M (x i)
  map_add' x y := by simp only [Pi.add_apply, val_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, val_smul, Finset.smul_sum, RingHom.id_apply]

/-- `M` to the total space. -/
def modToTot : M →ₗ[k] (repOf M).Tot :=
  LinearMap.pi fun i ↦ (actK M (pev (k := k) i)).rangeRestrict

lemma val_modToTot (m : M) (i : (pieceQuiver S).V) : val M (modToTot M m i) = pev (k := k) i • m :=
  rfl

lemma totToMod_modToTot (m : M) : totToMod M (modToTot M m) = m := by
  change ∑ i : (pieceQuiver S).V, val M (modToTot M m i) = m
  simp only [val_modToTot]
  rw [← Finset.sum_smul, sum_ev, one_smul]

lemma modToTot_totToMod (x : (repOf M).Tot) : modToTot M (totToMod M x) = x := by
  funext i
  apply val_injective M
  rw [val_modToTot]
  change pev (k := k) i • ∑ j : (pieceQuiver S).V, val M (x j) = val M (x i)
  rw [Finset.smul_sum, Finset.sum_eq_single i]
  · exact ev_smul_val M (x i)
  · intro j _ hji
    rw [← ev_smul_val M (x j), ← mul_smul, ev_mul_ev, if_neg (Ne.symm hji), zero_smul]
  · simp

/-- **The total space of `repOf M` is `M`.** -/
def totEquiv : (repOf M).Tot ≃ₗ[k] M :=
  LinearEquiv.ofLinear (totToMod M) (modToTot M) (LinearMap.ext (totToMod_modToTot M))
    (LinearMap.ext (modToTot_totToMod M))

lemma totToMod_arrOp (α : (pieceQuiver S).A) (x : (repOf M).Tot) :
    totToMod M ((repOf M).arrOp α x) = ea (k := k) α • totToMod M x := by
  change ∑ i : (pieceQuiver S).V, val M ((repOf M).arrOp α x i) =
    ea (k := k) α • ∑ j : (pieceQuiver S).V, val M (x j)
  rw [Finset.smul_sum, Finset.sum_eq_single ((pieceQuiver S).tgt α),
    Finset.sum_eq_single ((pieceQuiver S).src α)]
  · rw [Rep.arrOp_apply, Pi.single_eq_same, val_map]
  · intro j _ hj
    rw [← ev_smul_val M (x j), ← mul_smul, ea_mul_ev, if_neg hj, zero_smul]
  · simp
  · intro j _ hj
    rw [Rep.arrOp_apply, Pi.single_eq_of_ne hj, val_zero]
  · simp

lemma totToMod_pathTot : ∀ (l : List (pieceQuiver S).A) (x : (repOf M).Tot),
    totToMod M ((repOf M).pathTot l x) =
      (RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)
        (FinQuiver.word k (pieceQuiver S) l)) • totToMod M x
  | [], x => by
    change totToMod M x = (RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦
      a ∈ relGens k S ∧ b = 0) (1 : (pieceQuiver S).PathAlgebra k)) • totToMod M x
    rw [map_one, one_smul]
  | c :: l, x => by
    change totToMod M ((repOf M).pathTot l ((repOf M).arrOp c x)) =
      (RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)
        (FinQuiver.word k (pieceQuiver S) l * FinQuiver.arrow k _ c)) • totToMod M x
    rw [totToMod_pathTot l, totToMod_arrOp, ← mul_smul, map_mul]

/-- **The representation of a piece-algebra module respects the cover.** -/
theorem respectsCover_repOf : RespectsCover (repOf M) := by
  have hinj : Function.Injective (totToMod M) := (totEquiv M).injective
  refine ⟨fun le i j h h0 ↦ LinearMap.ext fun x ↦ hinj ?_,
    fun le le' i j h h' he ↦ LinearMap.ext fun x ↦ hinj ?_⟩
  · rw [totToMod_pathTot, mk_rel_zero (Or.inl ⟨le, i, j, h, h0, rfl⟩), zero_smul]
    exact (map_zero (totToMod M)).symm
  · rw [totToMod_pathTot, totToMod_pathTot]
    have := mk_rel_zero (k := k) (S := S) (Or.inr ⟨le, le', i, j, h, h', he, rfl⟩)
    rw [map_sub, sub_eq_zero] at this
    rw [this]

end LargeIndecomposable.RayCat
