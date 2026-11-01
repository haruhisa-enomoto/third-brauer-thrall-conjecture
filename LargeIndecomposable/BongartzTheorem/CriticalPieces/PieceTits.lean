module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceRigid
public import LargeIndecomposable.DirectedAlgebras.Directing.DimVector
public import LargeIndecomposable.Coverings.Pieces.PieceRepDir

/-!
# The Tits form of a representation-directed piece is weakly positive

Let `F` be a family of relations generating those of a piece `S`, with Tits form
`q_F(x) = Σᵢ xᵢ² - Σ_α x_{s α} x_{t α} + Σ_r x_{s r} x_{t r}`. If every nonzero indecomposable
module over the piece algebra is rigid (for instance directing), then every dimension vector
`x` has a representation `X` respecting the cover with no cocycles beyond coboundaries
(`exists_rigid_rep`; a module of minimal endomorphism dimension, ASS IX.3.3). Counting cocycles
gives `dim End X ≤ q_F(x)` (`finrank_end_le_titsF`). So `q_F` is weakly positive
(`one_le_titsF`), and a positive vector with `q_F(x) ≤ 1` is the dimension vector of a brick
(`exists_brick_of_titsF`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-! ### Paths of a piece with their lengths -/

lemma cover_of_piece_path_len : ∀ (le : List (pieceQuiver S).A) {i j : (pieceQuiver S).V}
    (h : PathFrom i le j), ∃ p : Quiver.Path (RayVert.mk (pt S i)) (RayVert.mk (pt S j)),
      p.length = le.length ∧ pathVal p = compD S le i j h
  | [], i, j, h => by
    change i = j at h
    subst h
    exact ⟨Quiver.Path.nil, rfl, rfl⟩
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    obtain ⟨p, hpl, hp⟩ := cover_of_piece_path_len le h2
    let a : RayVert.mk (pt S e.1) ⟶ RayVert.mk (pt S e.2.1) := ⟨e.2.2.1, e.2.2.2⟩
    refine ⟨(Quiver.Path.nil.cons a).comp p, ?_, ?_⟩
    · erw [Quiver.Path.length_comp, hpl]
      simp only [Quiver.Path.length_cons, Quiver.Path.length_nil, List.length_cons]
      omega
    · erw [pathVal_comp, hp]
      change (𝟙 _ ≫ e.2.2.1) ≫ compD S le _ j h2 = eqToHom rfl ≫ e.2.2.1 ≫ compD S le _ j h2
      simp

/-- A nonempty path of a piece never has the value of the empty path. -/
lemma compD_nil_ne (le : List (pieceQuiver S).A) (hle : le ≠ []) {i j : (pieceQuiver S).V}
    (h : PathFrom i ([] : List (pieceQuiver S).A) j) (h' : PathFrom i le j) :
    compD S [] i j h ≠ compD S le i j h' := by
  change i = j at h
  subst h
  obtain ⟨p, hpl, hp⟩ := cover_of_piece_path_len le h'
  intro heq
  apply pathVal_ne_id_of_length p (by rw [hpl]; exact List.length_pos_of_ne_nil hle)
  rw [hp, ← heq]
  rfl

/-! ### Representations with zero maps -/

variable (k S) in
/-- The representation with spaces `k^{x i}` and zero maps. -/
def zeroRep (x : (pieceQuiver S).V → ℕ) : Rep k (pieceQuiver S) where
  obj i := ModuleCat.of k (Fin (x i) → k)
  map _ := 0

lemma pathTot_zeroRep (x : (pieceQuiver S).V → ℕ) :
    ∀ le : List (pieceQuiver S).A, le ≠ [] → (zeroRep k S x).pathTot le = 0
  | [], h => absurd rfl h
  | e :: le, _ => by
    change (zeroRep k S x).pathTot le ∘ₗ (zeroRep k S x).arrOp e = 0
    have : (zeroRep k S x).arrOp e = 0 := LinearMap.ext fun w ↦ by
      rw [Rep.arrOp_apply]
      exact Pi.single_zero _
    rw [this, LinearMap.comp_zero]

lemma respectsCover_zeroRep (x : (pieceQuiver S).V → ℕ) : RespectsCover (zeroRep k S x) := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rcases le with _ | ⟨e, le⟩
    · exfalso
      change i = j at h
      subst h
      exact IsRayCategory.id_ne_zero (pt S i) h0
    · exact pathTot_zeroRep x _ (List.cons_ne_nil _ _)
  · rcases le with _ | ⟨e, le⟩ <;> rcases le' with _ | ⟨e', le'⟩
    · rfl
    · exact absurd he (compD_nil_ne _ (List.cons_ne_nil _ _) h h')
    · exact absurd he.symm (compD_nil_ne _ (List.cons_ne_nil _ _) h' h)
    · rw [pathTot_zeroRep x _ (List.cons_ne_nil _ _), pathTot_zeroRep x _ (List.cons_ne_nil _ _)]

instance (x : (pieceQuiver S).V → ℕ) (i : (pieceQuiver S).V) :
    FiniteDimensional k ((zeroRep k S x).obj i) :=
  inferInstanceAs (FiniteDimensional k (Fin (x i) → k))

/-! ### Dimension vectors -/

lemma pev_idem (v : (pieceQuiver S).V) : IsIdempotentElem (pev (k := k) (S := S) v) := by
  unfold IsIdempotentElem
  rw [ev_mul_ev, if_pos rfl]

lemma pieceAct_pev (X : Rep k (pieceQuiver S)) (hX : RespectsCover X) (v : (pieceQuiver S).V) :
    pieceAct X hX (pev v) = X.idm v := by
  rw [pieceAct_mk]
  exact Ext.act_vertex X v

/-- The `v`-piece of the module of a representation is `X(v)`. -/
def eSubEquiv (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] (v : (pieceQuiver S).V) :
    AR.eSub (toFDMod X hX) (pev v) ≃ₗ[k] X.obj v where
  toFun w := (show X.Tot from w.1) v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨show toFDMod X hX from (show X.Tot from Pi.single v y), by
    change pieceAct X hX (pev v) (Pi.single v y) = Pi.single v y
    rw [pieceAct_pev, Rep.idm_apply, Pi.single_eq_same]⟩
  left_inv w := by
    apply Subtype.ext
    have hw : pieceAct X hX (pev v) (show X.Tot from w.1) = w.1 := w.2
    rw [pieceAct_pev, Rep.idm_apply] at hw
    exact hw
  right_inv y := by
    change (Pi.single v y : X.Tot) v = y
    exact Pi.single_eq_same _ _

lemma dimv_toFDMod (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] (v : (pieceQuiver S).V) :
    AR.dimv pev (toFDMod X hX) v = finrank k (X.obj v) :=
  (eSubEquiv X hX v).finrank_eq

lemma dimv_eq_finrank_repOf (M : AR.FDMod k (PieceAlg k S)) (v : (pieceQuiver S).V) :
    AR.dimv pev M v = finrank k ((repOf M).obj v) := by
  have heq : LinearMap.range (actK M (pev (k := k) v)) = AR.eSub M (pev v) := by
    ext m
    constructor
    · rintro ⟨m', rfl⟩
      change pev (k := k) v • pev (k := k) v • m' = pev (k := k) v • m'
      rw [← mul_smul, (pev_idem v).eq]
    · intro hm
      exact ⟨m, hm⟩
  change finrank k (AR.eSub M (pev (k := k) v)) =
    finrank k (LinearMap.range (actK M (pev (k := k) v)))
  rw [heq]

/-- **A module is the module of its representation.** -/
def repOfEquivA (M : AR.FDMod k (PieceAlg k S)) :
    PieceMod (repOf M) (respectsCover_repOf M) ≃ₗ[PieceAlg k S] M where
  toFun := totToMod M
  map_add' := map_add (totToMod M)
  map_smul' a x := by
    obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective k _ a
    change totToMod M (pieceAct (repOf M) _ (RingQuot.mkAlgHom k _ z) x) = _
    rw [pieceAct_mk]
    exact totToMod_pdAct M z x
  invFun := modToTot M
  left_inv := modToTot_totToMod M
  right_inv := totToMod_modToTot M

/-- Vanishing of extensions is invariant under isomorphism. -/
lemma _root_.LargeIndecomposable.AR.ExtVanish.congr {A : Type u} [Ring A] [Algebra k A]
    {X X' Y Y' : AR.FDMod k A} (eX : X ≃ₗ[A] X') (eY : Y ≃ₗ[A] Y') (h : AR.ExtVanish X Y) :
    AR.ExtVanish X' Y' := by
  intro E i p hi hp hex
  have hex' : LinearMap.range (i ∘ₗ eY.toLinearMap) =
      LinearMap.ker (eX.symm.toLinearMap ∘ₗ p) := by
    ext e
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply,
        AR.mem_ker_of_range hex, map_zero]
    · intro he
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff] at he
      have : e ∈ LinearMap.range i := by rw [hex]; exact he
      obtain ⟨y, rfl⟩ := this
      exact ⟨eY.symm y, by simp⟩
  obtain ⟨s, hs⟩ := h E (i ∘ₗ eY.toLinearMap) (eX.symm.toLinearMap ∘ₗ p)
    (hi.comp eY.injective) (eX.symm.surjective.comp hp) hex'
  refine ⟨s ∘ₗ eX.symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  have := LinearMap.congr_fun hs (eX.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this ⊢
  exact eX.symm.injective this

/-! ### Rigid representations -/

/-- **Every dimension vector has a rigid representation** when indecomposables are rigid. -/
theorem exists_rigid_rep (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (hrig : ∀ M : AR.FDMod k (PieceAlg k S), AR.IsIndecMod (PieceAlg k S) M → Nontrivial M →
      AR.ExtVanish M M)
    (x : (pieceQuiver S).V → ℕ) :
    ∃ (X : Rep k (pieceQuiver S)) (hX : RespectsCover X) (_ : ∀ i, FiniteDimensional k (X.obj i)),
      (∀ i, finrank k (X.obj i) = x i) ∧
        Ext.cocycles F (X := X) (Y := X) ≤ LinearMap.range (Ext.cobL (X := X) (Y := X)) := by
  classical
  have hex : ∃ n, ∃ W : AR.FDMod k (PieceAlg k S),
      (fun v ↦ AR.dimv pev W v) = x ∧ finrank k (W →ₗ[PieceAlg k S] W) = n := by
    refine ⟨_, toFDMod (zeroRep k S x) (respectsCover_zeroRep x), funext fun v ↦ ?_, rfl⟩
    rw [dimv_toFDMod]
    exact Module.finrank_fin_fun k
  obtain ⟨W, hW, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W' : AR.FDMod k (PieceAlg k S),
      (fun v ↦ AR.dimv pev W' v) = (fun v ↦ AR.dimv pev W v) →
        finrank k (W →ₗ[PieceAlg k S] W) ≤ finrank k (W' →ₗ[PieceAlg k S] W') := by
    intro W' h
    rw [hWn]
    exact Nat.find_min' hex ⟨W', h.trans hW, rfl⟩
  have hv := AR.extVanish_of_minEnd (fun M ↦ fun v ↦ AR.dimv pev M v)
    (fun L M N f g hf hg hex ↦ funext fun v ↦ AR.dimv_exact pev pev_idem f g hf hg hex v)
    hrig W hmin
  refine ⟨repOf W, respectsCover_repOf W, fun i ↦ inferInstance, fun i ↦ ?_,
    cocycles_le_range_cob F hF hgen _ _ (hv.congr (repOfEquivA W).symm (repOfEquivA W).symm)⟩
  rw [← dimv_eq_finrank_repOf]
  exact congrFun hW i

/-! ### The Tits form -/

/-- **The Tits form** of a family of relations. -/
def titsF (F : Ext.RelFam (pieceQuiver S) k) (x : (pieceQuiver S).V → ℤ) : ℤ :=
  ∑ i, x i * x i - ∑ α, x ((pieceQuiver S).src α) * x ((pieceQuiver S).tgt α) +
    ∑ r, x (F.s r) * x (F.t r)

section IdFam

variable {D : FinQuiver} (X : Rep k D)

lemma idFam_mem : (fun j ↦ (LinearMap.id : X.obj j →ₗ[k] X.obj j)) ∈
    LinearMap.ker (Ext.cobL (X := X) (Y := X)) := by
  rw [LinearMap.mem_ker]
  funext α
  change LinearMap.id ∘ₗ (X.map α).hom - (X.map α).hom ∘ₗ LinearMap.id = 0
  rw [LinearMap.id_comp, LinearMap.comp_id, sub_self]

lemma idFam_ne {i : D.V} (hi : Nontrivial (X.obj i)) :
    (⟨_, idFam_mem X⟩ : LinearMap.ker (Ext.cobL (X := X) (Y := X))) ≠ 0 := by
  intro h
  have h1 := congrFun (congrArg Subtype.val h) i
  obtain ⟨y, hy⟩ := exists_ne (0 : X.obj i)
  exact hy (LinearMap.congr_fun h1 y)

lemma fam_mem (f : X ⟶ X) : (fun j ↦ (f.app j).hom) ∈
    LinearMap.ker (Ext.cobL (X := X) (Y := X)) := by
  rw [LinearMap.mem_ker]
  funext α
  change (f.app (D.tgt α)).hom ∘ₗ (X.map α).hom - (X.map α).hom ∘ₗ (f.app (D.src α)).hom = 0
  have := congrArg ModuleCat.Hom.hom (f.comm α)
  simp only [ModuleCat.hom_comp] at this
  rw [this, sub_self]

end IdFam

section Tits

variable (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (hrig : ∀ M : AR.FDMod k (PieceAlg k S), AR.IsIndecMod (PieceAlg k S) M → Nontrivial M →
      AR.ExtVanish M M)
include hF hgen hrig

/-- **Endomorphisms are bounded by the Tits form.** -/
theorem exists_rep_titsF (x : (pieceQuiver S).V → ℕ) :
    ∃ (X : Rep k (pieceQuiver S)) (_ : RespectsCover X) (_ : ∀ i, FiniteDimensional k (X.obj i)),
      (∀ i, finrank k (X.obj i) = x i) ∧
        (finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := X))) : ℤ) ≤
          titsF F (fun i ↦ (x i : ℤ)) := by
  obtain ⟨X, hX, hfin, hdim, hcoc⟩ := exists_rigid_rep F hF hgen hrig x
  refine ⟨X, hX, hfin, hdim, ?_⟩
  have hR : ∀ r, Ext.act X (F.ρ r) = 0 := fun r ↦ act_eq_zero_of_mem_span hX _ (hF r)
  have h := Ext.finrank_ker_cob_le F hR hR hcoc
  simp only [hdim] at h
  have h' : ((finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := X))) +
      ∑ α, x ((pieceQuiver S).src α) * x ((pieceQuiver S).tgt α) : ℕ) : ℤ) ≤
      ((∑ i, x i * x i + ∑ r, x (F.s r) * x (F.t r) : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  unfold titsF
  linarith

/-- **The Tits form of a piece with rigid indecomposables is weakly positive.** -/
theorem one_le_titsF (x : (pieceQuiver S).V → ℕ) (hx : x ≠ 0) :
    1 ≤ titsF F (fun i ↦ (x i : ℤ)) := by
  obtain ⟨X, hX, hfin, hdim, hle⟩ := exists_rep_titsF F hF hgen hrig x
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hnt : Nontrivial (X.obj i) := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hpos : 0 < finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := X))) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, idFam_ne X hnt⟩
  omega

/-- **Positive vectors with Tits form at most one are dimension vectors of bricks.** -/
theorem exists_brick_of_titsF (x : (pieceQuiver S).V → ℕ) (hx : x ≠ 0)
    (hq : titsF F (fun i ↦ (x i : ℤ)) ≤ 1) :
    ∃ (X : Rep k (pieceQuiver S)) (_ : RespectsCover X) (_ : ∀ i, FiniteDimensional k (X.obj i)),
      (∀ i, finrank k (X.obj i) = x i) ∧
        ∀ f : X ⟶ X, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id := by
  obtain ⟨X, hX, hfin, hdim, hle⟩ := exists_rep_titsF F hF hgen hrig x
  refine ⟨X, hX, hfin, hdim, fun f ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hnt : Nontrivial (X.obj i) := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hpos : 0 < finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := X))) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, idFam_ne X hnt⟩
  have h1 : finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := X))) = 1 := by omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ (idFam_ne X hnt)).1 h1 ⟨_, fam_mem X f⟩
  refine ⟨c, fun j ↦ ?_⟩
  have := congrFun (congrArg Subtype.val hc) j
  exact this.symm

end Tits

end LargeIndecomposable.RayCat
