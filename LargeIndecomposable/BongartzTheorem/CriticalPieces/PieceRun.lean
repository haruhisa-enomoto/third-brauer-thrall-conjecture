module

public import LargeIndecomposable.BongartzTheorem.ContourExclusion.ContourPiece
public import LargeIndecomposable.DirectedAlgebras.Sincere.FarSummand
public import LargeIndecomposable.RayCategories.Basic.MorphismDepth
public import LargeIndecomposable.BongartzTheorem.LongLines.LineContour

/-!
# Bounds on pieces

Paths of nonzero value in a finite ray category have bounded length (`exists_length_bound`). So
chains in a piece of the cover and in its quotients are bounded (`runB_piece`, `runB_quot`), and
the underlying graphs have bounded degree (`card_adj_le`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical Statement

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P]

/-- **Paths of nonzero value have bounded length.** -/
theorem exists_length_bound : ∃ N, ∀ (x y : P) (l : List (quiver P).A)
    (h : PathFrom (D := quiver P) x l y), pathMor l x y h ≠ 0 → l.length < N := by
  haveI : ∀ a b : P, Finite (a ⟶ b) := IsRayCategory.finite_hom
  letI : Fintype (Σ x y : P, x ⟶ y) := Fintype.ofFinite _
  let B : ℕ := Finset.univ.sup fun p : Σ x y : P, x ⟶ y ↦ depth p.2.2
  have hB : ∀ (x y : P) (f : x ⟶ y), depth f ≤ B := fun x y f ↦
    Finset.le_sup (f := fun p : Σ x y : P, x ⟶ y ↦ depth p.2.2) (Finset.mem_univ ⟨x, y, f⟩)
  have key : ∀ (l : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y),
      pathMor l x y h ≠ 0 → l.length ≤ depth (pathMor l x y h) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ _ ↦ Nat.zero_le _
    | cons e l ih =>
      intro x y h h0
      obtain ⟨a, b, f, hf⟩ := e
      obtain ⟨h1, h2⟩ := h
      change a = x at h1
      subst h1
      have e1 : pathMor (⟨a, b, f, hf⟩ :: l) a y ⟨rfl, h2⟩ = f ≫ pathMor l b y h2 := by
        change eqToHom rfl ≫ f ≫ pathMor l b y h2 = _
        simp
      rw [e1] at h0 ⊢
      have hg : pathMor l b y h2 ≠ 0 := fun h3 ↦ h0 (by rw [h3, comp_zero])
      have h3 := ih b y h2 hg
      have h4 := depth_lt_comp_left f (pathMor l b y h2) h0 hf.2.1
      change l.length + 1 ≤ _
      omega
  exact ⟨B + 1, fun x y l h h0 ↦ Nat.lt_succ_of_le ((key l x y h h0).trans (hB _ _ _))⟩

variable {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k] (hpar : ParEq S)
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)

include hpar in
/-- A nonzero chain of a piece has a long path. -/
lemma chain_path {x : ℕ → (pieceQuiver S).V} {c : ℕ → PieceAlg k S} {s t : ℕ} {w : PieceAlg k S}
    (h : AR.DirData.IsChain (pieceDirData (k := k) hacyc) x c s t w)
    (hne : ∀ i, s ≤ i → i < t → x i ≠ x (i + 1)) :
    pev (x t) * w * pev (x s) = 0 ∨ ∃ l, PathFrom (x s) l (x t) ∧ s ≤ t ∧ t - s ≤ l.length := by
  induction h with
  | refl => exact Or.inr ⟨[], rfl, le_rfl, by simp⟩
  | @step t w h ih =>
    have hst : s ≤ t := by
      clear hne ih
      induction h with
      | refl => exact le_rfl
      | step _ ih => omega
    rcases ih fun i h1 h2 ↦ hne i h1 (by omega) with h0 | ⟨l, hl, -, hlen⟩
    · left
      have e1 : pev (x (t + 1)) * (c t * pev (x t) * w) * pev (x s) =
          pev (x (t + 1)) * c t * (pev (x t) * w * pev (x s)) := by
        simp only [mul_assoc]
      change pev (x (t + 1)) * (c t * pev (x t) * w) * pev (x s) = 0
      rw [e1, h0, mul_zero]
    · by_cases h0 : pev (x (t + 1)) * c t * pev (x t) = 0
      · left
        have e1 : pev (x (t + 1)) * (c t * pev (x t) * w) * pev (x s) =
            (pev (x (t + 1)) * c t * pev (x t)) * w * pev (x s) := by
          simp only [mul_assoc]
        change pev (x (t + 1)) * (c t * pev (x t) * w) * pev (x s) = 0
        rw [e1, h0, zero_mul, zero_mul]
      · right
        obtain ⟨⟨l', hl'⟩, -⟩ := of_cn_ne_zero hpar hacyc
          (AR.DirData.cn_corner (D := pieceDirData (k := k) hacyc) (x (t + 1)) (x t) (c t)) h0
        have hl'0 : l' ≠ [] := by
          rintro rfl
          exact hne t hst (Nat.lt_succ_self t) hl'
        refine ⟨l ++ l', pathFrom_append l l' hl hl', by omega, ?_⟩
        have : 0 < l'.length := List.length_pos_iff.2 hl'0
        simp only [List.length_append]
        omega

include hpar in
/-- **Chains of pieces are bounded.** -/
theorem runB_piece {N : ℕ} (hN : ∀ (x y : P) (l : List (quiver P).A)
    (h : PathFrom (D := quiver P) x l y), pathMor l x y h ≠ 0 → l.length < N) :
    AR.DirData.RunB (pieceDirData (k := k) hacyc) N := by
  intro (x : ℕ → (pieceQuiver S).V) c s t w hne hlen hch
  rcases chain_path hpar hacyc hch hne with h0 | ⟨l, hl, -, hlen'⟩
  · exact h0
  · by_contra h0
    obtain ⟨-, hg⟩ := of_cn_ne_zero hpar hacyc
      (AR.DirData.cn_corner (D := pieceDirData (k := k) hacyc) (x t) (x s) w) h0
    have hv : Cover.val (gval (x s) (x t)) ≠ 0 := fun h3 ↦ hg ((val_eq_zero_iff _).1 h3)
    rw [gval_eq hpar hl, val_compD] at hv
    have := hN _ _ _ _ hv
    rw [List.length_map] at this
    omega


omit hpar in
lemma eq_of_out {a b b' : (pieceQuiver S).V} (h : gval a b ≠ 0) (h' : gval a b' ≠ 0)
    (he : (⟨(pt S b).y, Cover.val (gval a b)⟩ : Σ z, (pt S a).y ⟶ z) =
      ⟨(pt S b').y, Cover.val (gval a b')⟩) : b = b' := by
  have hkey : ∀ (g : pt S a ⟶ pt S b) (g' : pt S a ⟶ pt S b'), g ≠ 0 → g' ≠ 0 →
      (⟨(pt S b).y, Cover.val g⟩ : Σ z, (pt S a).y ⟶ z) = ⟨(pt S b').y, Cover.val g'⟩ →
      pt S b = pt S b' := by
    rintro (_ | f) (_ | f') h8 h9 h10
    · exact absurd rfl h8
    · exact absurd rfl h8
    · exact absurd rfl h9
    · obtain ⟨h11, h12⟩ := Sigma.mk.inj h10
      exact target_eq f f' h11 h12
  exact Subtype.ext (hkey _ _ h h' he)

omit hpar in
lemma eq_of_in {a b b' : (pieceQuiver S).V} (h : gval b a ≠ 0) (h' : gval b' a ≠ 0)
    (he : (⟨(pt S b).y, Cover.val (gval b a)⟩ : Σ z, z ⟶ (pt S a).y) =
      ⟨(pt S b').y, Cover.val (gval b' a)⟩) : b = b' := by
  have hkey : ∀ (g : pt S b ⟶ pt S a) (g' : pt S b' ⟶ pt S a), g ≠ 0 → g' ≠ 0 →
      (⟨(pt S b).y, Cover.val g⟩ : Σ z, z ⟶ (pt S a).y) = ⟨(pt S b').y, Cover.val g'⟩ →
      pt S b = pt S b' := by
    rintro (_ | f) (_ | f') h8 h9 h10
    · exact absurd rfl h8
    · exact absurd rfl h8
    · exact absurd rfl h9
    · obtain ⟨h11, h12⟩ := Sigma.mk.inj h10
      exact source_eq f f' h11 h12
  exact Subtype.ext (hkey _ _ h h' he)

/-- The number of nonzero morphisms is a bound for neighbours. -/
def morCard (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P] : ℕ :=
  haveI : ∀ a b : P, Finite (a ⟶ b) := IsRayCategory.finite_hom
  Nat.card (Σ x y : P, x ⟶ y)

omit hpar [DecidableEq P] in
lemma card_out_le {α : Type} (F : Finset α) (v : α → (pieceQuiver S).V) (hv : Set.InjOn v F)
    (a : (pieceQuiver S).V) (h : ∀ b ∈ F, gval a (v b) ≠ 0) : F.card ≤ morCard P := by
  haveI : ∀ a b : P, Finite (a ⟶ b) := IsRayCategory.finite_hom
  let g : α → Σ x y : P, x ⟶ y := fun b ↦ ⟨(pt S a).y, (pt S (v b)).y, Cover.val (gval a (v b))⟩
  have hinj : Set.InjOn g F := by
    intro b hb b' hb' he
    have h1 : (⟨(pt S (v b)).y, Cover.val (gval a (v b))⟩ : Σ z, (pt S a).y ⟶ z) =
        ⟨(pt S (v b')).y, Cover.val (gval a (v b'))⟩ := by
      have := (Sigma.mk.inj he).2
      exact eq_of_heq this
    exact hv hb hb' (eq_of_out (h b hb) (h b' hb') h1)
  let _ : Fintype (Σ x y : P, x ⟶ y) := Fintype.ofFinite _
  rw [morCard, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_univ _

omit [Fintype P] [DecidableEq P] [IsRayCategory P] in
lemma sig_inj {y₀ : P} {p q : Σ z, z ⟶ y₀}
    (h : (⟨p.1, y₀, p.2⟩ : Σ x y : P, x ⟶ y) = ⟨q.1, y₀, q.2⟩) : p = q := by
  obtain ⟨x, f⟩ := p
  obtain ⟨x', f'⟩ := q
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  change x = x' at h1
  subst h1
  obtain ⟨-, h4⟩ := Sigma.mk.inj (eq_of_heq h2)
  have h5 := eq_of_heq h4
  subst h5
  rfl

omit hpar [DecidableEq P] in
lemma card_in_le {α : Type} (F : Finset α) (v : α → (pieceQuiver S).V) (hv : Set.InjOn v F)
    (a : (pieceQuiver S).V) (h : ∀ b ∈ F, gval (v b) a ≠ 0) : F.card ≤ morCard P := by
  haveI : ∀ a b : P, Finite (a ⟶ b) := IsRayCategory.finite_hom
  let g : α → Σ x y : P, x ⟶ y := fun b ↦ ⟨(pt S (v b)).y, (pt S a).y, Cover.val (gval (v b) a)⟩
  have hinj : Set.InjOn g F := by
    intro b hb b' hb' he
    exact hv hb hb' (eq_of_in (h b hb) (h b' hb') (sig_inj he))
  let _ : Fintype (Σ x y : P, x ⟶ y) := Fintype.ofFinite _
  rw [morCard, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_univ _


section Killed

variable {B : Type u} [Ring B] [Algebra k B] (e : Linearization P k ≃ₐ[k] B)

/-- A module over `k(P)` as a `B`-module. -/
def modB (Z : AR.FDMod k (Linearization P k)) : AR.FDMod k B where
  carrier := Z
  isModule := Module.compHom _ e.symm.toRingHom
  isModuleK := inferInstance
  isScalarTower := by
    letI : Module B Z := Module.compHom _ e.symm.toRingHom
    exact ⟨fun c b m ↦ by
      change e.symm (c • b) • m = c • (e.symm b • m)
      rw [map_smul, smul_assoc]⟩
  isFD := inferInstance

lemma smul_modB (Z : AR.FDMod k (Linearization P k)) (b : B) (m : modB e Z) : b • m = (show Z from (e.symm b • (show Z from m))) := rfl

include e in
/-- **Modules killed by a nonzero element are bounded.** -/
theorem exists_bound_of_killed (hB : IsMinimalRepInfinite B) {b : Linearization P k} (hb : b ≠ 0) :
    ∃ K, ∀ Z : AR.FDMod k (Linearization P k), AR.IsIndecMod (Linearization P k) Z → Nontrivial Z →
      (∀ m : Z, b • m = 0) → finrank k Z ≤ K := by
  classical
  have hb' : e b ≠ 0 := fun h0 ↦ hb (e.injective (h0.trans (map_zero e).symm))
  let I : TwoSidedIdeal B := TwoSidedIdeal.span {e b}
  have hI : I ≠ ⊥ := by
    intro h0
    have : e b ∈ I := TwoSidedIdeal.subset_span rfl
    rw [h0] at this
    exact hb' this
  obtain ⟨n, X, hX⟩ := hB.2 I hI
  have hidx : ∀ Z : AR.FDMod k (Linearization P k), AR.IsIndecMod (Linearization P k) Z →
      Nontrivial Z → (∀ m : Z, b • m = 0) → ∃ i, Nonempty (modB e Z ≃ₗ[B]
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj (X i)) := by
    intro Z hZ hnt hk
    have hind : IsIndecomposable B (modB e Z) :=
      isIndecomposable_compHom e.symm.toRingEquiv (M := Z) ⟨hnt, hZ⟩
    haveI : Module.Finite B (modB e Z) := Module.Finite.of_restrictScalars_finite k B (modB e Z)
    refine exists_iso_of_isTorsion I X hX (modB e Z) hind ?_
    let Ann : TwoSidedIdeal B := TwoSidedIdeal.mk' {z | ∀ m : modB e Z, z • m = 0}
      (fun m ↦ zero_smul _ m) (fun ha hb' m ↦ by rw [add_smul, ha, hb', add_zero])
      (fun ha m ↦ by rw [neg_smul, ha, neg_zero]) (fun {z w} hw m ↦ by rw [mul_smul, hw, smul_zero])
      (fun {z w} hz m ↦ by rw [mul_smul, hz])
    have hbA : e b ∈ Ann := by
      refine (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).2 fun m ↦ ?_
      rw [smul_modB, AlgEquiv.symm_apply_apply]
      exact hk m
    have hle : I ≤ Ann := TwoSidedIdeal.span_le.2 (Set.singleton_subset_iff.2 hbA)
    intro z hzI m
    exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ z).1 (hle hzI) m
  let f : Fin n → ℕ := fun i ↦
    if h : ∃ Z : AR.FDMod k (Linearization P k), Nonempty (modB e Z ≃ₗ[B]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj (X i)) then
      finrank k h.choose else 0
  refine ⟨Finset.univ.sup f, fun Z hZ hnt hk ↦ ?_⟩
  obtain ⟨i, ⟨φ⟩⟩ := hidx Z hZ hnt hk
  have hex : ∃ Z : AR.FDMod k (Linearization P k), Nonempty (modB e Z ≃ₗ[B]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj (X i)) := ⟨Z, ⟨φ⟩⟩
  have h1 : f i = finrank k hex.choose := dif_pos hex
  obtain ⟨ψ⟩ := hex.choose_spec
  have h2 : finrank k Z = finrank k hex.choose := by
    have e₁₂ : modB e Z ≃ₗ[B] modB e hex.choose := φ.trans ψ.symm
    exact (e₁₂.restrictScalars k).finrank_eq
  rw [h2, ← h1]
  exact Finset.le_sup (f := f) (Finset.mem_univ i)

end Killed

end LargeIndecomposable.RayCat
