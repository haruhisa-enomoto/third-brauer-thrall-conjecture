module

public import LargeIndecomposable.BongartzTheorem.LongLines.CoverLine
public import LargeIndecomposable.BongartzTheorem.ContourExclusion.NoContour
public import LargeIndecomposable.Coverings.UniversalCover.CoverChain
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.CycleCoords

/-!
# A monomial band from a line of the cover

Labels of cover paths are paths of `Q_P` with the same value (`pathMor_labs`). A minimal good
pair of sinks of a line (`CLine.GoodPair`) projects to a closed walk of `Q_P` with a sink; it is
locally injective and primitive, and its directed segments are directed segments of the line, so
they have nonzero value. If `P` has no contours, this is a monomial band of `k(P)`
(BO23, proof of Theorem 7; BO13b, Lemma 7.2).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- The label of an arrow of the cover. -/
def arrLab {a b : RayVert (Cover x₀)} (f : a ⟶ b) : (quiver P).A :=
  ⟨a.out.y, b.out.y, val f.1, isIrreducible_val f.2⟩

/-- The labels of a path of the cover. -/
def labs {a : RayVert (Cover x₀)} : ∀ {b : RayVert (Cover x₀)}, Quiver.Path a b → List (quiver P).A
  | _, .nil => []
  | _, .cons q e => labs q ++ [arrLab e]

lemma labs_comp {a b : RayVert (Cover x₀)} (p : Quiver.Path a b) :
    ∀ {c : RayVert (Cover x₀)} (q : Quiver.Path b c), labs (p.comp q) = labs p ++ labs q
  | _, .nil => by simp [labs]
  | _, .cons q e => by
    change labs (p.comp q) ++ [arrLab e] = labs p ++ (labs q ++ [arrLab e])
    rw [labs_comp p q, List.append_assoc]

lemma pathFrom_labs {a : RayVert (Cover x₀)} : ∀ {b : RayVert (Cover x₀)} (q : Quiver.Path a b),
    PathFrom (D := quiver P) a.out.y (labs q) b.out.y
  | _, .nil => rfl
  | _, .cons q e => pathFrom_append _ [arrLab e] _ _ _ (pathFrom_labs q) ⟨rfl, rfl⟩

lemma pathMor_labs {a : RayVert (Cover x₀)} : ∀ {b : RayVert (Cover x₀)} (q : Quiver.Path a b),
    pathMor (labs q) a.out.y b.out.y (pathFrom_labs q) = val (pathVal q)
  | _, .nil => by simp [labs, pathMor, pathVal]; rfl
  | _, .cons q e => by
    refine (pathMor_append (labs q) [arrLab e] _ _ _ (pathFrom_labs q) ⟨rfl, rfl⟩).trans ?_
    rw [pathMor_labs q]
    change _ ≫ (eqToHom rfl ≫ val e.1 ≫ eqToHom rfl) = val (pathVal q ≫ e.1)
    rw [val_comp]
    simp

/-- A path of the cover with nonzero value has labels outside the zero paths. -/
lemma labs_not_mem_zeroPaths {a b : RayVert (Cover x₀)} (q : Quiver.Path a b)
    (hq : pathVal q ≠ 0) : labs q ∉ ZeroPaths P := by
  suffices key : ∀ l, l = labs q → ∀ x y (h : PathFrom (D := quiver P) x l y), pathMor l x y h ≠ 0
    from fun ⟨x, y, h, h0⟩ ↦ key _ rfl x y h h0
  intro l hl x y h
  rcases l with _ | ⟨c, l⟩
  · change x = y at h
    subst h
    simpa [pathMor] using IsRayCategory.id_ne_zero x
  · revert h
    rw [hl]
    intro h
    have hne : labs q ≠ [] := by rw [← hl]; exact List.cons_ne_nil _ _
    obtain rfl := pathFrom_src_unique (labs q) x a.out.y y b.out.y hne h (pathFrom_labs q)
    obtain rfl := pathFrom_tgt_unique (labs q) a.out.y y b.out.y h (pathFrom_labs q)
    rw [pathMor_labs q]
    intro h0
    exact hq (val_injective (by rw [h0]; rfl))

/-- The target of a lift is determined by the source and the label. -/
def tgtOf (c : Cover x₀) (s : (quiver P).A) (hs : s.1 = c.y) : Cover x₀ :=
  ⟨s.2.1, c.u ≫ cls (eqToHom hs.symm ≫ s.2.2.1) (fun h0 ↦ s.2.2.2.1
    ((cancel_epi (eqToHom hs.symm)).1 (h0.trans comp_zero.symm)))⟩

lemma eq_tgtOf {c d : Cover x₀} (f : RayVert.mk c ⟶ RayVert.mk d) :
    d = tgtOf c (arrLab f) rfl := by
  have hu := u_eq f.1 f.2.1
  have hc : cls (eqToHom rfl ≫ val f.1) (fun h0 ↦ (isIrreducible_val f.2).1
      ((cancel_epi (eqToHom rfl)).1 (h0.trans comp_zero.symm))) =
      cls (val f.1) (val_ne_zero f.2.1) := by
    congr 1; simp
  change d = ⟨d.y, c.u ≫ cls (eqToHom rfl ≫ val f.1) _⟩
  rw [hc, ← hu]

lemma tgtOf_congr (c : Cover x₀) {s s' : (quiver P).A} (h : s = s') (hs : s.1 = c.y)
    (hs' : s'.1 = c.y) : tgtOf c s hs = tgtOf c s' hs' := by
  subst h; rfl

/-- **Arrows with the same source and label have the same target.** -/
lemma arrLab_tgt_eq {c d d' : Cover x₀} (f : RayVert.mk c ⟶ RayVert.mk d)
    (f' : RayVert.mk c ⟶ RayVert.mk d') (h : arrLab f = arrLab f') : d = d' :=
  (eq_tgtOf f).trans ((tgtOf_congr c h rfl rfl).trans (eq_tgtOf f').symm)

/-- The source of a lift is determined by the target and the label. -/
def srcOf (d : Cover x₀) (s : (quiver P).A) (hs : s.2.1 = d.y) : Cover x₀ :=
  ⟨s.1, d.u ≫ inv (cls (s.2.2.1 ≫ eqToHom hs) (fun h0 ↦ s.2.2.2.1
    ((cancel_mono (eqToHom hs)).1 (h0.trans zero_comp.symm))))⟩

lemma eq_srcOf {c d : Cover x₀} (f : RayVert.mk c ⟶ RayVert.mk d) :
    c = srcOf d (arrLab f) rfl := by
  have hu := u_eq f.1 f.2.1
  have hc : cls (val f.1 ≫ eqToHom rfl) (fun h0 ↦ (isIrreducible_val f.2).1
      ((cancel_mono (eqToHom rfl)).1 (h0.trans zero_comp.symm))) =
      cls (val f.1) (val_ne_zero f.2.1) := by
    congr 1; simp
  change c = ⟨c.y, d.u ≫ inv (cls (val f.1 ≫ eqToHom rfl) _)⟩
  rw [hc, hu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

lemma srcOf_congr (d : Cover x₀) {s s' : (quiver P).A} (h : s = s') (hs : s.2.1 = d.y)
    (hs' : s'.2.1 = d.y) : srcOf d s hs = srcOf d s' hs' := by
  subst h; rfl

/-- **Arrows with the same target and label have the same source.** -/
lemma arrLab_src_eq {c c' d : Cover x₀} (f : RayVert.mk c ⟶ RayVert.mk d)
    (f' : RayVert.mk c' ⟶ RayVert.mk d) (h : arrLab f = arrLab f') : c = c' :=
  (eq_srcOf f).trans ((srcOf_congr d h rfl rfl).trans (eq_srcOf f').symm)

namespace CLine

variable (L : CLine x₀)

/-- The `i`-th arrow of the line with its endpoints. -/
def larr (i : ℕ) (hi : i < L.n) :
    Σ a b : ℕ, (RayVert.mk (L.pt a) ⟶ RayVert.mk (L.pt b)) :=
  if h : L.fwd i = true then
    ⟨i, i + 1, ⟨(L.arrF i hi h).choose, (L.arrF i hi h).choose_spec⟩⟩
  else
    ⟨i + 1, i, ⟨(L.arrB i hi (by simpa using h)).choose,
      (L.arrB i hi (by simpa using h)).choose_spec⟩⟩

lemma larr_fst (i : ℕ) (hi : i < L.n) : (L.larr i hi).1 = if L.fwd i then i else i + 1 := by
  unfold larr; split <;> simp_all

lemma larr_snd (i : ℕ) (hi : i < L.n) : (L.larr i hi).2.1 = if L.fwd i then i + 1 else i := by
  unfold larr
  by_cases h : L.fwd i = true
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

/-- The label of the `i`-th arrow. -/
def lab (i : ℕ) (hi : i < L.n) : (quiver P).A := arrLab (L.larr i hi).2.2

lemma lab_src (i : ℕ) (hi : i < L.n) : (quiver P).src (L.lab i hi) = (L.pt (L.larr i hi).1).y :=
  rfl

lemma lab_tgt (i : ℕ) (hi : i < L.n) :
    (quiver P).tgt (L.lab i hi) = (L.pt (L.larr i hi).2.1).y := rfl

lemma larr_le (i : ℕ) (hi : i < L.n) : (L.larr i hi).1 ≤ L.n ∧ (L.larr i hi).2.1 ≤ L.n := by
  have h1 := L.larr_fst i hi
  have h2 := L.larr_snd i hi
  split_ifs at h1 h2 <;> omega

lemma lab_inj_aux {a b a' b' : ℕ} (f : RayVert.mk (L.pt a) ⟶ RayVert.mk (L.pt b))
    (f' : RayVert.mk (L.pt a') ⟶ RayVert.mk (L.pt b')) (ha : a = a') (h : arrLab f = arrLab f') :
    L.pt b = L.pt b' := by
  subst ha; exact arrLab_tgt_eq f f' h

lemma lab_inj_aux' {a b a' b' : ℕ} (f : RayVert.mk (L.pt a) ⟶ RayVert.mk (L.pt b))
    (f' : RayVert.mk (L.pt a') ⟶ RayVert.mk (L.pt b')) (hb : b = b') (h : arrLab f = arrLab f') :
    L.pt a = L.pt a' := by
  subst hb; exact arrLab_src_eq f f' h

lemma idx_eq {i i' : ℕ} (hi : i < L.n) (hi' : i' < L.n)
    (h1 : (L.larr i hi).1 = (L.larr i' hi').1) (h2 : (L.larr i hi).2.1 = (L.larr i' hi').2.1) :
    i = i' := by
  rw [larr_fst, larr_fst] at h1
  rw [larr_snd, larr_snd] at h2
  split_ifs at h1 h2 <;> omega

/-- Arrows with the same source and label are equal. -/
lemma lab_inj_src {i i' : ℕ} (hi : i < L.n) (hi' : i' < L.n) (h : L.lab i hi = L.lab i' hi')
    (hs : (L.larr i hi).1 = (L.larr i' hi').1) : i = i' := by
  have ht := L.lab_inj_aux (L.larr i hi).2.2 (L.larr i' hi').2.2 hs h
  exact L.idx_eq hi hi' hs (L.inj _ _ (L.larr_le i hi).2 (L.larr_le i' hi').2 ht)

/-- Arrows with the same target and label are equal. -/
lemma lab_inj_tgt {i i' : ℕ} (hi : i < L.n) (hi' : i' < L.n) (h : L.lab i hi = L.lab i' hi')
    (ht : (L.larr i hi).2.1 = (L.larr i' hi').2.1) : i = i' := by
  have hs := L.lab_inj_aux' (L.larr i hi).2.2 (L.larr i' hi').2.2 ht h
  exact L.idx_eq hi hi' (L.inj _ _ (L.larr_le i hi).1 (L.larr_le i' hi').1 hs) ht

/-- Forgetting irreducibility in a label. -/
def forget (s : (quiver P).A) : Σ x y : P, (x ⟶ y) := ⟨s.1, s.2.1, s.2.2.1⟩

lemma forget_lab_fwd (i : ℕ) (hi : i < L.n) (h : L.fwd i = true) : forget (L.lab i hi) = L.labL i := by
  unfold forget lab larr labL
  rw [dif_pos h, dif_pos ⟨hi, h⟩]
  rfl

lemma forget_lab_bwd (t : ℕ) (hi : t + 1 < L.n) (h : L.fwd (t + 1) = false) :
    forget (L.lab (t + 1) hi) = L.labR t := by
  unfold forget lab larr labR
  rw [dif_neg (by simp [h]), dif_pos ⟨hi, h⟩]
  rfl

section Band

variable {L} {t t' : ℕ} (hg : L.GoodPair t t')

include hg in
lemma two_le : t + 2 ≤ t' := by
  obtain ⟨h1, h2, h3, -⟩ := hg
  by_contra h
  obtain rfl : t' = t + 1 := by omega
  have a1 : L.fwd (t + 1) = false := h1.2.2
  have a2 : L.fwd (t + 1) = true := h2.2.1
  rw [a1] at a2
  exact absurd a2 (by simp)

/-- The number of middle arrows of the band. -/
def nc (t t' : ℕ) : ℕ := t' - t - 2

include hg in
lemma t'_eq : t' = t + 2 + nc t t' := by
  have := two_le hg; unfold nc; omega

variable (L t t') in
/-- The orientations of the middle arrows. -/
def eps (j : Fin (nc t t')) : Bool := L.fwd (t + 2 + j)

variable (t) in
/-- The line arrow of an arrow of the cycle. -/
def lidx (e : CycArr (nc t t')) : ℕ := t + 1 + CycArr.posNat (nc t t') e

include hg in
lemma lidx_lt (e : CycArr (nc t t')) : lidx t e < L.n := by
  have h1 := CycArr.posNat_lt (nc t t') e
  have h2 := t'_eq hg
  have h3 := hg.2.1.1
  unfold lidx; omega

variable (t) in
/-- The line point of a vertex of the cycle. -/
def vidx : Option (Fin (nc t t' + 1)) → ℕ
  | none => t + 1
  | some j => t + 2 + j

include hg in
lemma src_idx (e : CycArr (nc t t')) :
    (L.larr (lidx t e) (lidx_lt hg e)).1 = vidx t ((cycleQuiver (nc t t') (eps L t t')).src e) := by
  rw [larr_fst]
  have h2 := t'_eq hg
  obtain ⟨⟨-, -, hf1⟩, ⟨-, hf2, -⟩, -⟩ := hg
  cases e with
  | first =>
    simp only [lidx, CycArr.posNat, vidx, add_zero, Fin.val_zero]
    rw [if_neg (by simp [hf1])]
  | second =>
    simp only [lidx, CycArr.posNat, vidx, Fin.val_last]
    simp only [show t + 1 + (nc t t' + 1) = t' by omega, hf2, if_true]; omega
  | mid j =>
    clear h2
    simp only [lidx, CycArr.posNat, vidx, eps]
    simp only [show t + 1 + ((j : ℕ) + 1) = t + 2 + j by omega]
    split_ifs <;> simp_all <;> omega

include hg in
lemma tgt_idx (e : CycArr (nc t t')) (he : e ≠ .second) :
    (L.larr (lidx t e) (lidx_lt hg e)).2.1 = vidx t ((cycleQuiver (nc t t') (eps L t t')).tgt e) := by
  rw [larr_snd]
  obtain ⟨⟨-, -, hf1⟩, -, -⟩ := hg
  cases e with
  | first =>
    simp only [lidx, CycArr.posNat, vidx, add_zero]
    rw [if_neg (by simp [hf1])]
  | second => exact absurd rfl he
  | mid j =>
    simp only [lidx, CycArr.posNat, vidx, eps]
    simp only [show t + 1 + ((j : ℕ) + 1) = t + 2 + j by omega]
    split_ifs <;> simp_all <;> omega

include hg in
lemma tgt_idx_second : (L.larr (lidx t (.second : CycArr (nc t t'))) (lidx_lt hg _)).2.1 = t' + 1 := by
  rw [larr_snd]
  have h2 := t'_eq hg
  obtain ⟨-, ⟨-, hf2, -⟩, -⟩ := hg
  simp only [lidx, CycArr.posNat]
  simp only [show t + 1 + (nc t t' + 1) = t' by omega, hf2, if_true]

include hg in
/-- The cycle of the band as a closed walk of `Q_P`. -/
def cyc : FinQuiver.Hom (cycleQuiver (nc t t') (eps L t t')) (quiver P) where
  vert v := (L.pt (vidx t v)).y
  arr e := L.lab (lidx t e) (lidx_lt hg e)
  map_src e := by
    rw [lab_src, src_idx hg e]
  map_tgt e := by
    rw [lab_tgt]
    by_cases he : e = .second
    · subst he
      rw [tgt_idx_second hg]
      exact hg.2.2.2.1.symm
    · rw [tgt_idx hg e he]

lemma lidx_first : lidx t (.first : CycArr (nc t t')) = t + 1 := rfl

include hg in
lemma lidx_second : lidx t (.second : CycArr (nc t t')) = t' := by
  have := t'_eq hg; simp only [lidx, CycArr.posNat]; omega

lemma forget_lab_fwd' {i j : ℕ} (hi : i < L.n) (hij : i = j) (h : L.fwd j = true) :
    forget (L.lab i hi) = L.labL j := by
  subst hij; exact L.forget_lab_fwd i hi h

include hg in
lemma arr_second_ne_first : (cyc hg).arr .second ≠ (cyc hg).arr .first := by
  intro ha
  have h1 : forget ((cyc hg).arr .second) = L.labL t' :=
    forget_lab_fwd' _ (lidx_second hg) hg.2.1.2.1
  have h2 : forget ((cyc hg).arr .first) = L.labR t := L.forget_lab_bwd t _ hg.1.2.2
  exact hg.2.2.2.2 (h2.symm.trans ((congrArg forget ha).symm.trans h1))

include hg in
/-- **The cycle is locally injective.** -/
lemma cyc_locInj : (cyc hg).LocallyInjective := by
  constructor
  · intro e e' hs ha
    have h1 := src_idx hg e
    have h2 := src_idx hg e'
    have := L.lab_inj_src (lidx_lt hg e) (lidx_lt hg e') ha (by rw [h1, h2, hs])
    exact CycArr.posNat_injective _ (by unfold lidx at this; omega)
  · intro e e' ht ha
    by_cases he : e = .second <;> by_cases he' : e' = .second
    · rw [he, he']
    · exfalso
      subst he
      cases e' with
      | first => exact arr_second_ne_first hg ha
      | second => exact he' rfl
      | mid j => simp at ht
    · exfalso
      subst he'
      cases e with
      | first => exact arr_second_ne_first hg ha.symm
      | second => exact he rfl
      | mid j => simp at ht
    · have h1 := tgt_idx hg e he
      have h2 := tgt_idx hg e' he'
      have := L.lab_inj_tgt (lidx_lt hg e) (lidx_lt hg e') ha (by rw [h1, h2, ht])
      exact CycArr.posNat_injective _ (by unfold lidx at this; omega)

lemma posNat_eixSymm {N : ℕ} {ε : Fin N → Bool} (y : ZMod (N + 2)) :
    CycArr.posNat N ((cycleCoords N ε).eix.symm y) = y.val := by
  have h : (cycleCoords N ε).eix ((cycleCoords N ε).eix.symm y) = y := Equiv.apply_symm_apply _ _
  change CycArr.posFun N _ = y at h
  rw [CycArr.posFun_eq] at h
  have h2 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (CycArr.posNat_lt N _)] at h2

include hg in
lemma cfwd_eq (e : CycArr (nc t t')) :
    (cycleCoords (nc t t') (eps L t t')).fwd e = L.fwd (lidx t e) := by
  cases e with
  | first => exact hg.1.2.2.symm
  | second => rw [lidx_second hg]; exact hg.2.1.2.1.symm
  | mid j =>
    change L.fwd (t + 2 + j) = L.fwd (t + 1 + ((j : ℕ) + 1))
    rw [show t + 1 + ((j : ℕ) + 1) = t + 2 + j by omega]

include hg in
/-- **A minimal good pair gives a primitive walk.** -/
lemma cyc_primitive (hmin : ∀ u u', L.GoodPair u u' → t' - t ≤ u' - u) :
    FinQuiver.Primitive (cyc hg) (cycleCoords (nc t t') (eps L t t')) := by
  intro τ hτ
  by_contra hall
  push_neg at hall
  have hN' := t'_eq hg
  have hr0 : τ.val ≠ 0 := fun h ↦ hτ ((ZMod.val_eq_zero τ).1 h)
  have hrlt : τ.val < nc t t' + 2 := ZMod.val_lt τ
  have hxv : (((nc t t' + 1 : ℕ) : ZMod (nc t t' + 2))).val = nc t t' + 1 :=
    ZMod.val_natCast_of_lt (by omega)
  obtain ⟨eA, hpA, hA1, hA2⟩ : ∃ eA, CycArr.posNat _ eA = τ.val ∧
      (cyc hg).arr eA = (cyc hg).arr .first ∧
      (cycleCoords (nc t t') (eps L t t')).fwd eA =
        (cycleCoords (nc t t') (eps L t t')).fwd .first := by
    have hA := hall 0
    simp only [FinQuiver.signedLabel, Prod.mk.injEq] at hA
    have p0 : (cycleCoords (nc t t') (eps L t t')).eix.symm 0 = .first :=
      CycArr.posNat_injective _ (by rw [posNat_eixSymm]; rfl)
    rw [p0] at hA
    exact ⟨_, by rw [posNat_eixSymm, zero_add], hA.1, hA.2⟩
  obtain ⟨eB, hpB, hB1, hB2⟩ : ∃ eB, CycArr.posNat _ eB = τ.val - 1 ∧
      (cyc hg).arr eB = (cyc hg).arr .second ∧
      (cycleCoords (nc t t') (eps L t t')).fwd eB =
        (cycleCoords (nc t t') (eps L t t')).fwd .second := by
    have hB := hall ((nc t t' + 1 : ℕ) : ZMod (nc t t' + 2))
    simp only [FinQuiver.signedLabel, Prod.mk.injEq] at hB
    have p1 : (cycleCoords (nc t t') (eps L t t')).eix.symm ((nc t t' + 1 : ℕ) : ZMod _) =
        .second :=
      CycArr.posNat_injective _ (by rw [posNat_eixSymm, hxv]; rfl)
    rw [p1] at hB
    refine ⟨_, ?_, hB.1, hB.2⟩
    rw [posNat_eixSymm, ZMod.val_add, hxv]
    rw [show nc t t' + 1 + τ.val = (τ.val - 1) + (nc t t' + 2) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have lA : lidx t eA = t + 1 + τ.val := by unfold lidx; rw [hpA]
  have lB : lidx t eB = t + τ.val := by unfold lidx; rw [hpB]; omega
  have fA : L.fwd (t + 1 + τ.val) = false := by
    rw [← lA, ← cfwd_eq hg eA, hA2, cfwd_eq hg]; exact hg.1.2.2
  have fB : L.fwd (t + τ.val) = true := by
    rw [← lB, ← cfwd_eq hg eB, hB2, cfwd_eq hg, lidx_second hg]; exact hg.2.1.2.1
  have hsink : L.IsSinkAt (t + τ.val) :=
    ⟨by have := hg.2.1.1; omega, fB,
      by rw [show t + τ.val + 1 = t + 1 + τ.val by omega]; exact fA⟩
  have hy : (L.pt (t + 1)).y = (L.pt (t + τ.val + 1)).y := by
    have hfB : L.fwd (lidx t eB) = true := by rw [lB]; exact fB
    have h1 : (quiver P).tgt ((cyc hg).arr eB) = (L.pt (t + τ.val + 1)).y := by
      change (L.pt (L.larr (lidx t eB) _).2.1).y = _
      rw [larr_snd, if_pos hfB, lB]
    have h2 : (quiver P).tgt ((cyc hg).arr .second) = (L.pt (t + 1)).y := (cyc hg).map_tgt .second
    rw [hB1] at h1
    exact h2.symm.trans h1
  have hlab : L.labR t ≠ L.labL (t + τ.val) := by
    have h1 : forget ((cyc hg).arr eB) = L.labL (t + τ.val) := forget_lab_fwd' _ lB fB
    have h2 : forget ((cyc hg).arr .second) = L.labL t' :=
      forget_lab_fwd' _ (lidx_second hg) hg.2.1.2.1
    rw [← h1, hB1, h2]
    exact hg.2.2.2.2
  have := hmin t (t + τ.val) ⟨hg.1, hsink, by omega, hy, hlab⟩
  omega

include hg in
lemma src_some (e : CycArr (nc t t')) :
    ∃ j, (cycleQuiver (nc t t') (eps L t t')).src e = some j := by
  cases e with
  | first => exact ⟨_, rfl⟩
  | second => exact ⟨_, rfl⟩
  | mid j => exact ⟨_, rfl⟩

include hg in
/-- Directed paths of the cycle lift to paths inside the line with the same labels. -/
lemma cover_path : ∀ (le : List (CycArr (nc t t'))) (i j : Option (Fin (nc t t' + 1))),
    PathFrom (D := cycleQuiver (nc t t') (eps L t t')) i le j → ∀ a, a ≤ L.n →
    (∀ j₀, i = some j₀ → a = vidx t (some j₀)) →
    ∃ (b : ℕ) (q : Quiver.Path (RayVert.mk (L.pt a)) (RayVert.mk (L.pt b))),
      PathIn L.pts q ∧ labs q = le.map (cyc hg).arr
  | [], _, _, _, a, ha, _ => ⟨a, .nil, ⟨a, ha, rfl⟩, rfl⟩
  | e :: le, i, j, h, a, ha, hv => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨j₀, hj₀⟩ := src_some hg e
    have haa : a = (L.larr (lidx t e) (lidx_lt hg e)).1 := by
      rw [hv j₀ (h1.symm.trans hj₀), src_idx hg e, hj₀]
    subst haa
    obtain ⟨b, q, hq, hlq⟩ := cover_path le _ j h2 (L.larr (lidx t e) (lidx_lt hg e)).2.1
      (L.larr_le _ _).2 (fun j₁ hj₁ ↦ by
        have he : e ≠ .second := by rintro rfl; simp at hj₁
        rw [tgt_idx hg e he, hj₁])
    refine ⟨b, (Quiver.Path.nil.cons (L.larr (lidx t e) (lidx_lt hg e)).2.2).comp q, ?_, ?_⟩
    · rw [pathIn_comp_iff]
      exact ⟨⟨⟨_, (L.larr_le _ _).1, rfl⟩, _, (L.larr_le _ _).2, rfl⟩, hq⟩
    · rw [labs_comp, hlq]
      rfl

include hg in
/-- **Directed segments of the cycle have nonzero value.** -/
lemma cyc_band (le : List (CycArr (nc t t'))) (i j : Option (Fin (nc t t' + 1)))
    (h : PathFrom (D := cycleQuiver (nc t t') (eps L t t')) i le j) :
    le.map (cyc hg).arr ∉ ZeroPaths P := by
  have hN := t'_eq hg
  have hn := hg.2.1.1
  obtain ⟨b, q, hq, hlq⟩ : ∃ (b : ℕ) (q : Quiver.Path (RayVert.mk (L.pt (vidx t i)))
      (RayVert.mk (L.pt b))), PathIn L.pts q ∧ labs q = le.map (cyc hg).arr := by
    refine cover_path hg le i j h (vidx t i) ?_ ?_
    · rcases i with _ | j₀
      · change t + 1 ≤ L.n; omega
      · change t + 2 + (j₀ : ℕ) ≤ L.n; have := j₀.2; omega
    · rintro j₀ rfl; rfl
  rw [← hlq]
  exact labs_not_mem_zeroPaths q (L.nz q hq)

end Band

end CLine

section Assemble

open CLine

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- **A monomial band from a line** (BO23, proof of Theorem 7): if `P` has no contours, a
minimal good pair of sinks of a line of the cover gives a monomial band of `B ≅ k(P)`. -/
def lineBand (L : CLine x₀) {t t' : ℕ} (hg : L.GoodPair t t')
    (hmin : ∀ u u', L.GoodPair u u' → t' - t ≤ u' - u) (hnc : NoContour P)
    (e : Linearization P k ≃ₐ[k] B) : Walk.MonomialBand k B where
  n := nc t t'
  ε := eps L t t'
  Q := quiver P
  p := cyc hg
  locInj := cyc_locInj hg
  primitive := cyc_primitive hg hmin
  π := e.toAlgHom.comp (linPres P k)
  surj := e.surjective.comp (linPres_surjective P k)
  P := ZeroPaths P
  ker_le z hz := by
    have : linPres P k z = 0 := by
      have h0 : e (linPres P k z) = e 0 := by rw [map_zero]; exact hz
      exact e.injective h0
    exact ker_linPres_le k hnc z this
  band le i j h := cyc_band hg le i j h

/-- **A long line of the cover gives a monomial band.** -/
theorem nonempty_monomialBand [∀ x y : P, Finite (x ⟶ y)] (L : CLine x₀)
    (hn : (2 * Fintype.card P + 1) * (2 * bound P) ≤ L.n) (hnc : NoContour P)
    (e : Linearization P k ≃ₐ[k] B) : Nonempty (Walk.MonomialBand k B) := by
  obtain ⟨t, t', hg, hmin⟩ := L.exists_minimal_goodPair (L.exists_goodPair hn)
  exact ⟨lineBand L hg hmin hnc e⟩

end Assemble

end LargeIndecomposable.RayCat
