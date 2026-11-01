module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceDirecting

/-!
# Branching morphisms

A nonzero morphism of a ray category *branches* if it has two different first arrows, while every
proper left factor has only one first arrow. If two different paths have the same nonzero value,
a branching morphism exists (`exists_isBranch`). In a convex piece of the cover, a lift of a
branching morphism gives branch data for the polygon of its interval.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P]

/-- The first arrows of the paths with a given value. -/
def Fst {x z : P} (u : x ⟶ z) : Set (quiver P).A :=
  {c | ∃ (l : List (quiver P).A) (h : PathFrom (D := quiver P) x (c :: l) z),
    pathMor (c :: l) x z h = u}

/-- Two different first arrows. -/
def TwoFst {x z : P} (u : x ⟶ z) : Prop := ∃ c c', c ∈ Fst u ∧ c' ∈ Fst u ∧ c ≠ c'

/-- A morphism with two first arrows, whose proper left factors have at most one. -/
def IsBranch {x y : P} (w : x ⟶ y) : Prop :=
  w ≠ 0 ∧ TwoFst w ∧ ∀ (z : P) (u : x ⟶ z) (g : z ⟶ y), u ≫ g = w →
    (⟨z, u⟩ : Σ z, x ⟶ z) ≠ ⟨y, w⟩ → ¬TwoFst u

/-- The left factors of a morphism. -/
def facS {x y : P} (w : x ⟶ y) : Set (Σ z, x ⟶ z) := {p | ∃ g : p.1 ⟶ y, p.2 ≫ g = w}

lemma facS_ssubset {x y z : P} {w : x ⟶ y} {u : x ⟶ z} {g : z ⟶ y} (hw : w ≠ 0) (h : u ≫ g = w)
    (hne : (⟨z, u⟩ : Σ z, x ⟶ z) ≠ ⟨y, w⟩) : facS u ⊂ facS w := by
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (by rw [← h, zero_comp])
  refine ⟨?_, fun hsub ↦ ?_⟩
  · rintro ⟨z', u'⟩ ⟨g', hg'⟩
    refine ⟨g' ≫ g, ?_⟩
    change u' ≫ g' = u at hg'
    change u' ≫ g' ≫ g = w
    rw [← Category.assoc, hg', h]
  · obtain ⟨g', hg'⟩ := hsub (show (⟨y, w⟩ : Σ z, x ⟶ z) ∈ facS w from ⟨𝟙 y, Category.comp_id w⟩)
    change w ≫ g' = u at hg'
    have h1 : w = 𝟙 x ≫ w ≫ (g' ≫ g) := by
      rw [Category.id_comp, ← Category.assoc, hg', h]
    have h2 : u = 𝟙 x ≫ u ≫ (g ≫ g') := by
      rw [Category.id_comp, ← Category.assoc, h, hg']
    have e1 := (IsRayCategory.eq_id_of_two_sided w hw _ _ h1).2
    have e2 := (IsRayCategory.eq_id_of_two_sided u hu _ _ h2).2
    haveI : IsIso g := ⟨g', e2, e1⟩
    have hzy : z = y := IsRayCategory.skeletal ⟨asIso g⟩
    subst hzy
    have he : g = 𝟙 z := RayCat.eq_id_of_isIso g inferInstance
    apply hne
    have : u = w := by
      rw [← h, he, Category.comp_id]
    rw [this]

/-- **Branching morphisms exist.** -/
theorem exists_isBranch (h : ∃ (x y : P) (w : x ⟶ y), w ≠ 0 ∧ TwoFst w) :
    ∃ (x y : P) (w : x ⟶ y), IsBranch w := by
  obtain ⟨x, y, w, hw, h2⟩ := h
  haveI : ∀ a b : P, Finite (a ⟶ b) := IsRayCategory.finite_hom
  have key : ∀ (n : ℕ) (y : P) (w : x ⟶ y), (facS w).ncard = n → w ≠ 0 → TwoFst w →
      ∃ (y : P) (w : x ⟶ y), IsBranch w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y w hn hw h2
      by_cases hb : IsBranch w
      · exact ⟨y, w, hb⟩
      · have : ∃ (z : P) (u : x ⟶ z) (g : z ⟶ y), u ≫ g = w ∧
            (⟨z, u⟩ : Σ z, x ⟶ z) ≠ ⟨y, w⟩ ∧ TwoFst u := by
          by_contra hno
          push Not at hno
          exact hb ⟨hw, h2, hno⟩
        obtain ⟨z, u, g, h3, h4, h5⟩ := this
        have hu : u ≠ 0 := by
          rintro rfl
          exact hw (by rw [← h3, zero_comp])
        have hlt := Set.ncard_lt_ncard (facS_ssubset hw h3 h4) (Set.toFinite _)
        exact ih _ (by omega) z u rfl hu h5
  obtain ⟨y', w', hb⟩ := key _ y w rfl hw h2
  exact ⟨x, y', w', hb⟩


section Piece

variable {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k] (hpar : ParEq S)

/-- There is a path in the piece. -/
def PR (x y : (pieceQuiver S).V) : Prop := ∃ l, PathFrom x l y

lemma PR.refl (x : (pieceQuiver S).V) : PR x x := ⟨[], rfl⟩

lemma PR.trans {x y z : (pieceQuiver S).V} (h1 : PR x y) (h2 : PR y z) : PR x z := by
  obtain ⟨l, hl⟩ := h1
  obtain ⟨l', hl'⟩ := h2
  exact ⟨l ++ l', pathFrom_append l l' hl hl'⟩

variable (k) in
/-- The corner element of the composite. -/
def cv (x y : (pieceQuiver S).V) : PieceAlg k S := pev y * pbvec x y * pev x

include hpar in
lemma cv_eq_of_path {x y : (pieceQuiver S).V} {l : List (pieceQuiver S).A} (h : PathFrom x l y)
    (hne : l ≠ []) : cv k x y = pmk (word k (pieceQuiver S) l) := by
  unfold cv
  rw [← pmk_word_eq_bvec hpar h]
  change pmk (vertex k _ y) * _ * pmk (vertex k _ x) = _
  rw [← map_mul, ← map_mul, vertex_mul_word_path k hne h y, if_pos rfl,
    word_mul_vertex_path k hne h x, if_pos rfl]

include hpar in
lemma cv_self (x : (pieceQuiver S).V) : cv k x x = pev x := by
  unfold cv
  rw [← pmk_word_eq_bvec hpar (x := x) (l := []) rfl]
  simp [word, ev_mul_ev]

include hpar in
lemma cv_mul {x y z : (pieceQuiver S).V} (h1 : PR x y) (h2 : PR y z) :
    cv k y z * cv k x y = cv k x z := by
  obtain ⟨l₁, hl₁⟩ := h1
  obtain ⟨l₂, hl₂⟩ := h2
  by_cases h₁ : l₁ = []
  · subst h₁
    change x = y at hl₁
    subst hl₁
    rw [cv_self hpar]
    by_cases h₂ : l₂ = []
    · subst h₂
      change x = z at hl₂
      subst hl₂
      rw [cv_self hpar, ev_mul_ev, if_pos rfl]
    · rw [cv_eq_of_path hpar hl₂ h₂]
      change pmk _ * pmk (vertex k _ x) = _
      rw [← map_mul, word_mul_vertex_path k h₂ hl₂ x, if_pos rfl]
  · by_cases h₂ : l₂ = []
    · subst h₂
      change y = z at hl₂
      subst hl₂
      rw [cv_self hpar, cv_eq_of_path hpar hl₁ h₁]
      change pmk (vertex k _ y) * pmk _ = _
      rw [← map_mul, vertex_mul_word_path k h₁ hl₁ y, if_pos rfl]
    · rw [cv_eq_of_path hpar hl₁ h₁, cv_eq_of_path hpar hl₂ h₂,
        cv_eq_of_path hpar (pathFrom_append l₁ l₂ hl₁ hl₂) (by simp [h₁]), word_append, map_mul]

include hpar in
lemma gval_mul {x y z : (pieceQuiver S).V} (h1 : PR x y) (h2 : PR y z) :
    gval x y ≫ gval y z = gval x z := by
  obtain ⟨l₁, hl₁⟩ := h1
  obtain ⟨l₂, hl₂⟩ := h2
  rw [gval_append hpar hl₁ hl₂, gval_eq hpar hl₂]

include hpar in
lemma cv_ne_zero {x y : (pieceQuiver S).V} (h : gval x y ≠ 0) : cv k x y ≠ 0 := by
  by_cases hxy : y = x
  · subst hxy
    rw [cv_self hpar]
    exact ev_ne_zero y
  · obtain ⟨l, hl⟩ := exists_path_of_gval h
    have hne : l ≠ [] := by
      rintro rfl
      exact hxy (show x = y from hl).symm
    rw [cv_eq_of_path hpar hl hne, pmk_word_eq_bvec hpar hl]
    exact bvec_ne_zero hpar hxy h

include hpar in
/-- Corners are multiples of the composite. -/
lemma corner_smul_cv (x y : (pieceQuiver S).V) (a : PieceAlg k S) (hacyc : ∀ (i : (pieceQuiver S).V)
    (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i) :
    ∃ c : k, pev y * a * pev x = c • cv k x y := by
  by_cases hxy : y = x
  · subst hxy
    obtain ⟨c, hc⟩ := (pieceDirData (k := k) hacyc).local_ y a
    exact ⟨c, by rw [cv_self hpar]; exact hc⟩
  have hsub : pmk (k := k) '' cornerSet k x y ⊆ {cv k x y} := by
    rintro _ ⟨r, (⟨h, -⟩ | ⟨l, hl, hp, rfl⟩), rfl⟩
    · exact absurd h.symm hxy
    · exact (cv_eq_of_path hpar hp hl).symm
  have h1 := Submodule.span_mono hsub (corner_piece (k := k) a x y)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨c, hc.symm⟩

include hpar in
/-- A nonzero corner has nonzero composite and a path. -/
lemma of_cn_ne_zero (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] →
    ¬PathFrom i l i) {x y : (pieceQuiver S).V} {z : PieceAlg k S}
    (hz : (pieceDirData (k := k) hacyc).Cn y x z) (h0 : z ≠ 0) : PR x y ∧ gval x y ≠ 0 := by
  have h1 : pev y * z * pev x = z := hz.eq
  obtain ⟨c, hc⟩ := corner_smul_cv hpar x y z hacyc
  rw [h1] at hc
  have hgv : gval x y ≠ 0 := by
    intro h
    apply h0
    rw [hc]
    unfold cv
    rw [bvec_eq_zero hpar h, mul_zero, zero_mul, smul_zero]
  have h2 : pev y * z * pev x ≠ 0 := by rwa [h1]
  exact ⟨path_of_rtg ((pieceDirData (k := k) hacyc).hom x y z h2), hgv⟩

/-- A first arrow of a composite lifts to the piece. -/
lemma exists_arrow_of_fst (hS : Convex (S : Set (Cover x₀))) {i j : (pieceQuiver S).V}
    (hg : gval i j ≠ 0) {c : (quiver P).A} (hc : c ∈ Fst (Cover.val (gval i j))) :
    ∃ e : (pieceQuiver S).A, (pieceQuiver S).src e = i ∧ PR ((pieceQuiver S).tgt e) j ∧
      (pieceProj S).arr e = c := by
  obtain ⟨l, h, he⟩ := hc
  have hv : Cover.val (gval i j) ≠ 0 := fun h0 ↦ hg ((val_eq_zero_iff _).1 h0)
  have hne : pathMor (c :: l) _ _ h ≠ 0 := he ▸ hv
  have hu := u_eq_of_ne_zero (gval i j) hg hv
  have hmem : (⟨(pt S j).y, (pt S i).u ≫ cls (pathMor (c :: l) _ _ h) hne⟩ : Cover x₀) ∈ S := by
    rw [cls_congr he hne hv, ← hu]
    exact (show S from j).2
  obtain ⟨le, j', hm, hp, hpt⟩ := exists_lift_piece hS (c :: l) i _ h hne hmem
  have hj : j' = j := by
    apply Subtype.ext
    refine hpt.trans ?_
    rw [cls_congr he hne hv, ← hu]
  subst hj
  cases le with
  | nil => simp at hm
  | cons e r =>
    simp only [List.map_cons, List.cons.injEq] at hm
    exact ⟨e, hp.1, ⟨r, hp.2⟩, hm.1⟩

include hpar in
/-- The label of a first arrow is a first arrow of the composite. -/
lemma fst_of_arrow {i z : (pieceQuiver S).V} {e : (pieceQuiver S).A}
    (he : (pieceQuiver S).src e = i) (hp : PR ((pieceQuiver S).tgt e) z) :
    (pieceProj S).arr e ∈ Fst (Cover.val (gval i z)) := by
  obtain ⟨r, hr⟩ := hp
  have hpath : PathFrom i (e :: r) z := ⟨he, hr⟩
  have hmap := pathFrom_map (pieceProj S) (e :: r) i z hpath
  refine ⟨r.map (pieceProj S).arr, hmap, ?_⟩
  rw [gval_eq hpar hpath, val_compD]
  rfl

include hpar in
/-- An arrow has no other first arrow. -/
lemma eq_of_arrow {e e' : (pieceQuiver S).A} (hs : (pieceQuiver S).src e = (pieceQuiver S).src e')
    (hp : PR ((pieceQuiver S).tgt e') ((pieceQuiver S).tgt e)) : e = e' := by
  obtain ⟨a, b, f, hf⟩ := e
  obtain ⟨a', b', f', hf'⟩ := e'
  change a = a' at hs
  subst hs
  change PR b' b at hp
  have hg : gval a b = f :=
    (gval_eq hpar (l := [⟨a, b, f, hf⟩]) ⟨rfl, rfl⟩).trans (compD_single ⟨a, b, f, hf⟩)
  have hg' : gval a b' = f' :=
    (gval_eq hpar (l := [⟨a, b', f', hf'⟩]) ⟨rfl, rfl⟩).trans (compD_single ⟨a, b', f', hf'⟩)
  have hdec : f = f' ≫ gval b' b := by
    rw [← hg, ← hg']
    exact (gval_mul hpar ⟨[⟨a, b', f', hf'⟩], rfl, rfl⟩ hp).symm
  rcases hf.2.2 _ _ _ hdec with h | h
  · exact absurd h hf'.2.1
  · have hbb : pt S b' = pt S b := IsRayCategory.skeletal ⟨asIso (gval b' b)⟩
    have hb : b' = b := Subtype.ext hbb
    subst hb
    have h1 : gval b' b' = 𝟙 _ := gval_self hpar
    have h2 : f = f' := by rw [hdec, h1, Category.comp_id]
    subst h2
    rfl

section Branch

variable (hS : Convex (S : Set (Cover x₀)))
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)
  {T' : Set (pieceQuiver S).V}
  {U : AR.FDMod k ((pieceDirData (k := k) hacyc).QAlg T')} {i j : T'}
include hS hpar

lemma locInj_arrow {e e' : (pieceQuiver S).A} (hs : (pieceQuiver S).src e = (pieceQuiver S).src e')
    (hl : (pieceProj S).arr e = (pieceProj S).arr e') : e = e' :=
  (pieceProj_locInj S).1 e e' hs hl

/-- **Branch data of a lift of a branching morphism.** -/
theorem exists_branchQ (hw : IsBranch (Cover.val (gval i.1 j.1))) (hpath : PR i.1 j.1)
    (hact : ∃ u : U, (pieceDirData (k := k) hacyc).qmap T' (cv k i.1 j.1) • u ≠ 0) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (B : AR.DirData.BranchQ U κ),
      B.a = i ∧ B.b = j := by
  classical
  let D₀ := pieceDirData (k := k) hacyc
  have hg : gval i.1 j.1 ≠ 0 := fun h0 ↦ hw.1 (by rw [h0]; rfl)
  have hcn : ∀ x y, D₀.Cn y x (cv k x y) := fun x y ↦ AR.DirData.cn_corner y x _
  have hmem : ∀ c, PR i.1 c → PR c j.1 → c ∈ T' := by
    intro c h1 h2
    by_contra hc
    obtain ⟨u, hu⟩ := hact
    apply hu
    rw [← cv_mul hpar h1 h2, map_mul, AR.DirData.qmap_cn_eq_zero (hcn i.1 c) hc, mul_zero, zero_smul]
  have hnea : ∀ e : (pieceQuiver S).A, (pieceQuiver S).src e = i.1 →
      (pieceQuiver S).tgt e ≠ i.1 := fun e h1 h2 ↦
    hacyc i.1 [e] (List.cons_ne_nil _ _) ⟨h1, h2⟩
  let κ : Type := {e : (pieceQuiver S).A // (pieceQuiver S).src e = i.1 ∧
    PR ((pieceQuiver S).tgt e) j.1}
  have hPR : ∀ e : κ, PR i.1 ((pieceQuiver S).tgt e.1) := fun e ↦ ⟨[e.1], e.2.1, rfl⟩
  obtain ⟨c₁, c₂, h1, h2, hc12⟩ := hw.2.1
  obtain ⟨e₁, he₁, he₁', hl₁⟩ := exists_arrow_of_fst hS hg h1
  obtain ⟨e₂, he₂, he₂', hl₂⟩ := exists_arrow_of_fst hS hg h2
  have hne12 : e₁ ≠ e₂ := by
    rintro rfl
    exact hc12 (hl₁.symm.trans hl₂)
  have hnb : ∀ e : κ, (pieceQuiver S).tgt e.1 ≠ j.1 := by
    intro e he
    have hs1 : (pieceQuiver S).src e.1 = (pieceQuiver S).src e₁ := e.2.1.trans he₁.symm
    have hs2 : (pieceQuiver S).src e.1 = (pieceQuiver S).src e₂ := e.2.1.trans he₂.symm
    have h3 : e.1 = e₁ := eq_of_arrow hpar hs1 (by rw [he]; exact he₁')
    have h4 : e.1 = e₂ := eq_of_arrow hpar hs2 (by rw [he]; exact he₂')
    exact hne12 (h3.symm.trans h4)
  have hmem' : ∀ e : κ, (pieceQuiver S).tgt e.1 ∈ T' := fun e ↦ hmem _ (hPR e) e.2.2
  have hij : i ≠ j := by
    rintro rfl
    obtain ⟨r, hr⟩ := he₁'
    exact hacyc i.1 (e₁ :: r) (List.cons_ne_nil _ _) ⟨he₁, hr⟩
  have htri : ∀ (e : κ) c, PR ((pieceQuiver S).tgt e.1) c → PR c j.1 →
      D₀.Tri i.1 j.1 ((pieceQuiver S).tgt e.1) c := by
    intro e c h3 h4
    refine ⟨cv k c j.1, cv k _ c, cv k i.1 _, hcn _ _, hcn _ _, hcn _ _, ?_⟩
    rw [cv_mul hpar h3 h4, cv_mul hpar (hPR e) (h3.trans h4)]
    exact cv_ne_zero hpar hg
  let B : AR.DirData.BranchQ U κ :=
    { a := i
      b := j
      hab := hij
      n := fun e ↦ ⟨_, hmem' e⟩
      hna := fun e h ↦ hnea e.1 e.2.1 (congrArg Subtype.val h)
      hnb := fun e h ↦ hnb e (congrArg Subtype.val h)
      F := fun e ↦ cv k i.1 _
      G := fun e ↦ cv k _ j.1
      hF := fun e ↦ hcn _ _
      hG := fun e ↦ hcn _ _
      act := fun e ↦ by
        obtain ⟨u, hu⟩ := hact
        refine ⟨u, ?_⟩
        rw [cv_mul hpar (hPR e) e.2.2]
        exact hu
      cover := fun c L M hca hcb hL hM hne ↦ by
        have hL0 : L ≠ 0 := fun h ↦ hne (by rw [h, zero_mul])
        have hM0 : M ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
        have h3 := (of_cn_ne_zero hpar hacyc hL hL0).1
        obtain ⟨⟨l, hl⟩, -⟩ := of_cn_ne_zero hpar hacyc hM hM0
        cases l with
        | nil => exact absurd (show i.1 = c from hl).symm hca
        | cons e r =>
          exact ⟨⟨e, hl.1, PR.trans ⟨r, hl.2⟩ h3⟩, htri ⟨e, hl.1, PR.trans ⟨r, hl.2⟩ h3⟩ c ⟨r, hl.2⟩ h3⟩
      disj := fun e e' c hcb h3 h4 ↦ by
        obtain ⟨L, M, R, hL, hM, hR, hne⟩ := h3
        obtain ⟨L', M', R', hL', hM', hR', hne'⟩ := h4
        have hM0 : M ≠ 0 := fun h ↦ hne (by rw [h, mul_zero, zero_mul])
        have hL0 : L ≠ 0 := fun h ↦ hne (by rw [h, zero_mul, zero_mul])
        have hM0' : M' ≠ 0 := fun h ↦ hne' (by rw [h, mul_zero, zero_mul])
        have h5 := (of_cn_ne_zero hpar hacyc hL hL0).1
        have h6 := (of_cn_ne_zero hpar hacyc hM hM0).1
        have h7 := (of_cn_ne_zero hpar hacyc hM' hM0').1
        by_contra hee
        have hne3 : e.1 ≠ e'.1 := fun h ↦ hee (Subtype.ext h)
        have hcomp : Cover.val (gval i.1 c) ≫ Cover.val (gval c j.1) = Cover.val (gval i.1 j.1) := by
          rw [← val_comp, gval_mul hpar ((hPR e).trans h6) h5]
        have hsig : (⟨(pt S c).y, Cover.val (gval i.1 c)⟩ : Σ z, (pt S i.1).y ⟶ z) ≠
            ⟨(pt S j.1).y, Cover.val (gval i.1 j.1)⟩ := by
          intro h
          have hkey : ∀ (g : pt S i.1 ⟶ pt S c) (g' : pt S i.1 ⟶ pt S j.1), g ≠ 0 → g' ≠ 0 →
              (⟨(pt S c).y, Cover.val g⟩ : Σ z, (pt S i.1).y ⟶ z) =
                ⟨(pt S j.1).y, Cover.val g'⟩ → pt S c = pt S j.1 := by
            rintro (_ | f) (_ | f') h8 h9 h10
            · exact absurd rfl h8
            · exact absurd rfl h8
            · exact absurd rfl h9
            · obtain ⟨h11, h12⟩ := Sigma.mk.inj h10
              exact target_eq f f' h11 h12
          have hc0 : gval i.1 c ≠ 0 := by
            intro h0
            apply hg
            rw [← gval_mul hpar ((hPR e).trans h6) h5, h0, zero_comp]
          exact hcb (Subtype.ext (hkey _ _ hc0 hg h))
        refine hw.2.2 _ _ _ hcomp hsig ⟨_, _, fst_of_arrow hpar e.2.1 h6,
          fst_of_arrow hpar e'.2.1 h7, fun h ↦ hne3 ?_⟩
        exact locInj_arrow hpar hS (e.2.1.trans e'.2.1.symm) h
      two := ⟨⟨e₁, he₁, he₁'⟩, ⟨e₂, he₂, he₂'⟩, fun h ↦ hne12 (congrArg Subtype.val h)⟩ }
  exact ⟨κ, Fintype.ofFinite _, Classical.decEq _, B, rfl, rfl⟩

end Branch

end Piece

end LargeIndecomposable.RayCat
