module

public import LargeIndecomposable.Coverings.Pieces.PieceCover
public import LargeIndecomposable.FundamentalGroups.Fischbacher.SepDual

/-!
# Separation of piece points from the cover

Every arrow of a piece is nonzero in the piece algebra (`parr_arrow`), so piece paths run along
the arrows of `pieceDirData`.
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

include hpar in
/-- **Every arrow of a piece is nonzero in the piece algebra.** -/
lemma parr_arrow (α : (pieceQuiver S).A) :
    PArr (k := k) ((pieceQuiver S).src α) ((pieceQuiver S).tgt α) := by
  refine ⟨α, rfl, rfl, ?_⟩
  have h := pmk_word_ne_zero (k := k) (x := (pieceQuiver S).src α) hpar (l := [α])
    (List.cons_ne_nil _ _) ⟨rfl, rfl⟩ (by rw [compD_single]; exact α.2.2.2.1)
  change pmk (k := k) (1 * arrow k (pieceQuiver S) α) ≠ 0 at h
  rwa [one_mul] at h

include hpar in
lemma rtg_of_path : ∀ (le : List (pieceQuiver S).A) {i j : (pieceQuiver S).V},
    PathFrom i le j → Relation.ReflTransGen (PArr (k := k) (S := S)) i j
  | [], i, j, h => by change i = j at h; subst h; exact Relation.ReflTransGen.refl
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    exact Relation.ReflTransGen.head (parr_arrow hpar e) (rtg_of_path le h2)

variable (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] →
  ¬PathFrom i l i) {x : (pieceQuiver S).V}

include hacyc in
lemma mem_qset_of_tg {z : (pieceQuiver S).V} (h : Relation.TransGen (PArr (k := k) (S := S)) x z) :
    z ∈ (pieceDirData (k := k) hacyc).QSet x :=
  ⟨Set.mem_univ _, (pieceDirData (k := k) hacyc).acyc x z h⟩

include hpar hacyc in
/-- Successors of `x` along a piece path are connected among the non-predecessors of `x`. -/
lemma conn_of_path_from : ∀ (w : List (pieceQuiver S).A) {a b : (pieceQuiver S).V},
    Relation.TransGen (PArr (k := k) (S := S)) x a → PathFrom a w b →
      (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x) a b
  | [], a, b, _, h => by change a = b at h; subst h; exact Relation.ReflTransGen.refl
  | e :: w, a, b, ha, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = a at h1
    subst h1
    have he := parr_arrow (k := k) hpar e
    have ht : Relation.TransGen (PArr (k := k) (S := S)) x ((pieceQuiver S).tgt e) := ha.tail he
    exact Relation.ReflTransGen.head ⟨mem_qset_of_tg hacyc ha, mem_qset_of_tg hacyc ht, Or.inl he⟩
      (conn_of_path_from w ht h2)

include hpar hacyc in
/-- **The first arrow towards a point reached from `x`.** -/
lemma first_arrow {u : (pieceQuiver S).V} (hu : RPt x u) :
    ∃ α : (pieceQuiver S).A, (pieceQuiver S).src α = x ∧ (pieceQuiver S).tgt α ≠ x ∧
      Cl x ((pieceQuiver S).tgt α) u ∧
      (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x)
        ((pieceQuiver S).tgt α) u := by
  obtain ⟨l, hl⟩ := exists_path_of_gval hu.2
  match l, hl with
  | [], hl => exact absurd (show x = u from hl).symm hu.1
  | α :: w, hl =>
    obtain ⟨h1, h2⟩ := hl
    change α.1 = x at h1
    subst h1
    have htx : (pieceQuiver S).tgt α ≠ α.1 := fun h ↦
      hacyc α.1 [α] (List.cons_ne_nil _ _) ⟨rfl, h⟩
    refine ⟨α, rfl, htx, ?_, conn_of_path_from (k := k) hpar hacyc w
      (Relation.TransGen.single (parr_arrow hpar α)) h2⟩
    refine Relation.EqvGen.rel _ _ ⟨htx, hu.1, w, h2, ?_⟩
    have h3 : gval α.1 u = gval α.1 ((pieceQuiver S).tgt α) ≫ compD S w _ u h2 :=
      gval_append hpar (l := [α]) ⟨rfl, rfl⟩ h2
    rw [← h3]
    exact hu.2

variable (x) in
/-- The cover set `{x} ∪ (non-predecessors of x)`. -/
def coverD : Set (Cover x₀) :=
  {c | ∃ y : (pieceQuiver S).V, (y ∈ (pieceDirData (k := k) hacyc).QSet x ∨ y = x) ∧ c = pt S y}

open Classical in
/-- The piece point of a cover object. -/
def ptOf (x : (pieceQuiver S).V) (c : Cover x₀) : (pieceQuiver S).V :=
  if h : c ∈ S then (⟨c, h⟩ : S) else x

omit [Fintype P] [DecidableEq P] in
lemma ptOf_pt (y : (pieceQuiver S).V) : ptOf x (pt S y) = y := by
  unfold ptOf
  exact (dif_pos y.2).trans rfl

include hpar in
/-- Nonzero cover morphisms between piece points are composites from `x`. -/
lemma gval_of_cover (hS : Convex (S : Set (Cover x₀))) {w : (pieceQuiver S).V}
    (f : pt S x ⟶ pt S w) (hf : f ≠ 0) : gval x w = f := by
  obtain ⟨p, hp⟩ := exists_path f hf
  obtain ⟨le, hle, he⟩ := piece_of_cover_path hS x p w.2
  exact (gval_eq hpar hle).trans (he.trans hp)

include hpar in
lemma ext_of_cover (hS : Convex (S : Set (Cover x₀))) {a b : (pieceQuiver S).V}
    (fa : pt S x ⟶ pt S a) (hfa : fa ≠ 0) (h : pt S a ⟶ pt S b) (hb : fa ≫ h ≠ 0) :
    Ext x a b := by
  have hh : h ≠ 0 := fun h0 ↦ hb (by rw [h0, Limits.comp_zero])
  obtain ⟨p, hp⟩ := exists_path h hh
  obtain ⟨le, hle, he⟩ := piece_of_cover_path hS a p b.2
  refine ⟨le, hle, ?_⟩
  rw [gval_of_cover hpar hS fa hfa]
  erw [he, hp]
  exact hb

include hpar hacyc in
lemma coverD_convex (hS : Convex (S : Set (Cover x₀))) : ConvexR (coverD (k := k) hacyc x) := by
  rintro c ⟨y1, hy1, rfl⟩ d ⟨y2, -, rfl⟩ z ⟨p⟩ ⟨q⟩
  have hz : z ∈ S := hS _ _ _ y1.2 y2.2 (reach_of_path p) (reach_of_path q)
  let w : (pieceQuiver S).V := ⟨z, hz⟩
  refine ⟨w, ?_, rfl⟩
  obtain ⟨le, hle, -⟩ := piece_of_cover_path hS y1 p hz
  have h1 : Relation.ReflTransGen (PArr (k := k) (S := S)) y1 w := rtg_of_path hpar le hle
  by_cases hw : w = x
  · exact Or.inr hw
  refine Or.inl ⟨Set.mem_univ _, fun hwx ↦ ?_⟩
  rcases hy1 with hy1 | rfl
  · exact hy1.2 (h1.trans hwx)
  · exact (pieceDirData (k := k) hacyc).acyc y1 w
      ((pieceDirData (k := k) hacyc).transGen_of_ne h1 (Ne.symm hw)) hwx

include hpar in
lemma coverD_min : ∀ {y : RayVert (Cover x₀)} (_ : y ⟶ RayVert.mk (pt S x)),
    y.out ∉ coverD (k := k) hacyc x := by
  intro y e hy
  obtain ⟨w, hw, hyw⟩ := hy
  change (y : Cover x₀) = pt S w at hyw
  subst hyw
  let α : (pieceQuiver S).A := ⟨w, x, e.1, e.2⟩
  have hα := parr_arrow (k := k) hpar α
  rcases hw with hw | rfl
  · exact hw.2 (Relation.ReflTransGen.single hα)
  · exact hacyc w [α] (List.cons_ne_nil _ _) ⟨rfl, rfl⟩

lemma adjOff_of_conn {D : Set (Cover x₀)}
    (hqD : ∀ y, y ∈ (pieceDirData (k := k) hacyc).QSet x → pt S y ∈ D ∧ pt S y ≠ pt S x)
    {a b : (pieceQuiver S).V}
    (h : (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x) a b) :
    Relation.EqvGen (AdjOff D (pt S x)) (pt S a) (pt S b) := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc', hbc'⟩ := hbc
    refine Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨(hqD b hb).1, (hqD c hc').1,
      (hqD b hb).2, (hqD c hc').2, ?_⟩)
    rcases hbc' with ⟨β, h1, h2, -⟩ | ⟨β, h1, h2, -⟩
    · subst h1 h2
      exact Or.inl ⟨⟨β.2.2.1, β.2.2.2⟩⟩
    · subst h1 h2
      exact Or.inr ⟨⟨β.2.2.1, β.2.2.2⟩⟩

include hpar hacyc in
/-- **Connected among the non-predecessors of `x` implies one class**, by the separation
criterion on the cover. -/
theorem cl_of_conn (hS : Convex (S : Set (Cover x₀))) (hlsc : CoverLocalSC x₀) :
    ∀ u v, RPt x u → RPt x v →
      (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x) u v → Cl x u v := by
  classical
  intro u v hu hv hc
  obtain ⟨α₁, hs₁, hne₁, hcl₁, hcn₁⟩ := first_arrow (k := k) hpar hacyc hu
  obtain ⟨α₂, hs₂, hne₂, hcl₂, hcn₂⟩ := first_arrow (k := k) hpar hacyc hv
  let t₁ := (pieceQuiver S).tgt α₁
  let t₂ := (pieceQuiver S).tgt α₂
  have hconn : (pieceDirData (k := k) hacyc).Conn ((pieceDirData (k := k) hacyc).QSet x) t₁ t₂ :=
    hcn₁.trans (hc.trans (AR.DirData.conn_symm hcn₂))
  let D := coverD (k := k) hacyc x
  have hDfin : D.Finite := (Set.finite_range (fun y : (pieceQuiver S).V ↦ pt S y)).subset
    fun c ⟨y, _, hcy⟩ ↦ ⟨y, hcy.symm⟩
  have hxD : pt S x ∈ D := ⟨x, Or.inr rfl, rfl⟩
  have hqD : ∀ y, y ∈ (pieceDirData (k := k) hacyc).QSet x → pt S y ∈ D ∧ pt S y ≠ pt S x :=
    fun y hy ↦ ⟨⟨y, Or.inl hy, rfl⟩, fun h ↦ hy.2 (by
      rw [show y = x from Subtype.ext h]; exact Relation.ReflTransGen.refl)⟩
  have hadj : Relation.EqvGen (AdjOff D (pt S x)) (pt S t₁) (pt S t₂) :=
    adjOff_of_conn hacyc hqD hconn
  have ht₁ : t₁ ∈ (pieceDirData (k := k) hacyc).QSet x :=
    mem_qset_of_tg hacyc (Relation.TransGen.single (hs₁ ▸ parr_arrow hpar α₁))
  have ht₂ : t₂ ∈ (pieceDirData (k := k) hacyc).QSet x :=
    mem_qset_of_tg hacyc (Relation.TransGen.single (hs₂ ▸ parr_arrow hpar α₂))
  have e₁ : RayVert.mk (pt S x) ⟶ RayVert.mk (pt S t₁) := hs₁ ▸ ⟨α₁.2.2.1, α₁.2.2.2⟩
  have e₂ : RayVert.mk (pt S x) ⟶ RayVert.mk (pt S t₂) := hs₂ ▸ ⟨α₂.2.2.1, α₂.2.2.2⟩
  have hout := outComp_of_coboundary hxD (coverD_min (k := k) hpar hacyc)
    (hlsc D hDfin (coverD_convex (k := k) hpar hacyc hS)) e₁ e₂ (hqD t₁ ht₁).1 (hqD t₂ ht₂).1
    (hqD t₁ ht₁).2 (hqD t₂ ht₂).2 hadj
  -- back to classes
  have hle : ∀ f g, OutLe D (pt S x) f g → Cl x (ptOf x f.1) (ptOf x g.1) := by
    rintro ⟨c, m⟩ ⟨d, m'⟩ ⟨hm, hm', ⟨y, hy, rfl⟩, ⟨y', hy', rfl⟩, hyx, hy'x, h, hh⟩
    rw [ptOf_pt, ptOf_pt]
    refine Relation.EqvGen.rel _ _ ⟨fun e ↦ hyx (congrArg (pt S) e),
      fun e ↦ hy'x (congrArg (pt S) e), ?_⟩
    exact ext_of_cover hpar hS m hm h (by rw [← hh]; exact hm')
  have hcl : Cl x (ptOf x (pt S t₁)) (ptOf x (pt S t₂)) := by
    have key : ∀ f g, OutComp D (pt S x) f g → Cl x (ptOf x f.1) (ptOf x g.1) := by
      intro f g h
      induction h with
      | rel f g h => exact hle f g h
      | refl => exact Relation.EqvGen.refl _
      | symm f g _ ih => exact cl_symm ih
      | trans f g h' _ _ ih1 ih2 => exact cl_trans ih1 ih2
    exact key _ _ hout
  rw [ptOf_pt, ptOf_pt] at hcl
  exact cl_trans (cl_symm hcl₁) (cl_trans hcl hcl₂)

omit hpar in
/-- **Pieces have preprojective components**: a nonempty convex piece of an acyclic,
interval-finite, locally simply connected cover has a preprojective component. -/
theorem piece_preprojComp (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀) :
    ∃ 𝒞 : AR.FDMod k (PieceAlg k S) → Prop, AR.PreprojComp 𝒞 := by
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  obtain ⟨a, ha⟩ := hne
  refine AR.DirData.exists_preprojComp _ (pieceDirData (k := k) hacyc)
    (fun z ↦ radDecomp (x := z) hpar hacyc)
    (fun z _ ↦ sepDecomp_radDecomp hpar hacyc (cl_of_conn hpar hacyc hS hlsc)) le_rfl
    ⟨⟨a, ha⟩, Set.mem_univ _⟩

end LargeIndecomposable.RayCat
