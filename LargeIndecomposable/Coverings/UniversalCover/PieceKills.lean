module

public import LargeIndecomposable.Coverings.UniversalCover.CoverPiece
public import LargeIndecomposable.RayCategories.Linearization.RegularRepresentation
public import LargeIndecomposable.Quivers.PathAlgebras.WordSum

/-!
# Push-downs from convex pieces of the universal cover

Let `S` be a finite convex set of objects of the universal cover `P̃` of a
finite ray category `P`, and `X` a representation of the piece `D_S` that
satisfies the relations of `P̃` (paths with zero composite act by zero, paths
with the same composite act equally). Then the push-down `p_*X` is a module
over the linearization `k(P)` (`RayCat.pdAct_eq_zero_of_linPres`): every
relation of `k(P)` lifts along `P̃ → P` to relations of `P̃` from each start
point, and convexity keeps the lifts inside `S`. This is the `kills` condition
of covering data with a Kronecker pair.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayCat

namespace Cover

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- A morphism of the cover whose value is invertible is invertible. -/
lemma isIso_of_isIso_val {a b : Cover x₀} (g : a ⟶ b) (hg : IsIso (val g)) : IsIso g := by
  obtain ⟨hy, he⟩ := eq_eqToHom_of_isIso (val g)
  obtain ⟨y, u⟩ := a
  obtain ⟨y', u'⟩ := b
  change y = y' at hy
  subst hy
  have h1 : val g = 𝟙 y := he
  rcases g with _ | g
  · exact absurd h1.symm (IsRayCategory.id_ne_zero y)
  obtain ⟨hg0, hgu⟩ := g.2
  have hu : u' = u := by
    have : u' = u ≫ cls g.1 hg0 := hgu
    rw [this, show cls g.1 hg0 = cls (𝟙 y) (IsRayCategory.id_ne_zero y) by congr 1, cls_id,
      Category.comp_id]
  subst hu
  have : (some g : (⟨y, u'⟩ : Cover x₀) ⟶ ⟨y, u'⟩) = 𝟙 (⟨y, u'⟩ : Cover x₀) :=
    val_injective (h1.trans (val_id (⟨y, u'⟩ : Cover x₀)).symm)
  rw [this]
  infer_instance

/-- The lift of an irreducible morphism is irreducible. -/
theorem isIrreducible_liftAt (a : Cover x₀) {z : P} {f : a.y ⟶ z} (hf : IsIrreducible f) :
    IsIrreducible (liftAt a f hf.1) := by
  refine ⟨fun h ↦ Option.some_ne_none _ h, fun hiso ↦ ?_, fun c g h hgh ↦ ?_⟩
  · exact hf.2.1 (isIso_val (liftAt a f hf.1))
  · have := congrArg val hgh
    rw [val_comp, val_liftAt] at this
    rcases hf.2.2 _ _ _ this with h1 | h1
    · exact Or.inl (isIso_of_isIso_val g h1)
    · exact Or.inr (isIso_of_isIso_val h h1)

/-- Reachability along irreducible morphisms (paths of the quiver of the cover). -/
inductive Reach : Cover x₀ → Cover x₀ → Prop
  | refl (a : Cover x₀) : Reach a a
  | step {a b c : Cover x₀} (f : a ⟶ b) (hf : IsIrreducible f) : Reach b c → Reach a c

/-- A set of objects of the cover is convex (closed under paths between its points). -/
def Convex (S : Set (Cover x₀)) : Prop :=
  ∀ a b c, a ∈ S → c ∈ S → Reach a b → Reach b c → b ∈ S

end Cover

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

omit [Fintype P] [DecidableEq P] in
lemma cls_congr {y z : P} {f g : y ⟶ z} (h : f = g) (hf : f ≠ 0) (hg : g ≠ 0) :
    cls f hf = cls g hg := by
  subst h
  rfl

/-- The lift of a path of `Q_P` with nonzero composite reaches the expected object. -/
lemma reach_lift : ∀ (l : List (quiver P).A) (a : Cover x₀) (y : P)
    (h : PathFrom (D := quiver P) a.y l y) (hne : pathMor l a.y y h ≠ 0),
    Reach a ⟨y, a.u ≫ cls (pathMor l a.y y h) hne⟩
  | [], a, y, h, hne => by
    obtain ⟨y0, u⟩ := a
    change y0 = y at h
    subst h
    have : cls (pathMor [] y0 y0 rfl) hne = 𝟙 _ := by
      rw [show cls (pathMor [] y0 y0 rfl) hne = cls (𝟙 y0) (IsRayCategory.id_ne_zero y0) by
        congr 1]
      exact cls_id y0
    rw [this, Category.comp_id]
    exact Reach.refl _
  | c :: l, a, y, h, hne => by
    obtain ⟨x1, z1, f, hf⟩ := c
    obtain ⟨h1, h2⟩ := h
    change x1 = a.y at h1
    obtain ⟨ay, au⟩ := a
    change x1 = ay at h1
    subst h1
    have hpm : pathMor (⟨x1, z1, f, hf⟩ :: l) x1 y ⟨rfl, h2⟩ = f ≫ pathMor l z1 y h2 := by
      simp [pathMor]
    have hne' : f ≫ pathMor l z1 y h2 ≠ 0 := hpm ▸ hne
    have hl0 : pathMor l z1 y h2 ≠ 0 := fun h0 ↦ hne' (by rw [h0, comp_zero])
    have := reach_lift l ⟨z1, au ≫ cls f hf.1⟩ y h2 hl0
    have e : (⟨y, au ≫ cls (pathMor (⟨x1, z1, f, hf⟩ :: l) x1 y ⟨rfl, h2⟩) hne⟩ : Cover x₀) =
        ⟨y, (au ≫ cls f hf.1) ≫ cls (pathMor l z1 y h2) hl0⟩ := by
      congr 1
      rw [Category.assoc, ← cls_comp f _ hne']
      rw [cls_congr hpm hne hne']
    rw [e]
    exact Reach.step (liftAt (⟨x1, au⟩ : Cover x₀) f hf.1)
      (isIrreducible_liftAt (⟨x1, au⟩ : Cover x₀) hf) this

lemma u_eq_of_ne_zero {a b : Cover x₀} (f : a ⟶ b) (hf : f ≠ 0) (hv : val f ≠ 0) :
    b.u = a.u ≫ cls (val f) hv := by
  rcases f with _ | f
  · exact absurd rfl hf
  obtain ⟨h0, hu⟩ := f.2
  exact hu

section Piece

variable (S : Finset (Cover x₀))

/-- The object of the cover at a vertex of the piece. -/
abbrev pt (i : (pieceQuiver S).V) : Cover x₀ := (show S from i).1

/-- The composite in the cover of a path of the piece. -/
def compD : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V),
    PathFrom i le j → (pt S i ⟶ pt S j)
  | [], _, _, h => eqToHom (congrArg (pt S) h)
  | e :: le, _, j, h => eqToHom (congrArg (pt S) h.1.symm) ≫ e.2.2.1 ≫ compD le _ j h.2

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma pathFrom_map {D Q : FinQuiver} (p : FinQuiver.Hom D Q) : ∀ (le : List D.A) (i j : D.V),
    PathFrom i le j → PathFrom (p.vert i) (le.map p.arr) (p.vert j)
  | [], _, _, h => congrArg p.vert h
  | e :: le, _, j, h => ⟨by rw [p.map_src, h.1], (p.map_tgt e) ▸ pathFrom_map p le _ j h.2⟩

lemma val_compD : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : PathFrom i le j),
    val (compD S le i j h) = pathMor (le.map (pieceProj S).arr) (pt S i).y (pt S j).y
      (pathFrom_map (pieceProj S) le i j h)
  | [], i, j, h => by
    change i = j at h
    subst h
    rfl
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    change val (eqToHom _ ≫ e.2.2.1 ≫ compD S le _ j h2) = _
    rw [val_comp, val_comp]
    erw [val_compD le _ j h2]
    rfl

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
/-- Locally injective morphisms have unique path lifts from a given start. -/
lemma lift_unique {D Q : FinQuiver} {p : FinQuiver.Hom D Q} (hinj : p.LocallyInjective) :
    ∀ (le le' : List D.A) (i j j' : D.V), le.map p.arr = le'.map p.arr →
      PathFrom i le j → PathFrom i le' j' → le = le'
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | e :: le, e' :: le', i, j, j', h, hp, hp' => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hee : e = e' := hinj.1 e e' (hp.1.trans hp'.1.symm) h.1
    subst hee
    rw [lift_unique hinj le le' _ j j' h.2 hp.2 hp'.2]

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
/-- The endpoints of a nonempty path are determined by its arrows. -/
lemma pathFrom_ends {D : FinQuiver} : ∀ (l : List D.A) (x y x' y' : D.V), l ≠ [] →
    PathFrom x l y → PathFrom x' l y' → x = x' ∧ y = y'
  | [], _, _, _, _, h, _, _ => absurd rfl h
  | [_], _, _, _, _, _, h, h' => ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩
  | _ :: c' :: l, _, y, _, y', _, h, h' =>
    ⟨h.1.symm.trans h'.1, (pathFrom_ends (c' :: l) _ y _ y' (List.cons_ne_nil _ _) h.2 h'.2).2⟩

variable {S}

/-- Lifts of paths with nonzero composite stay in a convex piece. -/
lemma exists_lift_piece (hS : Convex (S : Set (Cover x₀))) :
    ∀ (l : List (quiver P).A) (i : (pieceQuiver S).V) (y : P)
      (h : PathFrom (D := quiver P) (pt S i).y l y) (hne : pathMor l (pt S i).y y h ≠ 0),
      (⟨y, (pt S i).u ≫ cls (pathMor l (pt S i).y y h) hne⟩ : Cover x₀) ∈ S →
      ∃ (le : List (pieceQuiver S).A) (j : (pieceQuiver S).V), le.map (pieceProj S).arr = l ∧
        PathFrom i le j ∧ pt S j = ⟨y, (pt S i).u ≫ cls (pathMor l (pt S i).y y h) hne⟩
  | [], i, y, h, hne, _ => by
    refine ⟨[], i, rfl, rfl, ?_⟩
    obtain ⟨⟨y0, u⟩, hi⟩ := i
    change y0 = y at h
    subst h
    have : cls (pathMor [] y0 y0 rfl) hne = 𝟙 _ := by
      rw [show cls (pathMor [] y0 y0 rfl) hne = cls (𝟙 y0) (IsRayCategory.id_ne_zero y0) by
        congr 1]
      exact cls_id y0
    change (⟨y0, u⟩ : Cover x₀) = ⟨y0, u ≫ cls (pathMor [] y0 y0 rfl) hne⟩
    rw [this, Category.comp_id]
  | c :: l, i, y, h, hne, hj => by
    obtain ⟨x1, z1, f, hf⟩ := c
    obtain ⟨⟨ay, au⟩, hi⟩ := i
    obtain ⟨h1, h2⟩ := h
    change x1 = ay at h1
    subst h1
    have hpm : pathMor (⟨x1, z1, f, hf⟩ :: l) x1 y ⟨rfl, h2⟩ = f ≫ pathMor l z1 y h2 := by
      simp [pathMor]
    have hne' : f ≫ pathMor l z1 y h2 ≠ 0 := hpm ▸ hne
    have hl0 : pathMor l z1 y h2 ≠ 0 := fun h0 ↦ hne' (by rw [h0, comp_zero])
    have e : (⟨y, au ≫ cls (pathMor (⟨x1, z1, f, hf⟩ :: l) x1 y ⟨rfl, h2⟩) hne⟩ : Cover x₀) =
        ⟨y, (au ≫ cls f hf.1) ≫ cls (pathMor l z1 y h2) hl0⟩ := by
      congr 1
      rw [Category.assoc, ← cls_comp f _ hne', cls_congr hpm hne hne']
    change (⟨y, au ≫ cls (pathMor (⟨x1, z1, f, hf⟩ :: l) x1 y ⟨rfl, h2⟩) hne⟩ : Cover x₀) ∈ S
      at hj
    rw [e] at hj
    have ha' : (⟨z1, au ≫ cls f hf.1⟩ : Cover x₀) ∈ S :=
      hS _ _ _ hi hj (Reach.step (liftAt (⟨x1, au⟩ : Cover x₀) f hf.1)
        (isIrreducible_liftAt (⟨x1, au⟩ : Cover x₀) hf) (Reach.refl _))
        (reach_lift l ⟨z1, au ≫ cls f hf.1⟩ y h2 hl0)
    obtain ⟨le, j, hmap, hpath, hpt⟩ := exists_lift_piece hS l ⟨⟨z1, au ≫ cls f hf.1⟩, ha'⟩ y h2 hl0 hj
    refine ⟨⟨⟨⟨x1, au⟩, hi⟩, ⟨⟨z1, au ≫ cls f hf.1⟩, ha'⟩, ⟨liftAt (⟨x1, au⟩ : Cover x₀) f hf.1,
      isIrreducible_liftAt (⟨x1, au⟩ : Cover x₀) hf⟩⟩ :: le, j, ?_, ⟨rfl, hpath⟩, ?_⟩
    · change (pieceProj S).arr _ :: List.map (pieceProj S).arr le = _
      rw [hmap]
      rfl
    · rw [hpt]
      exact e.symm

end Piece

section Blocks

variable {k : Type*} [Field k] {D : FinQuiver} (X : Rep k D)

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma idm_idm_apply (i : D.V) (v : X.Tot) : X.idm i (X.idm i v) = X.idm i v :=
  LinearMap.congr_fun (X.idm_idm i) v

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma pathTot_blocks : ∀ (le : List D.A) (i j : D.V), PathFrom i le j → le ≠ [] →
    X.pathTot le = X.idm j ∘ₗ X.pathTot le ∘ₗ X.idm i
  | [], _, _, _, h => absurd rfl h
  | [e], i, j, h, _ => by
    obtain ⟨h1, h2⟩ := h
    change D.tgt e = j at h2
    subst h1 h2
    simp only [Rep.pathTot, LinearMap.id_comp]
    rw [X.arrOp_comp_idm, if_pos rfl]
    exact X.arrOp_eq_idm_comp e
  | e :: e' :: le, i, j, h, _ => by
    obtain ⟨h1, h2⟩ := h
    subst h1
    have ih := pathTot_blocks (e' :: le) _ j h2 (List.cons_ne_nil _ _)
    change X.pathTot (e' :: le) ∘ₗ X.arrOp e = X.idm j ∘ₗ (X.pathTot (e' :: le) ∘ₗ X.arrOp e) ∘ₗ
      X.idm (D.src e)
    rw [ih]
    simp only [LinearMap.comp_assoc]
    rw [X.arrOp_comp_idm, if_pos rfl]
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, idm_idm_apply]

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
open Classical in
lemma blk_pathTot (le : List D.A) {i0 j0 : D.V} (h : PathFrom i0 le j0) (hne : le ≠ []) (i j : D.V) :
    X.idm j ∘ₗ X.pathTot le ∘ₗ X.idm i = if PathFrom i le j then X.pathTot le else 0 := by
  rw [pathTot_blocks X le i0 j0 h hne]
  by_cases hp : PathFrom i le j
  · obtain ⟨rfl, rfl⟩ := pathFrom_ends le i0 j0 i j hne h hp
    rw [if_pos hp]
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, idm_idm_apply]
  · rw [if_neg hp]
    by_cases hi : i0 = i
    · subst hi
      have hj : j0 ≠ j := fun e ↦ hp (e ▸ h)
      rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, X.idm_comp_idm, if_neg (Ne.symm hj),
        LinearMap.zero_comp, LinearMap.zero_comp]
    · rw [LinearMap.comp_assoc, LinearMap.comp_assoc, X.idm_comp_idm, if_neg hi,
        LinearMap.comp_zero, LinearMap.comp_zero, LinearMap.comp_zero]

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
open Classical in
lemma blk_term (le : List D.A) (hne : le ≠ []) (i j : D.V) :
    X.idm j ∘ₗ X.pathTot le ∘ₗ X.idm i = if PathFrom i le j then X.pathTot le else 0 := by
  by_cases hc : ∃ i0 j0, PathFrom i0 le j0
  · obtain ⟨i0, j0, h⟩ := hc
    exact blk_pathTot X le h hne i j
  · push Not at hc
    rw [Rep.pathTot_eq_zero X le hc hne, if_neg (hc i j), LinearMap.zero_comp,
      LinearMap.comp_zero]

end Blocks

lemma pathMor_congr {l l' : List (quiver P).A} (hl : l = l') {x y : P}
    (h : PathFrom (D := quiver P) x l y) (h' : PathFrom (D := quiver P) x l' y) :
    pathMor l x y h = pathMor l' x y h' := by
  subst hl
  rfl

section Main

variable {k : Type*} [Field k] {S : Finset (Cover x₀)}

/-- A representation of the piece satisfies the relations of the cover. -/
def RespectsCover (X : Rep k (pieceQuiver S)) : Prop :=
  (∀ le i j (h : PathFrom i le j), compD S le i j h = 0 → X.pathTot le = 0) ∧
    ∀ le le' i j (h : PathFrom i le j) (h' : PathFrom i le' j),
      compD S le i j h = compD S le' i j h' → X.pathTot le = X.pathTot le'

open Classical in
lemma blk_word (X : Rep k (pieceQuiver S)) (l : List (quiver P).A) (hl : l ≠ [])
    (i j : (pieceQuiver S).V) :
    X.idm j ∘ₗ X.pdAct (pieceProj S) (word k (quiver P) l) ∘ₗ X.idm i =
      ∑ le ∈ (Rep.lab (pieceProj S) l).filter (fun le ↦ PathFrom i le j), X.pathTot le := by
  rw [Rep.pdAct_word_eq_sum, finsetSum_comp, comp_finsetSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun le hle ↦ ?_
  have hmap := (Rep.mem_lab _ _ _).1 hle
  have hne : le ≠ [] := by rintro rfl; exact hl hmap.symm
  exact blk_term X le hne i j

/-- Paths of the piece over a path with zero composite act by zero. -/
lemma pathTot_eq_zero_of_zero {X : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    {l : List (quiver P).A} {x y : P} {h : PathFrom (D := quiver P) x l y}
    (h0 : pathMor l x y h = 0) (hl : l ≠ []) {le : List (pieceQuiver S).A}
    (hle : le.map (pieceProj S).arr = l) {i j : (pieceQuiver S).V} (hp : PathFrom i le j) :
    X.pathTot le = 0 := by
  apply hX.1 le i j hp
  rw [← val_eq_zero_iff, val_compD]
  have hp' := pathFrom_map (pieceProj S) le i j hp
  obtain ⟨hx, hy⟩ := pathFrom_ends l x y _ _ hl h (hle ▸ hp')
  subst hx hy
  exact (pathMor_congr hle _ h).trans h0

/-- A lift of one path is matched by a lift of a parallel path with the same
nonzero composite. -/
lemma exists_partner (hS : Convex (S : Set (Cover x₀))) {X : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) {l l' : List (quiver P).A} {x y : P}
    {h : PathFrom (D := quiver P) x l y} {h' : PathFrom (D := quiver P) x l' y}
    (he : pathMor l x y h = pathMor l' x y h') (hν : pathMor l x y h ≠ 0) (hl : l ≠ [])
    {le : List (pieceQuiver S).A} (hle : le.map (pieceProj S).arr = l)
    {i j : (pieceQuiver S).V} (hp : PathFrom i le j) :
    ∃ le' : List (pieceQuiver S).A, le'.map (pieceProj S).arr = l' ∧ PathFrom i le' j ∧
      X.pathTot le = X.pathTot le' := by
  have hp' := pathFrom_map (pieceProj S) le i j hp
  obtain ⟨hx, hy⟩ := pathFrom_ends l x y _ _ hl h (hle ▸ hp')
  subst hx hy
  have hv : val (compD S le i j hp) = pathMor l _ _ h :=
    (val_compD S le i j hp).trans (pathMor_congr hle _ h)
  have hν' : pathMor l' _ _ h' ≠ 0 := he ▸ hν
  have hc0 : compD S le i j hp ≠ 0 := fun h0 ↦ hν (hv.symm.trans (by rw [h0]; rfl))
  have hu := u_eq_of_ne_zero _ hc0 (hv ▸ hν)
  have hT : (⟨(pt S j).y, (pt S i).u ≫ cls (pathMor l' _ _ h') hν'⟩ : Cover x₀) = pt S j := by
    show _ = (⟨(pt S j).y, (pt S j).u⟩ : Cover x₀)
    congr 1
    rw [hu, cls_congr (hv.trans he) _ hν']
    rfl
  obtain ⟨le', j', hmap', hp'', hpt⟩ := exists_lift_piece hS l' i _ h' hν'
    (hT ▸ (show S from j).2)
  have hj : j' = j := Subtype.ext (hpt.trans hT)
  subst hj
  refine ⟨le', hmap', hp'', hX.2 le le' i j' hp hp'' (val_injective ?_)⟩
  rw [hv, he]
  exact ((val_compD S le' i j' hp'').trans (pathMor_congr hmap' _ h')).symm

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma sum_eq_of_match {α M : Type*} [AddCommMonoid M] {F F' : Finset α} {f g : α → M}
    (hc : F.card ≤ 1) (hc' : F'.card ≤ 1) (h : ∀ a ∈ F, ∃ b ∈ F', f a = g b)
    (h' : ∀ b ∈ F', ∃ a ∈ F, g b = f a) : ∑ a ∈ F, f a = ∑ b ∈ F', g b := by
  rcases F.eq_empty_or_nonempty with hF | ⟨a, ha⟩
  · have hF' : F' = ∅ := Finset.eq_empty_of_forall_notMem fun b hb ↦ by
      obtain ⟨a, ha, -⟩ := h' b hb
      simp [hF] at ha
    simp [hF, hF']
  · obtain ⟨b, hb, hab⟩ := h a ha
    rw [Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx ↦ Finset.card_le_one.1 hc x hx a ha⟩,
      Finset.eq_singleton_iff_unique_mem.2 ⟨hb, fun x hx ↦ Finset.card_le_one.1 hc' x hx b hb⟩,
      Finset.sum_singleton, Finset.sum_singleton, hab]

open Classical in
/-- The push-down of a representation respecting the relations of the cover
satisfies the relations of `k(P)`. -/
theorem pdAct_linRel (hS : Convex (S : Set (Cover x₀))) {X : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) {a b : (quiver P).PathAlgebra k} (hab : LinRel P k a b) :
    X.pdAct (pieceProj S) a = X.pdAct (pieceProj S) b := by
  have hinj := pieceProj_locInj S
  cases hab with
  | zero l x y h h0 =>
    rw [map_zero]
    rcases l with _ | ⟨c, l⟩
    · exfalso
      change x = y at h
      subst h
      exact IsRayCategory.id_ne_zero x h0
    · rw [Rep.pdAct_word_eq_sum]
      refine Finset.sum_eq_zero fun le hle ↦ ?_
      have hmap := (Rep.mem_lab _ _ _).1 hle
      have hne : le ≠ [] := by rintro rfl; simp at hmap
      by_cases hc : ∃ i j, PathFrom i le j
      · obtain ⟨i, j, hp⟩ := hc
        exact pathTot_eq_zero_of_zero hX h0 (List.cons_ne_nil _ _) hmap hp
      · push Not at hc
        exact Rep.pathTot_eq_zero X le hc hne
  | eq l l' x y h h' he =>
    rcases l with _ | ⟨c, l⟩ <;> rcases l' with _ | ⟨c', l'⟩
    · rfl
    · exfalso
      change x = y at h
      subst h
      exact pathMor_ne_id c' l' x h' he.symm
    · exfalso
      change x = y at h'
      subst h'
      exact pathMor_ne_id c l x h he
    · refine Rep.ext_blocks fun j i ↦ ?_
      rw [blk_word X _ (List.cons_ne_nil _ _), blk_word X _ (List.cons_ne_nil _ _)]
      by_cases hν : pathMor (c :: l) x y h = 0
      · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
        · intro le hle
          rw [Finset.mem_filter] at hle
          exact pathTot_eq_zero_of_zero hX (he ▸ hν) (List.cons_ne_nil _ _)
            ((Rep.mem_lab _ _ _).1 hle.1) hle.2
        · intro le hle
          rw [Finset.mem_filter] at hle
          exact pathTot_eq_zero_of_zero hX hν (List.cons_ne_nil _ _)
            ((Rep.mem_lab _ _ _).1 hle.1) hle.2
      · have hν' : pathMor (c' :: l') x y h' ≠ 0 := he ▸ hν
        refine sum_eq_of_match ?_ ?_ (fun le hle ↦ ?_) (fun le hle ↦ ?_)
        · refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
          rw [Finset.mem_filter, Rep.mem_lab] at ha hb
          exact lift_unique hinj a b i j j (ha.1.trans hb.1.symm) ha.2 hb.2
        · refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
          rw [Finset.mem_filter, Rep.mem_lab] at ha hb
          exact lift_unique hinj a b i j j (ha.1.trans hb.1.symm) ha.2 hb.2
        · rw [Finset.mem_filter, Rep.mem_lab] at hle
          obtain ⟨le', hm, hp, he'⟩ := exists_partner hS hX he hν (List.cons_ne_nil _ _) hle.1 hle.2
          exact ⟨le', by rw [Finset.mem_filter, Rep.mem_lab]; exact ⟨hm, hp⟩, he'⟩
        · rw [Finset.mem_filter, Rep.mem_lab] at hle
          obtain ⟨le', hm, hp, he'⟩ :=
            exists_partner hS hX he.symm hν' (List.cons_ne_nil _ _) hle.1 hle.2
          exact ⟨le', by rw [Finset.mem_filter, Rep.mem_lab]; exact ⟨hm, hp⟩, he'⟩

/-- **The push-down of a piece**: the push-down from a convex piece of a representation respecting the
relations of the cover is a module over `k(P)`. -/
theorem pdAct_eq_zero_of_linPres (hS : Convex (S : Set (Cover x₀)))
    {X : Rep k (pieceQuiver S)} (hX : RespectsCover X) (z : (quiver P).PathAlgebra k)
    (hz : linPres P k z = 0) : X.pdAct (pieceProj S) z = 0 := by
  let f : {f : (quiver P).PathAlgebra k →ₐ[k] Module.End k X.Tot //
      ∀ ⦃x y⦄, LinRel P k x y → f x = f y} :=
    ⟨X.pdAct (pieceProj S), fun _ _ h ↦ pdAct_linRel hS hX h⟩
  calc X.pdAct (pieceProj S) z = RingQuot.liftAlgHom k f (RingQuot.mkAlgHom k (LinRel P k) z) :=
        (RingQuot.liftAlgHom_mkAlgHom_apply k f.1 f.2 z).symm
    _ = 0 := by
      change RingQuot.liftAlgHom k f (linPres P k z) = 0
      rw [hz, map_zero]

end Main

end RayCat

end LargeIndecomposable
