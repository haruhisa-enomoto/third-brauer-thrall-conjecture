module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerGlue
public import LargeIndecomposable.AuslanderReiten.Lengths.FDMod
public import LargeIndecomposable.Quivers.PathAlgebras.PathSpan

/-!
# Relations of a piece in its path algebra

For a finite piece `S` of the universal cover, the relations of the cover are the elements
`w(l)` of the path algebra `k D_S` for paths `l` with zero composite and `w(l) - w(l')` for
parallel paths with equal composites (`relGens`). A representation respects the cover exactly when
these elements act by zero on its total space (`respectsCover_iff`): with the identity labelling a
word acts as its own path operator (`pdAct_id_word`). This is the first step of the bridge from
representations of pieces to modules over the piece algebra.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Covering

universe u

variable {k : Type u} [Field k] {D : FinQuiver}

namespace Rep

lemma lab_id : ∀ l : List D.A, lab (FinQuiver.Hom.id D) l = {l}
  | l => by
    ext le
    rw [mem_lab, Finset.mem_singleton]
    change le.map id = l ↔ le = l
    rw [List.map_id]

lemma pdAct_id_word (X : Rep k D) (l : List D.A) :
    X.pdAct (FinQuiver.Hom.id D) (FinQuiver.word k D l) = X.pathTot l := by
  rw [pdAct_word_eq_sum, lab_id, Finset.sum_singleton]

end Rep

namespace Rep

lemma pdVert_id (X : Rep k D) (q : D.V) : X.pdVert (FinQuiver.Hom.id D) q = X.idm q := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  rw [pdVert_apply, idm_apply]
  change (if i = q then x i else 0) = _
  by_cases h : i = q
  · subst h; simp
  · simp [h, Pi.single_eq_of_ne h]

lemma pdArr_id (X : Rep k D) (c : D.A) : X.pdArr (FinQuiver.Hom.id D) c = X.arrOp c := by
  unfold pdArr
  have : Finset.univ.filter (fun e : D.A ↦ (FinQuiver.Hom.id D).arr e = c) = {c} := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]; rfl
  rw [this, Finset.sum_singleton]

end Rep

namespace RayCat

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} (S : Finset (Cover x₀))

variable (k) in
/-- The relations of the cover in the path algebra of a piece. -/
def relGens : Set ((pieceQuiver S).PathAlgebra k) :=
  {r : (pieceQuiver S).PathAlgebra k | (∃ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
      (h : FinQuiver.PathFrom i le j), compD S le i j h = 0 ∧
      r = FinQuiver.word k (pieceQuiver S) le) ∨
    ∃ (le le' : List (pieceQuiver S).A) (i j : (pieceQuiver S).V) (h : FinQuiver.PathFrom i le j)
      (h' : FinQuiver.PathFrom i le' j),
      compD S le i j h = compD S le' i j h' ∧
        r = FinQuiver.word k (pieceQuiver S) le - FinQuiver.word k (pieceQuiver S) le'}

variable {S}

/-- **A representation respects the cover iff the relations act by zero.** -/
theorem respectsCover_iff (X : Rep k (pieceQuiver S)) :
    RespectsCover X ↔ ∀ r ∈ relGens k S, X.pdAct (FinQuiver.Hom.id _) r = 0 := by
  constructor
  · rintro ⟨h0, h1⟩ r (⟨le, i, j, h, hz, rfl⟩ | ⟨le, le', i, j, h, h', he, rfl⟩)
    · rw [Rep.pdAct_id_word]
      exact h0 le i j h hz
    · rw [map_sub, Rep.pdAct_id_word, Rep.pdAct_id_word, h1 le le' i j h h' he, sub_self]
  · intro hr
    refine ⟨fun le i j h hz ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
    · rw [← Rep.pdAct_id_word]
      exact hr _ (Or.inl ⟨le, i, j, h, hz, rfl⟩)
    · have := hr _ (Or.inr ⟨le, le', i, j, h, h', he, rfl⟩)
      rw [map_sub, Rep.pdAct_id_word, Rep.pdAct_id_word, sub_eq_zero] at this
      exact this

variable (k S) in
/-- The algebra of a piece: the path algebra modulo the relations of the cover. -/
abbrev PieceAlg : Type _ :=
  RingQuot (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)

/-- The action of the piece algebra on a representation respecting the cover. -/
def pieceAct (X : Rep k (pieceQuiver S)) (hX : RespectsCover X) :
    PieceAlg k S →ₐ[k] Module.End k X.Tot :=
  RingQuot.liftAlgHom k ⟨X.pdAct (FinQuiver.Hom.id _), fun a b ⟨ha, hb⟩ ↦ by
    rw [hb, map_zero]
    exact (respectsCover_iff X).1 hX a ha⟩

lemma pieceAct_mk (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)
    (a : (pieceQuiver S).PathAlgebra k) :
    pieceAct X hX (RingQuot.mkAlgHom k _ a) = X.pdAct (FinQuiver.Hom.id _) a := by
  simp [pieceAct]

/-- The total space of a representation respecting the cover, as a module over the piece
algebra. -/
def PieceMod (X : Rep k (pieceQuiver S)) (_hX : RespectsCover X) : Type u := X.Tot

namespace PieceMod

variable (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)

instance : AddCommGroup (PieceMod X hX) := inferInstanceAs (AddCommGroup X.Tot)

instance : Module k (PieceMod X hX) := inferInstanceAs (Module k X.Tot)

instance : Module (PieceAlg k S) (PieceMod X hX) :=
  Module.compHom X.Tot (pieceAct X hX).toRingHom

lemma smul_def (a : PieceAlg k S) (x : PieceMod X hX) :
    a • x = (show X.Tot →ₗ[k] X.Tot from pieceAct X hX a) (show X.Tot from x) := rfl

instance : IsScalarTower k (PieceAlg k S) (PieceMod X hX) where
  smul_assoc c a x := by
    rw [smul_def, smul_def, map_smul]
    rfl

instance [hfin : ∀ i, FiniteDimensional k (X.obj i)] : FiniteDimensional k (PieceMod X hX) :=
  inferInstanceAs (FiniteDimensional k (∀ i, X.obj i))

end PieceMod

/-- **A finite-dimensional representation respecting the cover as a module over the piece
algebra.** -/
def toFDMod (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] : AR.FDMod k (PieceAlg k S) where
  carrier := PieceMod X hX

lemma tot_comp_pieceAct {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    (hY : RespectsCover Y) (φ : X ⟶ Y) (a : PieceAlg k S) :
    φ.tot ∘ₗ pieceAct X hX a = pieceAct Y hY a ∘ₗ φ.tot := by
  obtain ⟨b, rfl⟩ := RingQuot.mkAlgHom_surjective k _ a
  rw [pieceAct_mk, pieceAct_mk]
  have h := Rep.Hom.isPdHom_tot (FinQuiver.Hom.id _) φ
  exact Rep.commute_pdAct _ X φ.tot h.1 h.2 b

/-- **A morphism of representations is a homomorphism of piece-algebra modules.** -/
def toFDModHom {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X) (hY : RespectsCover Y)
    [∀ i, FiniteDimensional k (X.obj i)] [∀ i, FiniteDimensional k (Y.obj i)] (φ : X ⟶ Y) :
    toFDMod X hX ⟶ toFDMod Y hY :=
  show PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY from
  { toFun := φ.tot
    map_add' := map_add φ.tot
    map_smul' := fun a x ↦ LinearMap.congr_fun (tot_comp_pieceAct hX hY φ a) x }

lemma mk_rel_zero {a : (pieceQuiver S).PathAlgebra k} (ha : a ∈ relGens k S) :
    RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0) a
      = 0 := by
  exact (RingQuot.mkAlgHom_rel k
    (s := fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0) (x := a) (y := 0)
    ⟨ha, rfl⟩).trans (map_zero _)

open Classical in
/-- The value in the piece algebra of a composite `f : pt i ⟶ pt j`. -/
def compVal (x : Σ (i j : (pieceQuiver S).V), (pt S i ⟶ pt S j)) : PieceAlg k S :=
  if h : ∃ (l : List (pieceQuiver S).A) (h : FinQuiver.PathFrom x.1 l x.2.1),
      compD S l x.1 x.2.1 h = x.2.2 then
    RingQuot.mkAlgHom k _ (FinQuiver.word k (pieceQuiver S) h.choose) else 0

lemma mk_word_eq_compVal (l : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : FinQuiver.PathFrom i l j) :
    RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)
      (FinQuiver.word k (pieceQuiver S) l) = compVal ⟨i, j, compD S l i j h⟩ := by
  have hex : ∃ (l' : List (pieceQuiver S).A) (h' : FinQuiver.PathFrom i l' j),
      compD S l' i j h' = compD S l i j h := ⟨l, h, rfl⟩
  unfold compVal
  rw [dif_pos hex]
  obtain ⟨h', he⟩ := hex.choose_spec
  have := mk_rel_zero (k := k) (S := S) (a := FinQuiver.word k (pieceQuiver S) l -
    FinQuiver.word k (pieceQuiver S) hex.choose) (Or.inr ⟨l, hex.choose, i, j, h, h', he.symm, rfl⟩)
  rw [map_sub, sub_eq_zero] at this
  exact this

/-- **The piece algebra is finite-dimensional.** -/
instance finiteDimensional_pieceAlg : FiniteDimensional k (PieceAlg k S) := by
  classical
  haveI : ∀ i j : (pieceQuiver S).V, Finite (pt S i ⟶ pt S j) := fun i j ↦
    IsRayCategory.finite_hom _ _
  let T : Set (PieceAlg k S) := {0} ∪ Set.range (fun v ↦ RingQuot.mkAlgHom k _
    (FinQuiver.vertex k (pieceQuiver S) v)) ∪ Set.range (compVal (k := k) (S := S))
  have hT : T.Finite := ((Set.finite_singleton 0).union (Set.finite_range _)).union
    (Set.finite_range _)
  have hspan : Submodule.span k T = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k _ z
    have hx : x ∈ FinQuiver.vwSpan k (Q := pieceQuiver S) := by
      rw [FinQuiver.vwSpan_eq_top]; trivial
    have hmap := Submodule.mem_map_of_mem (f := (RingQuot.mkAlgHom k (fun a b :
      (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)).toLinearMap) hx
    unfold FinQuiver.vwSpan at hmap
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, (⟨v, rfl⟩ | ⟨l, rfl⟩), rfl⟩
    · exact Or.inl (Or.inr ⟨v, rfl⟩)
    · by_cases hp : ∃ i j, FinQuiver.PathFrom i l j
      · obtain ⟨i, j, h⟩ := hp
        exact Or.inr ⟨⟨i, j, compD S l i j h⟩, (mk_word_eq_compVal l i j h).symm⟩
      · left; left
        change RingQuot.mkAlgHom k _ (FinQuiver.word k (pieceQuiver S) l) = 0
        rw [FinQuiver.word_eq_zero_of_not_path k l hp, map_zero]
  exact Module.finite_def.2 (hspan ▸ Submodule.fg_span hT)

section Back

variable {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X) (hY : RespectsCover Y)
  [∀ i, FiniteDimensional k (X.obj i)] [∀ i, FiniteDimensional k (Y.obj i)]

/-- The underlying `k`-linear map of total spaces. -/
def totOf (f : toFDMod X hX ⟶ toFDMod Y hY) : X.Tot →ₗ[k] Y.Tot :=
  (show PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY from f).restrictScalars k

lemma totOf_idm (f : toFDMod X hX ⟶ toFDMod Y hY) (q : (pieceQuiver S).V) :
    totOf hX hY f ∘ₗ X.idm q = Y.idm q ∘ₗ totOf hX hY f := by
  refine LinearMap.ext fun x ↦ ?_
  have h := (show PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY from f).map_smul
    (RingQuot.mkAlgHom k _ (FinQuiver.vertex k _ q)) (show PieceMod X hX from x)
  rw [PieceMod.smul_def, PieceMod.smul_def, pieceAct_mk, pieceAct_mk, Rep.pdAct_vertex,
    Rep.pdAct_vertex, Rep.pdVert_id, Rep.pdVert_id] at h
  exact h

lemma totOf_arrOp (f : toFDMod X hX ⟶ toFDMod Y hY) (c : (pieceQuiver S).A) :
    totOf hX hY f ∘ₗ X.arrOp c = Y.arrOp c ∘ₗ totOf hX hY f := by
  refine LinearMap.ext fun x ↦ ?_
  have h := (show PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY from f).map_smul
    (RingQuot.mkAlgHom k _ (FinQuiver.arrow k _ c)) (show PieceMod X hX from x)
  rw [PieceMod.smul_def, PieceMod.smul_def, pieceAct_mk, pieceAct_mk, Rep.pdAct_arrow,
    Rep.pdAct_arrow, Rep.pdArr_id, Rep.pdArr_id] at h
  exact h

lemma totOf_single (f : toFDMod X hX ⟶ toFDMod Y hY) (i : (pieceQuiver S).V) (v : X.obj i) :
    totOf hX hY f (Pi.single i v) = Pi.single i (Rep.blk (totOf hX hY f) i i v) := by
  have h := LinearMap.congr_fun (totOf_idm hX hY f i) (Pi.single i v)
  simp only [LinearMap.comp_apply, Rep.idm_apply, Pi.single_eq_same] at h
  rw [h]
  rfl

/-- **A homomorphism of piece-algebra modules is a morphism of representations.** -/
def ofFDModHom (f : toFDMod X hX ⟶ toFDMod Y hY) : X ⟶ Y where
  app i := ModuleCat.ofHom (Rep.blk (totOf hX hY f) i i)
  comm e := by
    ext1
    refine LinearMap.ext fun v ↦ ?_
    have h := LinearMap.congr_fun (totOf_arrOp hX hY f e) (Pi.single _ v)
    simp only [LinearMap.comp_apply, Rep.arrOp_apply, Pi.single_eq_same, totOf_single] at h
    have h2 := congrFun h ((pieceQuiver S).tgt e)
    simp only [Pi.single_eq_same] at h2
    exact h2

lemma tot_ofFDModHom (f : toFDMod X hX ⟶ toFDMod Y hY) :
    (ofFDModHom hX hY f).tot = totOf hX hY f := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · rw [totOf_single, Pi.single_eq_same]
    rfl
  · intro i _ hij
    rw [totOf_single, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp

end Back

end RayCat

end LargeIndecomposable
