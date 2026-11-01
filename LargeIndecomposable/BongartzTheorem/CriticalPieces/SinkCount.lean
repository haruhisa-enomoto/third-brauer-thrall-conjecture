module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalPoint
public import LargeIndecomposable.Quivers.Representations.ExtCount

/-!
# Point–brick data from a count of arrows and relations

Let `F` be a finite family of relations generating the relations of the cover of a piece. For a
brick `V` vanishing at `x`, the extensions of `V` by the simple representation at `x` that respect
the cover are the cocycles of `F` (`crossOK_of_cocycle`), and their dimension is at least
`Σ_{α → x} dim V(s α) - Σ_{ρ_r ending at x} dim V(s r)` (`Ext.finrank_data_le`). If this number is
at least `2`, two independent extensions give the data of Bongartz's Lemma 4
(`pointBrick_of_count`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- Representations respecting the cover are killed by the ideal of relations. -/
lemma act_eq_zero_of_mem_span {X : Rep k (pieceQuiver S)} (hX : RespectsCover X) :
    ∀ ρ ∈ TwoSidedIdeal.span (relGens k S), Ext.act X ρ = 0 := by
  let Ann : TwoSidedIdeal ((pieceQuiver S).PathAlgebra k) :=
    TwoSidedIdeal.mk' {ρ | X.pdAct (FinQuiver.Hom.id _) ρ = 0} (by simp)
      (fun {a b} (ha : X.pdAct _ a = 0) (hb : X.pdAct _ b = 0) ↦ by
        change X.pdAct _ (a + b) = 0; rw [map_add, ha, hb, add_zero])
      (fun {a} (ha : X.pdAct _ a = 0) ↦ by change X.pdAct _ (-a) = 0; rw [map_neg, ha, neg_zero])
      (fun {a b} (hb : X.pdAct _ b = 0) ↦ by
        change X.pdAct _ (a * b) = 0; rw [map_mul, hb, mul_zero])
      (fun {a b} (ha : X.pdAct _ a = 0) ↦ by
        change X.pdAct _ (a * b) = 0; rw [map_mul, ha, zero_mul])
  have hle : TwoSidedIdeal.span (relGens k S) ≤ Ann := by
    rw [TwoSidedIdeal.span_le]
    intro ρ hρ
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_mk']
    exact (respectsCover_iff X).1 hX ρ hρ
  intro ρ hρ
  have := hle hρ
  rw [TwoSidedIdeal.mem_mk'] at this
  exact this

lemma kcross_eq {D : FinQuiver} (K : KroneckerPair k D)
    (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α)) :
    ∀ le : List D.A, K.cross z le = Ext.cross (X := K.P) (Y := K.Q₀) z le
  | [] => rfl
  | e :: le => by
    change K.Q₀.pathTot le ∘ₗ K.zOp z e + K.cross z le ∘ₗ K.P.arrOp e =
      K.Q₀.pathTot le ∘ₗ Ext.zOp z e + Ext.cross z le ∘ₗ K.P.arrOp e
    rw [kcross_eq K z le]
    rfl

lemma crossA_word {D : FinQuiver} {X Y : Rep k D} (z : Ext.Data X Y) (l : List D.A) :
    Ext.crossA z (FinQuiver.word k D l) = Ext.cross z l := by
  unfold Ext.crossA; rw [Ext.act_word, Ext.cross_eq]

lemma crossA_sub {D : FinQuiver} {X Y : Rep k D} (z : Ext.Data X Y) (a b : D.PathAlgebra k) :
    Ext.crossA z (a - b) = Ext.crossA z a - Ext.crossA z b := by
  simp [Ext.crossA, LinearMap.sub_comp, LinearMap.comp_sub]

/-- **Cocycles of a generating family give extensions respecting the cover.** -/
theorem crossOK_of_cocycle (K : KroneckerPair k (pieceQuiver S)) (hP : RespectsCover K.P)
    (hQ : RespectsCover K.Q₀) (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (z : ∀ α : (pieceQuiver S).A, K.P.obj ((pieceQuiver S).src α) →ₗ[k]
      K.Q₀.obj ((pieceQuiver S).tgt α))
    (hz : z ∈ Ext.cocycles F (X := K.P) (Y := K.Q₀)) : CrossOK K z := by
  have hle : TwoSidedIdeal.span (Set.range F.ρ) ≤ TwoSidedIdeal.span (relGens k S) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨r, rfl⟩
    exact hF r
  have hall : ∀ ρ ∈ TwoSidedIdeal.span (Set.range F.ρ), Ext.crossA z ρ = 0 :=
    Ext.crossA_eq_zero_of_span z _ (fun ρ hρ ↦ act_eq_zero_of_mem_span hP ρ (hle hρ))
      (fun ρ hρ ↦ act_eq_zero_of_mem_span hQ ρ (hle hρ))
      (by rintro _ ⟨r, rfl⟩; exact (Ext.mem_cocycles F z).1 hz r)
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rw [kcross_eq, ← crossA_word]
    exact hall _ (hgen (Or.inl ⟨le, i, j, h, h0, rfl⟩))
  · rw [kcross_eq, kcross_eq, ← crossA_word, ← crossA_word, ← sub_eq_zero, ← crossA_sub]
    exact hall _ (hgen (Or.inr ⟨le, le', i, j, h, h', he, rfl⟩))

/-- Two linearly independent vectors in a space of dimension at least two. -/
lemma exists_pair {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (h : 2 ≤ Module.finrank k W) :
    ∃ w₁ w₂ : W, ∀ c₁ c₂ : k, c₁ • w₁ + c₂ • w₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
  let b := Module.finBasis k W
  refine ⟨b ⟨0, by omega⟩, b ⟨1, by omega⟩, fun c₁ c₂ hc ↦ ?_⟩
  have hinj : Function.Injective
      (![⟨0, by omega⟩, ⟨1, by omega⟩] : Fin 2 → Fin (Module.finrank k W)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  have hli : LinearIndependent k ![b ⟨0, by omega⟩, b ⟨1, by omega⟩] := by
    have := b.linearIndependent.comp _ hinj
    convert this using 1
    funext i; fin_cases i <;> rfl
  exact LinearIndependent.pair_iff.1 hli c₁ c₂ hc

/-- **Point–brick data from a count.** If `V` is a sincere brick off `x`, vanishing at `x` and
respecting the cover, and a generating family of relations has
`Σ_r dim V(s r) dim S_x(t r) + 2 ≤ Σ_α dim V(s α) dim S_x(t α)`, then `PointBrick` holds. -/
theorem pointBrick_of_count (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hsinc : ∀ i, i ≠ x → Nontrivial (V.obj i))
    (hVc : RespectsCover V)
    (hcount : ∑ r, Module.finrank k (V.obj (F.s r)) *
        Module.finrank k ((Rep.pointRep (k := k) x).obj (F.t r)) + 2 ≤
      ∑ α : (pieceQuiver S).A, Module.finrank k (V.obj ((pieceQuiver S).src α)) *
        Module.finrank k ((Rep.pointRep (k := k) x).obj ((pieceQuiver S).tgt α))) :
    PointBrick (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  have hdata : Module.finrank k (Ext.Data V (Rep.pointRep (k := k) x)) =
      ∑ α : (pieceQuiver S).A, Module.finrank k (V.obj ((pieceQuiver S).src α)) *
        Module.finrank k ((Rep.pointRep (k := k) x).obj ((pieceQuiver S).tgt α)) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  have hle := Ext.finrank_data_le F (X := V) (Y := Rep.pointRep (k := k) x)
  have h2 : 2 ≤ Module.finrank k (Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x)) := by
    omega
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data V (Rep.pointRep (k := k) x)) α + c₂ • (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) α = 0) →
      c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x),
      CrossOK (pairAtSink x V finV hVx brickV hV (w₁ : Ext.Data V (Rep.pointRep (k := k) x)) (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) hind)
        (w : Ext.Data V (Rep.pointRep (k := k) x)) := fun w ↦
    crossOK_of_cocycle _ hVc (respectsCover_pointRep x) F hF hgen _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hsinc, hVc,
    Or.inr ⟨(w₁ : Ext.Data V (Rep.pointRep (k := k) x)), (w₂ : Ext.Data V (Rep.pointRep (k := k) x)), hind, hK w₁, hK w₂⟩⟩

end LargeIndecomposable.RayCat