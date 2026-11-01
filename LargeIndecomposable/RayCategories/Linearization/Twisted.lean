module

public import LargeIndecomposable.RayCategories.Basic.RayQuiver

/-!
# Twisted linearizations

For scalars `λ(l, l') ∈ kˣ` on pairs of paths of `Q_P` with the same nonzero
value, the twisted linearization `k^λ(P)` is `kQ_P` modulo the zero paths and
the relations `l = λ(l, l') l'` (Gabriel–Roiter 13.9, in contour form). If
`λ(l, l') = a(l)/a(l')` for a function `a` on the arrows, rescaling the arrows
gives `k^λ(P) ≅ k(P)` (`RayQuiver.twistedLinEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] (k : Type*) [Field k]

/-- Scalars on pairs of paths with the same start and end. -/
abbrev TwistFn : Type _ :=
  ∀ (l l' : List (quiver P).A) (x y : P), PathFrom (D := quiver P) x l y →
    PathFrom (D := quiver P) x l' y → kˣ

/-- The relations of the twisted linearization. -/
inductive TwistRel (t : TwistFn P k) : (quiver P).PathAlgebra k → (quiver P).PathAlgebra k → Prop
  | zero (l : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
      (h0 : pathMor l x y h = 0) : TwistRel t (word k (quiver P) l) 0
  | eq (l l' : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
      (h' : PathFrom (D := quiver P) x l' y) (he : pathMor l x y h = pathMor l' x y h')
      (hne : pathMor l x y h ≠ 0) :
      TwistRel t (word k (quiver P) l) ((t l l' x y h h' : k) • word k (quiver P) l')

/-- The twisted linearization `k^λ(P)`. -/
abbrev TwistedLin (t : TwistFn P k) := RingQuot (TwistRel P k t)

variable {P k}

/-- The product of an arrow function along a word. -/
def wordProd (a : (quiver P).A → kˣ) (l : List (quiver P).A) : kˣ := (l.map a).prod

/-- Rescaling the arrows of `kQ_P`. -/
def rescale (a : (quiver P).A → kˣ) : (quiver P).PathAlgebra k →ₐ[k] (quiver P).PathAlgebra k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (fun g ↦ match g with
    | Sum.inl v => vertex k (quiver P) v
    | Sum.inr e => ((a e : k)) • arrow k (quiver P) e), by
    intro x y h
    induction h with
    | idem v w =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      change vertex k _ v * vertex k _ w = _
      split_ifs with hvw
      · simp only [FreeAlgebra.lift_ι_apply]
        change _ = RingQuot.mkAlgHom k _ _
        rw [vertex, vertex, ← map_mul]
        exact RingQuot.mkAlgHom_rel k (by convert PathRel.idem (k := k) v w; simp [hvw])
      · rw [map_zero, vertex, vertex, ← map_mul]
        rw [RingQuot.mkAlgHom_rel k (PathRel.idem (k := k) (Q := quiver P) v w), if_neg hvw,
          map_zero]
    | one =>
      simp only [map_sum, FreeAlgebra.lift_ι_apply, map_one]
      change ∑ v, RingQuot.mkAlgHom k _ _ = 1
      rw [← map_sum, RingQuot.mkAlgHom_rel k (PathRel.one (k := k) (Q := quiver P)), map_one]
    | src e =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      change ((a e : k) • arrow k _ e) * vertex k _ _ = (a e : k) • arrow k _ e
      rw [smul_mul_assoc, arrow, vertex, ← map_mul,
        RingQuot.mkAlgHom_rel k (PathRel.src (k := k) (Q := quiver P) e)]
    | tgt e =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      change vertex k _ _ * ((a e : k) • arrow k _ e) = (a e : k) • arrow k _ e
      rw [mul_smul_comm, arrow, vertex, ← map_mul,
        RingQuot.mkAlgHom_rel k (PathRel.tgt (k := k) (Q := quiver P) e)]⟩

lemma rescale_arrow (a : (quiver P).A → kˣ) (e : (quiver P).A) :
    rescale a (arrow k (quiver P) e) = ((a e : k)) • arrow k (quiver P) e := by
  rw [rescale, arrow, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rfl

lemma rescale_word (a : (quiver P).A → kˣ) :
    ∀ l : List (quiver P).A, rescale a (word k (quiver P) l) =
      ((wordProd a l : kˣ) : k) • word k (quiver P) l
  | [] => by simp [word, wordProd]
  | e :: l => by
    rw [word, map_mul, rescale_word a l, rescale_arrow, smul_mul_smul_comm, wordProd, wordProd,
      List.map_cons, List.prod_cons, Units.val_mul, mul_comm]

/-- The twist is the coboundary of `a`. -/
def IsExactTwist (t : TwistFn P k) (a : (quiver P).A → kˣ) : Prop :=
  ∀ (l l' : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
    (h' : PathFrom (D := quiver P) x l' y), pathMor l x y h = pathMor l' x y h' →
      pathMor l x y h ≠ 0 → t l l' x y h h' = wordProd a l / wordProd a l'

variable {t : TwistFn P k} {a : (quiver P).A → kˣ}

/-- `k^λ(P) → k(P)`, rescaling the arrows by `a`. -/
def toLin (ht : IsExactTwist t a) : TwistedLin P k t →ₐ[k] Linearization P k :=
  RingQuot.liftAlgHom k ⟨(linPres P k).comp (rescale a), by
    intro x y h
    induction h with
    | zero l x y h h0 =>
      simp only [AlgHom.comp_apply, rescale_word, map_smul, map_zero]
      rw [linPres, RingQuot.mkAlgHom_rel k (LinRel.zero l x y h h0), map_zero, smul_zero]
    | eq l l' x y h h' he hne =>
      simp only [AlgHom.comp_apply, map_smul, rescale_word]
      rw [linPres, RingQuot.mkAlgHom_rel k (LinRel.eq l l' x y h h' he), ht l l' x y h h' he hne,
        smul_smul]
      congr 1
      rw [← Units.val_mul, div_mul_cancel]⟩

/-- `k(P) → k^λ(P)`, rescaling the arrows by `a⁻¹`. -/
def fromLin (ht : IsExactTwist t a) : Linearization P k →ₐ[k] TwistedLin P k t :=
  RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k (TwistRel P k t)).comp (rescale (fun e ↦ (a e)⁻¹)), by
    intro x y h
    have hinv : ∀ l : List (quiver P).A, wordProd (fun e ↦ (a e)⁻¹) l = (wordProd a l)⁻¹ := by
      intro l
      induction l with
      | nil => simp [wordProd]
      | cons e l ih =>
        simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
        rw [ih, mul_inv]
    induction h with
    | zero l x y h h0 =>
      simp only [AlgHom.comp_apply, rescale_word, map_smul, map_zero]
      rw [RingQuot.mkAlgHom_rel k (TwistRel.zero (t := t) l x y h h0), map_zero, smul_zero]
    | eq l l' x y h h' he =>
      simp only [AlgHom.comp_apply, map_smul, rescale_word]
      by_cases hz : pathMor l x y h = 0
      · rw [RingQuot.mkAlgHom_rel k (TwistRel.zero (t := t) l x y h hz),
          RingQuot.mkAlgHom_rel k (TwistRel.zero (t := t) l' x y h' (he ▸ hz)), map_zero,
          smul_zero, smul_zero]
      · rw [RingQuot.mkAlgHom_rel k (TwistRel.eq (t := t) l l' x y h h' he hz),
          ht l l' x y h h' he hz, map_smul, smul_smul, hinv, hinv]
        congr 1
        rw [← Units.val_mul]
        congr 1
        rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]⟩

lemma rescale_vertex (a : (quiver P).A → kˣ) (v : (quiver P).V) :
    rescale a (vertex k (quiver P) v) = vertex k (quiver P) v := by
  rw [rescale, vertex, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rfl

lemma toLin_mk (ht : IsExactTwist t a) (x : (quiver P).PathAlgebra k) :
    toLin ht (RingQuot.mkAlgHom k (TwistRel P k t) x) = linPres P k (rescale a x) := by
  rw [toLin, RingQuot.liftAlgHom_mkAlgHom_apply]
  rfl

lemma fromLin_linPres (ht : IsExactTwist t a) (x : (quiver P).PathAlgebra k) :
    fromLin ht (linPres P k x) =
      RingQuot.mkAlgHom k (TwistRel P k t) (rescale (fun e ↦ (a e)⁻¹) x) := by
  rw [fromLin, linPres, RingQuot.liftAlgHom_mkAlgHom_apply]
  rfl

/-- **An exact twist is trivial**: `k^λ(P) ≅ k(P)`. -/
def twistedLinEquiv (ht : IsExactTwist t a) : TwistedLin P k t ≃ₐ[k] Linearization P k :=
  AlgEquiv.ofAlgHom (toLin ht) (fromLin ht)
    (by
      apply RingQuot.ringQuot_ext'
      refine algHom_ext (B := Linearization P k) k (quiver P) ?_ ?_
      · intro v
        change toLin ht (fromLin ht (linPres P k _)) = linPres P k _
        rw [fromLin_linPres, toLin_mk, rescale_vertex, rescale_vertex]
      · intro e
        change toLin ht (fromLin ht (linPres P k _)) = linPres P k _
        rw [fromLin_linPres, toLin_mk, rescale_arrow, map_smul, rescale_arrow]
        simp only [map_smul, smul_smul]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
    (by
      apply RingQuot.ringQuot_ext'
      refine algHom_ext (B := TwistedLin P k t) k (quiver P) ?_ ?_
      · intro v
        change fromLin ht (toLin ht (RingQuot.mkAlgHom k _ _)) = RingQuot.mkAlgHom k _ _
        rw [toLin_mk, fromLin_linPres, rescale_vertex, rescale_vertex]
      · intro e
        change fromLin ht (toLin ht (RingQuot.mkAlgHom k _ _)) = RingQuot.mkAlgHom k _ _
        rw [toLin_mk, fromLin_linPres, rescale_arrow, map_smul, rescale_arrow]
        simp only [map_smul, smul_smul]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])

end RayQuiver

end LargeIndecomposable
