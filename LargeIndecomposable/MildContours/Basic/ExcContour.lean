module

public import LargeIndecomposable.MildContours.PennyFarthings.OpenLengthTwo
public import LargeIndecomposable.MildContours.PennyFarthings.OpenAssembly
public import LargeIndecomposable.MildContours.PennyFarthings.OpenCase2
public import LargeIndecomposable.MildContours.Diamonds.Conclusion
public import LargeIndecomposable.MildContours.DumbBells.RemainingFacts

/-!
# Exceptional contours, one contour at a time

`Q2Pair v w`: the contour `v = ρ ρ`, `w = a β` of the exceptional penny-farthing,
with the conditions that let one twist `β` (`Q2Src`) or `a` (`Q2Tgt`) by a unit.
`PFData.exit_q2src`: an open penny-farthing satisfies `Q2Src` (by LPF, no tiny
point and the case-2 analysis).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

section Defs

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]

/-- Every non-invertible endomorphism of `x` is a power of the loop `ρ`. -/
def LoopGen' {x : RayVert Q} (ρ : x ⟶ x) : Prop :=
  ∀ f : x.out ⟶ x.out, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow ρ.1 n

/-- `β` followed by any power of `ρ` kills every other arrow out of `x`. -/
def Q2Src {x t : RayVert Q} (ρ : x ⟶ x) (β : t ⟶ x) : Prop :=
  ∀ {m : RayVert Q} (e : x ⟶ m), ¬(∃ _ : m = x, HEq e ρ) → ∀ n, β.1 ≫ rpow ρ.1 n ≫ e.1 = 0

/-- Every other arrow into `x` followed by any power of `ρ` kills `a`. -/
def Q2Tgt {x t : RayVert Q} (ρ : x ⟶ x) (a : x ⟶ t) : Prop :=
  ∀ {m : RayVert Q} (e : m ⟶ x), ¬(∃ _ : m = x, HEq e ρ) → ∀ n, e.1 ≫ rpow ρ.1 n ≫ a.1 = 0

/-- **The exceptional penny-farthing contour** `ρ ρ ~ a β`. -/
def Q2Pair {x : RayVert Q} (v w : Quiver.Path x x) : Prop :=
  ∃ (ρ : x ⟶ x) (t : RayVert Q) (a : x ⟶ t) (β : t ⟶ x), t ≠ x ∧
    v = (Quiver.Path.nil.cons ρ).cons ρ ∧ w = (Quiver.Path.nil.cons a).cons β ∧
    LoopGen' ρ ∧ ρ.1 ≫ ρ.1 ≫ ρ.1 ≠ 0 ∧ (Q2Src ρ β ∨ Q2Tgt ρ a)

variable (Q) in
/-- **Connectedness**: a set of objects closed under arrows both ways is empty or all. -/
def ArrowConn : Prop :=
  ∀ V : Set Q, (∀ {a b : Q} (e : a ⟶ b), IsIrreducible e → a ∈ V → b ∈ V) →
    (∀ {a b : Q} (e : a ⟶ b), IsIrreducible e → b ∈ V → a ∈ V) → (∀ X, X ∉ V) ∨ ∀ X, X ∈ V

/-- **The exceptional dumb-bell contour** `χ μ ~ μ α`: every other point is a sink or a
source, `μ` is the only arrow from `x` to `y`, and the loops kill the other arrows. -/
def DBExcPair {x y : RayVert Q} (v w : Quiver.Path x y) : Prop :=
  ∃ (χ : x ⟶ x) (μ : x ⟶ y) (α : y ⟶ y) (N : DBN x.out y.out),
    N.χ = χ.1 ∧ N.μ = μ.1 ∧ N.α = α.1 ∧
    v = (Quiver.Path.nil.cons χ).cons μ ∧ w = (Quiver.Path.nil.cons μ).cons α ∧
    (∀ X : Q, X ≠ x.out → X ≠ y.out →
      (∀ {Z : Q} (e : X ⟶ Z), ¬IsIrreducible e) ∨ ∀ {Z : Q} (e : Z ⟶ X), ¬IsIrreducible e) ∧
    (∀ e : x.out ⟶ y.out, IsIrreducible e → e = μ.1) ∧
    (∀ {m : RayVert Q} (e : m ⟶ x), ¬(∃ _ : m = x, HEq e χ) → ∀ n, e.1 ≫ rpow χ.1 n ≫ χ.1 = 0) ∧
    (∀ {m : RayVert Q} (e : y ⟶ m), ¬(∃ _ : m = y, HEq e α) → ∀ n, α.1 ≫ rpow α.1 n ≫ e.1 = 0)

/-- **Exceptional contours**: dumb-bell or `Q₂'`, in either order. -/
def ExcPair {x y : RayVert Q} (v w : Quiver.Path x y) : Prop :=
  DBExcPair v w ∨ DBExcPair w v ∨ ∃ h : y = x, Q2Pair (h ▸ v) (h ▸ w) ∨ Q2Pair (h ▸ w) (h ▸ v)

end Defs

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- A set closed under arrows out of it contains the targets of all nonzero morphisms. -/
lemma mem_of_out (V : Set P) (hout : ∀ {a b : P} (e : a ⟶ b), IsIrreducible e → a ∈ V → b ∈ V) :
    ∀ (n : ℕ) {a b : P} (f : a ⟶ b), depth f ≤ n → f ≠ 0 → a ∈ V → b ∈ V := by
  intro n
  induction n with
  | zero =>
    intro a b f hd hf ha
    by_cases hi : IsIso f
    · exact (eq_of_isIso hi) ▸ ha
    · obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      omega
  | succ n ih =>
    intro a b f hd hf ha
    by_cases hi : IsIso f
    · exact (eq_of_isIso hi) ▸ ha
    · obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      exact ih r (by omega) (fun h ↦ hf (by rw [h, comp_zero])) (hout e he ha)

/-- A set closed under arrows into it contains the sources of all nonzero morphisms. -/
lemma mem_of_in (V : Set P) (hin : ∀ {a b : P} (e : a ⟶ b), IsIrreducible e → b ∈ V → a ∈ V) :
    ∀ (n : ℕ) {a b : P} (f : a ⟶ b), depth f ≤ n → f ≠ 0 → b ∈ V → a ∈ V := by
  intro n
  induction n with
  | zero =>
    intro a b f hd hf hb
    by_cases hi : IsIso f
    · exact (eq_of_isIso hi).symm ▸ hb
    · obtain ⟨c, r, e, he, rfl⟩ := DBN.exists_last f hf hi
      have := depth_lt_comp_right r e hf he.2.1
      omega
  | succ n ih =>
    intro a b f hd hf hb
    by_cases hi : IsIso f
    · exact (eq_of_isIso hi).symm ▸ hb
    · obtain ⟨c, r, e, he, rfl⟩ := DBN.exists_last f hf hi
      have := depth_lt_comp_right r e hf he.2.1
      exact ih r (by omega) (fun h ↦ hf (by rw [h, zero_comp])) (hin e he hb)

/-- An irreducible `e = g ≫ u` with `g` non-invertible: `u` is invertible. -/
lemma tgt_of_irr {a c b : P} (e : a ⟶ b) (he : IsIrreducible e) (g : a ⟶ c) (hg : ¬IsIso g)
    (u : c ⟶ b) (h : g ≫ u = e) : b = c := by
  rcases he.2.2 _ g u h.symm with h' | h'
  · exact absurd h' hg
  · exact (eq_of_isIso h').symm

/-- An irreducible `e = u ≫ g` with `g` non-invertible: `u` is invertible. -/
lemma src_of_irr {a c b : P} (e : a ⟶ b) (he : IsIrreducible e) (g : c ⟶ b) (hg : ¬IsIso g)
    (u : a ⟶ c) (h : u ≫ g = e) : a = c := by
  rcases he.2.2 _ u g h.symm with h' | h'
  · exact eq_of_isIso h'
  · exact absurd h' hg

namespace DBN

variable {x y : P} (N : DBN x y)

/-- `μ` is the only arrow from `x` to `y`. -/
lemma mu_unique (hMo : MildHyp k Pᵒᵖ) (e : x ⟶ y) (he : IsIrreducible e) : e = N.μ := by
  rcases N.out_x hMo e he with ⟨u, hu⟩ | ⟨u, hu⟩
  · rcases he.2.2 _ N.μ u hu.symm with h | h
    · exact absurd h N.hμ.2.1
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
      simpa using hu.symm
  · rcases he.2.2 _ N.χ u hu.symm with h | h
    · exact absurd h N.hχ.2.1
    · exact absurd (eq_of_isIso h) N.hxy

include N in
/-- Arrows out of `x` go to `x` or `y`. -/
lemma out_x_tgt (hMo : MildHyp k Pᵒᵖ) {c : P} (e : x ⟶ c) (he : IsIrreducible e) :
    c = x ∨ c = y := by
  rcases N.out_x hMo e he with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact Or.inr (tgt_of_irr e he N.μ N.hμ.2.1 u hu)
  · exact Or.inl (tgt_of_irr e he N.χ N.hχ.2.1 u hu)

include N in
/-- Arrows into `y` come from `x` or `y`. -/
lemma into_y_src (hM : MildHyp k P) {c : P} (e : c ⟶ y) (he : IsIrreducible e) :
    c = x ∨ c = y := by
  rcases N.into_y hM e he with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact Or.inl (src_of_irr e he N.μ N.hμ.2.1 u hu)
  · exact Or.inr (src_of_irr e he N.α N.hα.2.1 u hu)

/-- The three exceptional dumb-bells: closed, tail at `y`, tail at `x`. -/
def DBGlob : Prop :=
  N.Closed ∨ (∃ (z : P) (t : y ⟶ z), N.TailY t) ∨
    (letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
     ∃ (z : Pᵒᵖ) (t : Opposite.op x ⟶ z), N.op.TailY t)

/-- **The local and global facts of an exceptional dumb-bell.** -/
theorem dbConds (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hconn : ArrowConn P)
    (hg : N.DBGlob) :
    (∀ X : P, X ≠ x → X ≠ y →
      (∀ {Z : P} (e : X ⟶ Z), ¬IsIrreducible e) ∨ ∀ {Z : P} (e : Z ⟶ X), ¬IsIrreducible e) ∧
    (∀ {c : P} (e : c ⟶ x), IsIrreducible e →
      (∃ u, u ≫ N.χ = e) ∨ ∀ n, e ≫ rpow N.χ n ≫ N.χ = 0) ∧
    (∀ {c : P} (e : y ⟶ c), IsIrreducible e →
      (∃ u, N.α ≫ u = e) ∨ ∀ n, N.α ≫ rpow N.α n ≫ e = 0) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  have all : ∀ V : Set P, x ∈ V → (∀ {a b : P} (e : a ⟶ b), IsIrreducible e → a ∈ V → b ∈ V) →
      (∀ {a b : P} (e : a ⟶ b), IsIrreducible e → b ∈ V → a ∈ V) → ∀ X, X ∈ V := by
    intro V hx hout hin
    rcases hconn V hout hin with h | h
    · exact absurd hx (h x)
    · exact h
  rcases hg with hc | ⟨z, t, ht⟩ | ⟨z, t, ht⟩
  · -- closed
    have hall := all {X | X = x ∨ X = y} (Or.inl rfl)
      (fun {a b} e he ha ↦ by
        rcases ha with ha | ha <;> subst a
        · exact N.out_x_tgt hMo e he
        · obtain ⟨u, hu⟩ := hc.1 e he
          exact Or.inr (tgt_of_irr e he N.α N.hα.2.1 u hu))
      (fun {a b} e he hb ↦ by
        rcases hb with hb | hb <;> subst b
        · obtain ⟨u, hu⟩ := hc.2 e he
          exact Or.inl (src_of_irr e he N.χ N.hχ.2.1 u hu)
        · exact N.into_y_src hM e he)
    refine ⟨fun X hX hY ↦ ?_, fun e he ↦ Or.inl (hc.2 e he), fun e he ↦ Or.inl (hc.1 e he)⟩
    rcases hall X with h | h
    · exact absurd h hX
    · exact absurd h hY
  · -- tail at `y`
    have hall := all {X | X = x ∨ X = y ∨ X = z} (Or.inl rfl)
      (fun {a b} e he ha ↦ by
        rcases ha with ha | ha | ha <;> subst a
        · rcases N.out_x_tgt hMo e he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases ht.out_y e he with ⟨u, hu⟩ | ⟨u, hu⟩
          · exact Or.inr (Or.inl (tgt_of_irr e he N.α N.hα.2.1 u hu))
          · exact Or.inr (Or.inr (tgt_of_irr e he t ht.ht.2.1 u hu))
        · exact absurd he (ht.sink e))
      (fun {a b} e he hb ↦ by
        rcases hb with hb | hb | hb <;> subst b
        · obtain ⟨u, hu⟩ := ht.into_x e he
          exact Or.inl (src_of_irr e he N.χ N.hχ.2.1 u hu)
        · rcases N.into_y_src hM e he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · obtain ⟨u, hu⟩ := ht.into_z e he
          exact Or.inr (Or.inl (src_of_irr e he t ht.ht.2.1 u hu)))
    refine ⟨fun X hX hY ↦ ?_, fun e he ↦ Or.inl (ht.into_x e he), fun e he ↦ ?_⟩
    · rcases hall X with h | h | h
      · exact absurd h hX
      · exact absurd h hY
      · subst h; exact Or.inl fun e ↦ ht.sink e
    · rcases ht.out_y e he with h | ⟨u, rfl⟩
      · exact Or.inl h
      · right; intro n
        rw [← Category.assoc, N.rpow_comm, Category.assoc, ← Category.assoc N.α t, ht.αt]
        simp
  · -- tail at `x`
    have hall := all {X | X = x ∨ X = y ∨ X = z.unop} (Or.inl rfl)
      (fun {a b} e he ha ↦ by
        rcases ha with ha | ha | ha <;> subst a
        · rcases N.out_x_tgt hMo e he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · obtain ⟨u, hu⟩ := ht.into_x e.op ((isIrreducible_op e).2 he)
          have hu' : N.α ≫ u.unop = e := by
            have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this
          exact Or.inr (Or.inl (tgt_of_irr e he N.α N.hα.2.1 u.unop hu'))
        · obtain ⟨u, hu⟩ := ht.into_z e.op ((isIrreducible_op e).2 he)
          have hu' : t.unop ≫ u.unop = e := by
            have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this
          exact Or.inl (tgt_of_irr e he t.unop
            (fun h ↦ ht.ht.2.1 ((isIso_unop_iff t).1 h)) u.unop hu'))
      (fun {a b} e he hb ↦ by
        rcases hb with hb | hb | hb <;> subst b
        · rcases ht.out_y e.op ((isIrreducible_op e).2 he) with ⟨u, hu⟩ | ⟨u, hu⟩
          · have hu' : u.unop ≫ N.χ = e := by
              have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this
            exact Or.inl (src_of_irr e he N.χ N.hχ.2.1 u.unop hu')
          · have hu' : u.unop ≫ t.unop = e := by
              have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this
            exact Or.inr (Or.inr (src_of_irr e he t.unop
              (fun h ↦ ht.ht.2.1 ((isIso_unop_iff t).1 h)) u.unop hu'))
        · rcases N.into_y_src hM e he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd ((isIrreducible_op e).2 he) (ht.sink e.op))
    refine ⟨fun X hX hY ↦ ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩
    · rcases hall X with h | h | h
      · exact absurd h hX
      · exact absurd h hY
      · subst h
        exact Or.inr fun e he ↦ ht.sink e.op ((isIrreducible_op e).2 he)
    · rcases ht.out_y e.op ((isIrreducible_op e).2 he) with ⟨u, hu⟩ | ⟨u, hu⟩
      · left
        refine ⟨u.unop, ?_⟩
        have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this
      · right; intro n
        have hu' : e = u.unop ≫ t.unop := by
          have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this.symm
        have htχ : t.unop ≫ N.χ = 0 := by
          have := congrArg Quiver.Hom.unop ht.αt; simpa [DBN.op] using this
        have hc : rpow N.χ n ≫ N.χ = N.χ ≫ rpow N.χ n := by rw [← rpow_succ', rpow_succ]
        rw [hu', hc]
        simp only [Category.assoc]
        rw [← Category.assoc t.unop, htχ]
        simp
    · obtain ⟨u, hu⟩ := ht.into_x e.op ((isIrreducible_op e).2 he)
      left
      refine ⟨u.unop, ?_⟩
      have := congrArg Quiver.Hom.unop hu; simpa [DBN.op] using this

end DBN

/-- An arrow `e = u ≫ f` with `f` an arrow: `e` is `f`. -/
lemma heq_of_comp_left {m x y : RayVert P} (e : m ⟶ y) (f : x ⟶ y) (u : m.out ⟶ x.out)
    (h : u ≫ f.1 = e.1) : ∃ _ : m = x, HEq e f := by
  have hmx : m.out = x.out := src_of_irr e.1 e.2 f.1 f.2.2.1 u h
  have hmx' : m = x := hmx
  subst hmx'
  rcases e.2.2.2 _ u f.1 h.symm with hu | hu
  · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
    exact ⟨rfl, heq_of_eq (Subtype.ext (by simpa using h.symm))⟩
  · exact absurd hu f.2.2.1

/-- An arrow `e = f ≫ u` with `f` an arrow: `e` is `f`. -/
lemma heq_of_comp_right {x m y : RayVert P} (e : x ⟶ m) (f : x ⟶ y) (u : y.out ⟶ m.out)
    (h : f.1 ≫ u = e.1) : ∃ _ : m = y, HEq e f := by
  have hmy : m.out = y.out := tgt_of_irr e.1 e.2 f.1 f.2.2.1 u h
  have hmy' : m = y := hmy
  subst hmy'
  rcases e.2.2.2 _ f.1 u h.symm with hu | hu
  · exact absurd hu f.2.2.1
  · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
    exact ⟨rfl, heq_of_eq (Subtype.ext (by simpa using h.symm))⟩

/-- The paths of a dumb-bell contour have length two. -/
lemma db_shape {x y t : RayVert P} (q w' : Quiver.Path x t) (β : t ⟶ y) (α : y ⟶ y)
    (χ : Quiver.Path x x) (hχ : w' = χ.comp q) (hq : q.length = 0) (hl : χ.length = 1) :
    ∃ (χ' : x ⟶ x) (μ' : x ⟶ y), (q.cons β).cons α = (Quiver.Path.nil.cons μ').cons α ∧
      w'.cons β = (Quiver.Path.nil.cons χ').cons μ' ∧ μ'.1 = pathVal q ≫ β.1 ∧
      χ'.1 = pathVal χ := by
  cases q with
  | cons _ _ => simp at hq
  | nil =>
    cases χ with
    | nil => simp at hl
    | cons χ₀ e =>
      have h0 : χ₀.length = 0 := by simp at hl; omega
      cases χ₀ with
      | cons _ _ => simp at h0
      | nil =>
        subst hχ
        refine ⟨e, β, rfl, rfl, ?_, ?_⟩
        · change β.1 = 𝟙 _ ≫ β.1; simp
        · change e.1 = 𝟙 _ ≫ e.1; simp

namespace DBData

/-- **[mild] Theorem 3, dumb-bell case, one contour**: the contour is an exceptional
dumb-bell contour. -/
theorem db_exc {x y : RayVert P} (D : DBData x y) (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ)
    (hOS : OneSidedCyclic P) (hE : EndCyclic P) (hNPI : NoProjInj P) (hNS : NoSplit P)
    (hconn : ArrowConn P) : DBExcPair (D.w'.cons D.β) D.v := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨χ, hχ⟩ := D.suffix hM hOS
  have hlen := D.χ_len hM hχ
  have hq0 := D.q_nil hM hχ
  have hR : RightCancel P := hM.right
  have hcirr : IsIrreducible (pathVal χ) := irr_of_length_one χ hlen
  haveI : IsIso (pathVal D.q) := MildContour.isIso_pathVal_of_length_zero _ hq0
  have hμirr : IsIrreducible D.μ := isIrreducible_iso_comp (pathVal D.q) D.β.2
  have hap := D.C.apart hR
  let N : DBN x.out y.out := ⟨pathVal χ, D.μ, D.α.1, hcirr, hμirr, D.α.2,
    (D.ω_w hχ).symm.trans (D.ω_v), by have := D.hωρ; rw [D.ω_v] at this; simpa using this,
    D.x_ne_y hM, D.no_yx hM hχ, D.hρ, gen_of_irr _ hcirr hE, D.not_c_μ hM hχ, by
      rintro ⟨g, hg⟩
      have hg0 : g ≠ 0 := fun h ↦ D.h0 (by rw [D.ω_v, ← hg, h, zero_comp, zero_comp])
      obtain ⟨pg, hpg⟩ := exists_path g hg0
      exact cons_ne_of_apart _ D.α _ D.β hap
        (D.uniq_μ hM (pg.cons D.α) (by change pathVal pg ≫ D.α.1 = _; rw [hpg, hg]))⟩
  have hg : N.DBGlob :=
    N.classify hM hMo hNPI hNS (N.midbRest hM hMo) (N.op.midbRest hMo hMo.op)
  obtain ⟨hF1, hLx, hRy⟩ := N.dbConds hM hMo hconn hg
  obtain ⟨χ', μ', hv, hw, hμ', hχ'⟩ := db_shape D.q D.w' D.β D.α χ hχ hq0 hlen
  refine ⟨χ', μ', D.α, N, hχ'.symm, hμ'.symm, rfl, hw, hv, hF1, fun e he ↦ ?_, ?_, ?_⟩
  · rw [N.mu_unique hMo e he]; exact hμ'.symm
  · intro m e he n
    rcases hLx e.1 e.2 with ⟨u, hu⟩ | h
    · exact absurd (heq_of_comp_left e χ' u (by rw [hχ']; exact hu)) he
    · have := h n; rwa [show N.χ = χ'.1 from hχ'.symm] at this
  · intro m e he n
    rcases hRy e.1 e.2 with ⟨u, hu⟩ | h
    · exact absurd (heq_of_comp_right e D.α u hu) he
    · exact h n

end DBData

namespace PFData

/-- **An open penny-farthing has `n = 2` and satisfies `Q2Src`.** -/
theorem exit_q2src {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P}
    (a₁ : x ⟶ c) (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
    (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNT : NoTiny P)
    (hNTo : NoTiny Pᵒᵖ) {z : RayVert P} (μ : x.out ⟶ z.out) (hμ : μ ≠ 0)
    (hz : ¬∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁) :
    ∃ a : x ⟶ D.t, D.w' = Quiver.Path.nil.cons a ∧ Q2Src D.α D.β := by
  have hl := lpfStmt (P := P) (k := k) D hq a₁ w₁ hw hM hMo hE μ hμ hz
  cases w₁ with
  | cons _ _ => simp at hl
  | nil =>
    have hw2 : D.w' = Quiver.Path.nil.cons a₁ := by rw [hw]; rfl
    refine ⟨a₁, hw2, ?_⟩
    have hzx : z ≠ x := by
      rintro rfl
      exact hz ⟨.nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm⟩
    have hzt : z ≠ D.t := by
      rintro rfl
      exact hz ⟨Quiver.Path.nil.cons a₁, Quiver.Path.nil.cons D.β, D.split2 hq a₁ hw2⟩
    have hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y) := by
      intro y hyx hyt
      refine ⟨fun ε ↦ hNT _ _ (D.tiny_x0 hq a₁ hw2 hM hMo hE ε hyx hyt)⟩
    obtain ⟨y, hyx, hyt, γ, haγ⟩ := D.exit_t hq a₁ hw2 hM hE hno _
      (pathOf (P := P) (x := x.out) (y := z.out) μ hμ) rfl
      (by rw [pathVal_pathOf]; exact hμ) hzx hzt
    have hγk := fun {v : P} (e : y.out ⟶ v) (he : IsIrreducible e) ↦
      D.γ_kill hq a₁ hw2 hM hMo hE hNTo hno γ.1 γ.2 hyx hyt haγ e he
    have hs0 : D.β.1 ≫ D.α.1 ≫ a₁.1 = 0 := by
      by_contra h
      exact hNT _ _ (D.tiny_case2 hq a₁ hw2 hM hMo hE hNTo hno γ.1 γ.2 hyx hyt haγ hγk h)
    have hba := D.ba_zero hq a₁ hw2 hM hE
    obtain ⟨-, -, r3⟩ := D.rel hq a₁ hw2 hM hMo hE hNTo hno hM
    have bra : ∀ j, D.β.1 ≫ rpow D.α.1 j ≫ a₁.1 = 0 := by
      intro j
      rcases j with _ | _ | j
      · simpa [rpow] using hba
      · simpa [rpow] using hs0
      · rw [show j + 1 + 1 = 2 + j by omega, rpow_add]
        simp only [rpow, Category.id_comp, Category.assoc]
        rw [← Category.assoc D.β.1, ← Category.assoc (D.β.1 ≫ D.α.1), Category.assoc D.β.1, r3,
          zero_comp]
    intro m e he n
    by_cases hmx : m = x
    · subst hmx
      exact absurd ⟨rfl, heq_of_eq (D.loop_eq_rho hq a₁ .nil (D.hw2 hq a₁ hw2) e)⟩ he
    by_cases hmt : m = D.t
    · subst hmt
      by_cases he0 : e.1 = 0
      · rw [he0]; simp
      obtain ⟨j, hj⟩ := D.mor_to_interior hq a₁ .nil (D.hw2 hq a₁ hw2) hM hE
        (Quiver.Path.nil.cons a₁) (Quiver.Path.nil.cons D.β) (by simp) (by simp)
        (D.split2 hq a₁ hw2) e.1 he0
      have ha1v : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
        change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
      rw [hj, ha1v, ← Category.assoc (rpow D.α.1 n), ← rpow_add, bra]
    · exact ((hno hmx hmt).false e).elim

end PFData

/-- `Q2Src` in `Pᵒᵖ` for the reversed loop and `revArr a` is `Q2Tgt` in `P`. -/
lemma q2tgt_of_op {x t : RayVert P} (ρ : x ⟶ x) (a : x ⟶ t)
    (h : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); Q2Src (revArr ρ) (revArr a)) : Q2Tgt ρ a := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  intro m e he n
  have h' := h (revArr e) (by
    rintro ⟨hm, hh⟩
    apply he
    have hmx : m = x := by
      have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hm
      exact this
    subst hmx
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    have := congrArg (fun f : (RayVert.mk (op m.out) : RayVert Pᵒᵖ) ⟶ RayVert.mk (op m.out) ↦
      f.1.unop) (eq_of_heq hh)
    exact this) n
  apply Quiver.Hom.op_inj
  change (revArr a).1 ≫ rpow (revArr ρ).1 n ≫ (revArr e).1 = 0 at h'
  change a.1.op ≫ rpow ρ.1.op n ≫ e.1.op = 0 at h'
  rw [op_zero, op_comp, op_comp, op_rpow, Category.assoc]
  exact h'

namespace PFData

/-- **[mild] Theorem 3, penny-farthing case, one contour**: the contour is the
exceptional `Q₂'` contour. -/
theorem pf_exc {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P}
    (a₁ : x ⟶ c) (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
    (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNPI : NoProjInj P)
    (hNT : NoTiny P) (hNTo : NoTiny Pᵒᵖ) : Q2Pair D.v (D.w'.cons D.β) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have hv : D.v = (Quiver.Path.nil.cons D.α).cons D.α := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]
  have h3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by
    have := D.hωρ
    rw [show (D.q.cons D.α).cons D.α = (Quiver.Path.nil.cons D.α).cons D.α by rw [hq]] at this
    change ((𝟙 _ ≫ D.α.1) ≫ D.α.1) ≫ D.α.1 ≠ 0 at this
    simpa using this
  by_cases hclR : ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁
  · by_cases hclL : ∀ {z : RayVert P} (μ : z.out ⟶ x.out), μ ≠ 0 →
        ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁
    · exact (D.closed_false hq a₁ w₁ hw hM hE hNPI hclR hclL).elim
    · push Not at hclL
      obtain ⟨z, μ, hμ, hz⟩ := hclL
      obtain ⟨a', hw', hsrc⟩ := exit_q2src (D.op hq a₁ w₁ hw) rfl (revArr D.β) (revPath w₁) rfl
        hMo hMo.op hE.op hNTo hNT.op_op
        (show (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ).out ⟶
          (RayVert.mk (Opposite.op z.out) : RayVert Pᵒᵖ).out from μ.op)
        (fun h ↦ hμ (Quiver.Hom.op_inj (by exact h.trans (op_zero _ _).symm))) (by
          rintro ⟨p, s₁, hps⟩
          apply hz (unrevPath s₁) (unrevPath p)
          have h1 : (D.op hq a₁ w₁ hw).w'.cons (D.op hq a₁ w₁ hw).β =
              revPath (D.w'.cons D.β) := (D.revPath_w a₁ w₁ hw).symm
          have h2 := congrArg unrevPath (h1.symm.trans hps)
          rw [unrevPath_revPath, unrevPath_comp] at h2
          exact h2)
      have hl : w₁.length = 0 := by
        have := congrArg Quiver.Path.length hw'
        change ((Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁)).length = _ at this
        simp [length_revPath] at this
        exact this
      cases w₁ with
      | cons _ _ => simp at hl
      | nil =>
        have hw2 : D.w' = Quiver.Path.nil.cons a₁ := by rw [hw]; rfl
        refine ⟨D.α, D.t, a₁, D.β, D.t_ne_x hq a₁ hw2 hM, hv, by rw [hw2], D.hρ, h3, Or.inr ?_⟩
        exact q2tgt_of_op D.α a₁ hsrc
  · push Not at hclR
    obtain ⟨z, μ, hμ, hz⟩ := hclR
    obtain ⟨a, hw2, hsrc⟩ := exit_q2src D hq a₁ w₁ hw hM hMo hE hNT hNTo μ hμ
      (fun ⟨p, s₁, h⟩ ↦ hz p s₁ h)
    exact ⟨D.α, D.t, a, D.β, D.t_ne_x hq a hw2 hM, hv, by rw [hw2], D.hρ, h3, Or.inl hsrc⟩

end PFData

/-- **The core case of [mild] Theorem 3, one contour**: a contour with `ρ = ω' ≫ α` is
exceptional. -/
theorem coreExc (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hOS : OneSidedCyclic P) (hNPI : NoProjInj P) (hNS : NoSplit P) (hNT : NoTiny P)
    (hNTo : NoTiny Pᵒᵖ) (hconn : ArrowConn P) {x y : P} (C : MildContour x y)
    (ω' : y ⟶ C.sv) (hρ : C.ρ = ω' ≫ C.α.1) : ExcPair (C.v'.cons C.α) (C.w'.cons C.β) := by
  by_cases hω' : IsIso ω'
  swap
  · exact (diamondStmt (P := P) (k := k) C ω' hω' hρ hM hMo hE hNPI hNT hNTo).elim
  have hR : RightCancel P := hM.right
  have hv := C.v'_pos hR
  have hw := C.w'_pos hR
  obtain ⟨sv, sw, v', α, w', β, hval, h0, hni, ρ, hρρ, hωρ⟩ := C
  obtain ⟨h, he⟩ := RayQuiver.eq_id_of_isIso ω'
  dsimp only at h he hρ hv hw ⊢
  subst he
  subst h
  change ρ = 𝟙 _ ≫ α.1 at hρ
  rw [Category.id_comp] at hρ
  subst hρ
  change 0 < v'.length at hv
  change 0 < w'.length at hw
  obtain ⟨s, e, v'', hv''⟩ : ∃ (s : P) (e : (RayVert.mk s : RayVert P) ⟶ RayVert.mk y)
      (v'' : Quiver.Path (RayVert.mk x) (RayVert.mk s)), v' = v''.cons e := by
    cases v' with
    | nil => simp at hv
    | cons v'' e => exact ⟨_, e, v'', rfl⟩
  subst hv''
  rcases MildContour.loop_prev hM v'' e α w' β hval h0 hni hρρ hωρ with ⟨hs, hes⟩ | ⟨hs, hes⟩
  · subst hs
    have he' := eq_of_heq hes
    subst he'
    have hq := (PFData.mk (x := RayVert.mk x) (y := RayVert.mk s) e (RayVert.mk sw) w' β v''
      hval h0 hni hρρ hωρ).q_length hM
    change v''.length = 0 at hq
    obtain ⟨c, a₁, w₁, hw₁⟩ := path_first_arrow w' (by omega)
    cases v'' with
    | nil =>
        right; right
        refine ⟨rfl, Or.inl ?_⟩
        exact (PFData.mk (x := RayVert.mk x) (y := RayVert.mk x) e (RayVert.mk sw) w' β .nil
          hval h0 hni hρρ hωρ).pf_exc rfl a₁ w₁ hw₁ hM hMo hE hNPI hNT hNTo
    | cons _ _ => simp at hq
  · subst hs
    have he' := eq_of_heq hes
    subst he'
    right; left
    exact DBData.db_exc ⟨α, RayVert.mk s, w', e, v'', hval, h0, hni, hρρ, hωρ⟩ hM hMo hOS hE
      hNPI hNS hconn

section Dual

lemma unop_rpow {C : Type*} [Category C] {X : Cᵒᵖ} (e : X ⟶ X) (n : ℕ) :
    (rpow e n).unop = rpow e.unop n := by
  apply Quiver.Hom.op_inj
  rw [Quiver.Hom.op_unop, op_rpow]
  rfl

/-- The dumb-bell of `Pᵒᵖ` read in `P`. -/
def DBN.unop {x y : P}
    (N : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); DBN (Opposite.op y) (Opposite.op x)) :
    DBN x y :=
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  { χ := N.α.unop
    μ := N.μ.unop
    α := N.χ.unop
    hχ := (isIrreducible_unop _).2 N.hα
    hμ := (isIrreducible_unop _).2 N.hμ
    hα := (isIrreducible_unop _).2 N.hχ
    comm := by have := congrArg Quiver.Hom.unop N.comm; simpa using this.symm
    hτ := by
      intro h
      apply N.hτ
      apply Quiver.Hom.unop_inj
      have hc : N.α.unop ≫ N.μ.unop = N.μ.unop ≫ N.χ.unop := by
        have := congrArg Quiver.Hom.unop N.comm; simpa using this.symm
      have e : N.α.unop ≫ N.α.unop ≫ N.μ.unop = N.μ.unop ≫ N.χ.unop ≫ N.χ.unop := by
        rw [hc, ← Category.assoc, hc, Category.assoc]
      simp only [unop_comp, unop_zero, Category.assoc]
      rw [e]; exact h
    hxy := fun h ↦ N.hxy (congrArg Opposite.op h.symm)
    hyx := fun f ↦ Quiver.Hom.op_inj (by rw [N.hyx f.op]; rfl)
    hρ := by
      intro f hf
      obtain ⟨n, hn, h⟩ := N.hρx f.op (fun h' ↦ hf ((isIso_op_iff f).1 h'))
      exact ⟨n, hn, by rw [← unop_rpow, ← h]; rfl⟩
    hρx := by
      intro f hf
      obtain ⟨n, hn, h⟩ := N.hρ f.op (fun h' ↦ hf ((isIso_op_iff f).1 h'))
      exact ⟨n, hn, by rw [← unop_rpow, ← h]; rfl⟩
    nχμ := by
      rintro ⟨g, hg⟩
      exact N.nαμ ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩
    nαμ := by
      rintro ⟨g, hg⟩
      exact N.nχμ ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩ }

/-- A path of `Pᵒᵖ` of length two, read back. -/
lemma unrevPath_two {X Y Z : RayVert Pᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z) :
    unrevPath ((Quiver.Path.nil.cons a).cons b) =
      (Quiver.Path.nil.cons (unrevArr b)).cons (unrevArr a) := rfl

lemma eq_of_revPath_two {x y : RayVert P} (v : Quiver.Path x y)
    {Y : RayVert Pᵒᵖ} (a : (RayVert.mk (Opposite.op y.out) : RayVert Pᵒᵖ) ⟶ Y)
    (b : Y ⟶ RayVert.mk (Opposite.op x.out))
    (h : revPath v = (Quiver.Path.nil.cons a).cons b) :
    v = (Quiver.Path.nil.cons (unrevArr b)).cons (unrevArr a) := by
  have := congrArg unrevPath h
  rw [unrevPath_revPath] at this
  exact this

/-- Reversing preserves "another arrow". -/
lemma not_heq_revArr_src {m x : RayVert P} (e : m ⟶ x)
    (c : (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ) ⟶ RayVert.mk (Opposite.op x.out))
    (he : ¬∃ _ : m = x, HEq e (unrevArr c)) :
    ¬∃ _ : (RayVert.mk (Opposite.op m.out) : RayVert Pᵒᵖ) = RayVert.mk (Opposite.op x.out),
      HEq (revArr e) c := by
  rintro ⟨hm, hh⟩
  apply he
  have hmx : m = x := by
    have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hm
    exact this
  subst hmx
  refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
  have := congrArg (fun f : (RayVert.mk (Opposite.op m.out) : RayVert Pᵒᵖ) ⟶
    RayVert.mk (Opposite.op m.out) ↦ f.1.unop) (eq_of_heq hh)
  exact this

lemma not_heq_revArr_tgt {x m : RayVert P} (e : x ⟶ m)
    (c : (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ) ⟶ RayVert.mk (Opposite.op x.out))
    (he : ¬∃ _ : m = x, HEq e (unrevArr c)) :
    ¬∃ _ : (RayVert.mk (Opposite.op m.out) : RayVert Pᵒᵖ) = RayVert.mk (Opposite.op x.out),
      HEq (revArr e) c := by
  rintro ⟨hm, hh⟩
  apply he
  have hmx : m = x := by
    have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hm
    exact this
  subst hmx
  refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
  have := congrArg (fun f : (RayVert.mk (Opposite.op m.out) : RayVert Pᵒᵖ) ⟶
    RayVert.mk (Opposite.op m.out) ↦ f.1.unop) (eq_of_heq hh)
  exact this

/-- **An exceptional dumb-bell contour of `Pᵒᵖ`, reversed**, is one of `P`. -/
theorem db_of_op {x y : RayVert P} (v w : Quiver.Path x y)
    (h : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); DBExcPair (revPath v) (revPath w)) :
    DBExcPair w v := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  obtain ⟨χo, μo, αo, No, h1, h2, h3, hv, hw, hF1, hF4, hLx, hRy⟩ := h
  refine ⟨unrevArr αo, unrevArr μo, unrevArr χo, DBN.unop No, ?_, ?_, ?_,
    eq_of_revPath_two w μo αo hw, eq_of_revPath_two v χo μo hv, ?_, ?_, ?_, ?_⟩
  · change No.α.unop = αo.1.unop; rw [h3]
  · change No.μ.unop = μo.1.unop; rw [h2]
  · change No.χ.unop = χo.1.unop; rw [h1]
  · intro X hX hY
    rcases hF1 (Opposite.op X) (fun h ↦ hY (congrArg Opposite.unop h))
        (fun h ↦ hX (congrArg Opposite.unop h)) with h | h
    · exact Or.inr fun e he ↦ h e.op ((isIrreducible_op e).2 he)
    · exact Or.inl fun e he ↦ h e.op ((isIrreducible_op e).2 he)
  · intro e he
    have := hF4 e.op ((isIrreducible_op e).2 he)
    exact Quiver.Hom.op_inj this
  · intro m e he n
    have := hRy (revArr e) (not_heq_revArr_src e αo he) n
    apply Quiver.Hom.op_inj
    change αo.1 ≫ rpow αo.1 n ≫ e.1.op = 0 at this
    rw [op_zero, op_comp, op_comp, op_rpow, Category.assoc]
    exact this
  · intro m e he n
    have := hLx (revArr e) (not_heq_revArr_tgt e χo he) n
    apply Quiver.Hom.op_inj
    change e.1.op ≫ rpow χo.1 n ≫ χo.1 = 0 at this
    rw [op_zero, op_comp, op_comp, op_rpow]
    change (e.1.op ≫ rpow χo.1 n) ≫ χo.1 = 0
    rw [Category.assoc]; exact this

/-- **The exceptional penny-farthing contour of `Pᵒᵖ`, reversed**, is one of `P`. -/
theorem q2_of_op {x : RayVert P} (v w : Quiver.Path x x)
    (h : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); Q2Pair (revPath v) (revPath w)) :
    Q2Pair v w := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  obtain ⟨ρo, tₒ, ao, βo, hto, hv, hw, hLG, h3, hst⟩ := h
  have h3' : (unrevArr ρo).1 ≫ (unrevArr ρo).1 ≫ (unrevArr ρo).1 ≠ 0 := by
    intro h; apply h3
    change ρo.1 ≫ ρo.1 ≫ ρo.1 = 0
    apply Quiver.Hom.unop_inj
    change (ρo.1 ≫ ρo.1 ≫ ρo.1).unop = 0
    simp only [unop_comp, Category.assoc]
    exact h
  rcases hst with hsrc | htgt
  · refine ⟨unrevArr ρo, RayVert.mk tₒ.out.unop, unrevArr βo, unrevArr ao, ?_,
      eq_of_revPath_two v ρo ρo hv, eq_of_revPath_two w ao βo hw, ?_, h3', Or.inr ?_⟩
    · intro h; apply hto
      change (RayVert.mk (Opposite.op (tₒ.out.unop)) : RayVert Pᵒᵖ) = _
      exact congrArg (fun z : P ↦ (RayVert.mk (Opposite.op z) : RayVert Pᵒᵖ)) h
    · intro f hf
      obtain ⟨n, hn, h⟩ := hLG f.op (fun h' ↦ hf ((isIso_op_iff f).1 h'))
      exact ⟨n, hn, by
        change f = rpow ρo.1.unop n
        rw [← unop_rpow, ← h]; rfl⟩
    · intro m e he n
      have := hsrc (revArr e) (not_heq_revArr_src e ρo he) n
      apply Quiver.Hom.op_inj
      change βo.1 ≫ rpow ρo.1 n ≫ e.1.op = 0 at this
      rw [op_zero, op_comp, op_comp, op_rpow, Category.assoc]
      exact this
  · refine ⟨unrevArr ρo, RayVert.mk tₒ.out.unop, unrevArr βo, unrevArr ao, ?_,
      eq_of_revPath_two v ρo ρo hv, eq_of_revPath_two w ao βo hw, ?_, h3', Or.inl ?_⟩
    · intro h; apply hto
      change (RayVert.mk (Opposite.op (tₒ.out.unop)) : RayVert Pᵒᵖ) = _
      exact congrArg (fun z : P ↦ (RayVert.mk (Opposite.op z) : RayVert Pᵒᵖ)) h
    · intro f hf
      obtain ⟨n, hn, h⟩ := hLG f.op (fun h' ↦ hf ((isIso_op_iff f).1 h'))
      exact ⟨n, hn, by
        change f = rpow ρo.1.unop n
        rw [← unop_rpow, ← h]; rfl⟩
    · intro m e he n
      have := htgt (revArr e) (not_heq_revArr_tgt e ρo he) n
      apply Quiver.Hom.op_inj
      change e.1.op ≫ rpow ρo.1 n ≫ ao.1 = 0 at this
      rw [op_zero, op_comp, op_comp, op_rpow]
      change (e.1.op ≫ rpow ρo.1 n) ≫ ao.1 = 0
      rw [Category.assoc]; exact this

/-- **An exceptional contour of `Pᵒᵖ`, reversed**, is one of `P`. -/
theorem excPair_of_op {x y : RayVert P} (v w : Quiver.Path x y)
    (h : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); ExcPair (revPath v) (revPath w)) :
    ExcPair v w := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  rcases h with h | h | ⟨hxy, h | h⟩
  · exact Or.inr (Or.inl (db_of_op v w h))
  · exact Or.inl (db_of_op w v h)
  · have hyx : y = x := by
      have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hxy
      exact this.symm
    subst hyx
    exact Or.inr (Or.inr ⟨rfl, Or.inl (q2_of_op v w h)⟩)
  · have hyx : y = x := by
      have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hxy
      exact this.symm
    subst hyx
    exact Or.inr (Or.inr ⟨rfl, Or.inr (q2_of_op w v h)⟩)

end Dual

section Chain

variable (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] in
/-- **The core case, one contour at a time**: a contour with `ρ = ω' ≫ α` is exceptional. -/
def CoreExcHyp : Prop :=
  ∀ {x y : Q} (C : MildContour x y) (ω' : y ⟶ C.sv), C.ρ = ω' ≫ C.α.1 →
    ExcPair (C.v'.cons C.α) (C.w'.cons C.β)

lemma excPair_symm {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]
    {x y : RayVert Q} {v w : Quiver.Path x y} (h : ExcPair v w) : ExcPair w v := by
  rcases h with h | h | ⟨hh, h | h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hh, Or.inr h⟩)
  · exact Or.inr (Or.inr ⟨hh, Or.inl h⟩)

lemma revContour_v {x y c d : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) (b : x ⟶ d)
    (w₁ : Quiver.Path d y)
    (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
    (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
    (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0) :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).v'.cons (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).α =
      revPath ((Quiver.Path.nil.cons a).comp v₁) ∧
    (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).w'.cons (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).β =
      revPath ((Quiver.Path.nil.cons b).comp w₁) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  exact ⟨(revPath_cons_first a v₁).symm, (revPath_cons_first b w₁).symm⟩

/-- The reversed contour is exceptional, or its reversal is. -/
lemma excPair_of_revContour {x y c d : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) (b : x ⟶ d)
    (w₁ : Quiver.Path d y)
    (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
    (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
    (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (h : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
      ExcPair ((revContour a v₁ b w₁ hval h0 hni σ hσ hσω).v'.cons
          (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).α)
        ((revContour a v₁ b w₁ hval h0 hni σ hσ hσω).w'.cons
          (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).β)) :
    ExcPair ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  obtain ⟨h1, h2⟩ := revContour_v a v₁ b w₁ hval h0 hni σ hσ hσω
  rw [h1, h2] at h
  exact excPair_of_op _ _ h

variable {k : Type*} [Field k] [Infinite k]

/-- **Lemma 2.1 on the reversal, one contour**: non-deep at `y`, or exceptional. -/
theorem dual_step_exc {x y c d : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) (b : x ⟶ d)
    (w₁ : Quiver.Path d y)
    (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
    (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
    (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hMo : MildHyp k Pᵒᵖ)
    (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreExcHyp Pᵒᵖ) :
    (∃ R : y.out ⟶ y.out, ¬IsIso R ∧
      σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) =
        pathVal ((Quiver.Path.nil.cons a).comp v₁) ≫ R) ∨
      ExcPair ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  set C' := revContour a v₁ b w₁ hval h0 hni σ hσ hσω with hC'
  have hRo : RightCancel Pᵒᵖ := hMo.right
  have hω := revContour_ω a v₁ b w₁ hval h0 hni σ hσ hσω
  rw [← hC'] at hω
  have key : ∀ (g : (op y.out : Pᵒᵖ) ⟶ op y.out), ¬IsIso g → C'.τ = g ≫ C'.ω →
      ∃ R : y.out ⟶ y.out, ¬IsIso R ∧
        σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) =
          pathVal ((Quiver.Path.nil.cons a).comp v₁) ≫ R := by
    intro g hg he
    refine ⟨g.unop, fun h ↦ hg (by have : IsIso g.unop.op := inferInstance; exact this), ?_⟩
    have := congrArg Quiver.Hom.unop he
    change (C'.ω ≫ σ.op).unop = (g ≫ C'.ω).unop at this
    rw [unop_comp, unop_comp, hω] at this
    exact this
  rcases C'.lemma21 hMo with ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩
  · exact Or.inr (excPair_of_revContour a v₁ b w₁ hval h0 hni σ hσ hσω (hcoreo C' ξ hξ.symm))
  · have h := hcoreo C'.swap ξ hξ.symm
    obtain ⟨h1, h2⟩ := revContour_v a v₁ b w₁ hval h0 hni σ hσ hσω
    change ExcPair (C'.w'.cons C'.β) (C'.v'.cons C'.α) at h
    rw [h1, h2] at h
    exact Or.inr (excPair_symm (excPair_of_op _ _ h))
  · exact Or.inl (key _ (not_isIso_comp_of_left _ _ (C'.γ_not_isIso hRo)) hξ)
  · exact Or.inl (key _ (not_isIso_comp_of_left _ _ (C'.δ_not_isIso hRo)) hξ)

namespace MildContour

/-- **The γ-alternative of Lemma 2.1, one contour**: the contour is exceptional. -/
theorem gamma_case_exc (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreExcHyp Pᵒᵖ) {x y : P}
    (C : MildContour x y) {ξ : C.sv ⟶ x} (hξ : C.τ = (C.γ ≫ ξ) ≫ C.ω) :
    ExcPair (C.v'.cons C.α) (C.w'.cons C.β) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  obtain ⟨σ, hσ⟩ := hE x
  obtain ⟨n, hn, hn'⟩ := hσ _ (not_isIso_comp_of_left _ _ (C.γ_not_isIso hR))
  obtain ⟨c, a, v₁', hv'⟩ := path_first_arrow C.v' (by have := C.v'_pos hR; omega)
  obtain ⟨d, b, w₁', hw'⟩ := path_first_arrow C.w' (by have := C.w'_pos hR; omega)
  have hvfull : C.v'.cons C.α = (Quiver.Path.nil.cons a).comp (v₁'.cons C.α) := by rw [hv']; rfl
  have hwfull : C.w'.cons C.β = (Quiver.Path.nil.cons b).comp (w₁'.cons C.β) := by rw [hw']; rfl
  rw [hvfull, hwfull]
  have hval : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) =
      pathVal ((Quiver.Path.nil.cons b).comp (w₁'.cons C.β)) := by
    rw [← hvfull, ← hwfull]; exact C.hval
  have h0 : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) ≠ 0 := by
    rw [← hvfull]; exact C.h0
  have hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α))
      ((Quiver.Path.nil.cons b).comp (w₁'.cons C.β)) := by
    rw [← hvfull, ← hwfull]; exact C.hni
  have hωv : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) = C.ω := by rw [← hvfull]
  have hτ : C.τ = rpow σ n ≫ C.ω := by rw [hξ, hn']
  have hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) ≠ 0 := by
    rw [hωv]; intro h
    apply C.τ_ne_zero
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hτ, rpow_succ, Category.assoc, h, comp_zero]
  rcases dual_step_exc (k := k) a (v₁'.cons C.α) b (w₁'.cons C.β) hval h0 hni σ hσ hσω hMo
    hcoreo with ⟨R, hRi, hRe⟩ | hexc
  swap
  · exact hexc
  rw [hωv] at hRe
  obtain ⟨i, hi, hRi'⟩ := C.hρ R hRi
  have hiter : ∀ m, rpow σ m ≫ C.ω = C.ω ≫ rpow C.ρ (m * i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [rpow_succ, Category.assoc, hRe, ← Category.assoc, ih, Category.assoc, hRi',
          ← rpow_add, Nat.succ_mul]
  have h1 : C.ω ≫ C.ρ = C.ω ≫ rpow C.ρ (n * i) := by
    change C.τ = _; rw [hτ, hiter]
  have h2 : rpow C.ρ 1 = rpow C.ρ (n * i) := by
    rw [show rpow C.ρ 1 = C.ρ by simp [rpow_succ]]
    exact hL _ _ _ h1 C.τ_ne_zero
  have hρ1 : rpow C.ρ 1 ≠ 0 := by
    rw [show rpow C.ρ 1 = C.ρ by simp [rpow_succ]]
    intro h
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [h, comp_zero]
  have h3 := rpow_le_of_eq C.ρ C.ρ_not_isIso hρ1 h2
  have hn1 : n = 1 := by
    have : n * i ≤ 1 := h3
    rcases Nat.lt_or_ge 1 n with h | h
    · have : 2 ≤ n * i := le_trans (by omega) (Nat.mul_le_mul_right i h)
      omega
    · omega
  subst hn1
  have hσa : σ = a.1 ≫ (pathVal v₁' ≫ ξ) := by
    have hγ : C.γ = a.1 ≫ pathVal v₁' := by
      change pathVal C.v' = _; rw [hv', pathVal_comp]; change (𝟙 _ ≫ a.1) ≫ _ = _
      rw [Category.id_comp]
    rw [← Category.assoc, ← hγ, hn']; simp [rpow_succ]
  refine excPair_of_revContour a (v₁'.cons C.α) b (w₁'.cons C.β) hval h0 hni σ hσ hσω
    (hcoreo (revContour a (v₁'.cons C.α) b (w₁'.cons C.β) hval h0 hni σ hσ hσω)
      (pathVal v₁' ≫ ξ).op ?_)
  change σ.op = (pathVal v₁' ≫ ξ).op ≫ a.1.op
  rw [← op_comp, ← hσa]

/-- **Every mild contour is exceptional**, given the core case for `P` and `Pᵒᵖ`. -/
theorem exc_of_mildContour (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcore : CoreExcHyp P) (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreExcHyp Pᵒᵖ)
    {x y : P} (C : MildContour x y) : ExcPair (C.v'.cons C.α) (C.w'.cons C.β) := by
  rcases C.lemma21 hM with ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩
  · exact hcore C ξ hξ.symm
  · exact excPair_symm (hcore C.swap ξ hξ.symm)
  · exact C.gamma_case_exc hM hMo hE hcoreo hξ
  · refine excPair_symm (C.swap.gamma_case_exc hM hMo hE hcoreo (ξ := ξ) ?_)
    rw [swap_τ, swap_ω]; exact hξ

/-- **Contours are deep or exceptional** ([mild] Theorem 3 at the ray level, one contour). -/
theorem deep_or_exc (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcore : CoreExcHyp P) (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreExcHyp Pᵒᵖ)
    {x y : RayVert P} (v w : Quiver.Path x y) (hval : pathVal v = pathVal w)
    (h0 : pathVal v ≠ 0) (hni : ¬Interlaced v w) :
    ((∀ e : y.out ⟶ y.out, ¬IsIso e → pathVal v ≫ e = 0) ∧
      (∀ e : x.out ⟶ x.out, ¬IsIso e → e ≫ pathVal v = 0)) ∨ ExcPair v w := by
  by_cases hexc : ExcPair v w
  · exact Or.inr hexc
  left
  have hy : ∀ e : y.out ⟶ y.out, ¬IsIso e → pathVal v ≫ e = 0 := by
    intro e he
    by_contra hne
    obtain ⟨ρ, hρ⟩ := hE y.out
    obtain ⟨n, hn, rfl⟩ := hρ e he
    have hωρ : pathVal v ≫ ρ ≠ 0 := by
      intro h; apply hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rpow_succ', ← Category.assoc, h, zero_comp]
    cases v with
    | nil => exact absurd (length_pos_of_contour hval hni) (by simp)
    | cons v' α =>
        cases w with
        | nil => exact absurd (length_pos_of_contour hval.symm (fun h ↦ hni h.symm)) (by simp)
        | cons w' β =>
            exact hexc (exc_of_mildContour hM hMo hE hcore hcoreo
              (⟨_, _, v', α, w', β, hval, h0, hni, ρ, hρ, hωρ⟩ : MildContour x.out y.out))
  refine ⟨hy, fun e he ↦ ?_⟩
  by_contra hne
  obtain ⟨σ, hσ⟩ := hE x.out
  obtain ⟨n, hn, rfl⟩ := hσ e he
  have hσω : σ ≫ pathVal v ≠ 0 := by
    intro h; apply hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rpow_succ, Category.assoc, h, comp_zero]
  obtain ⟨c, a, v₁, hv⟩ := path_first_arrow v (by have := length_pos_of_contour hval hni; omega)
  obtain ⟨d, b, w₁, hw⟩ := path_first_arrow w
    (by have := length_pos_of_contour hval.symm (fun h ↦ hni h.symm); omega)
  subst hv hw
  rcases dual_step_exc (k := k) a v₁ b w₁ hval h0 hni σ hσ hσω hMo hcoreo with ⟨R, hRi, hRe⟩ | h
  · exact hσω (by rw [hRe, hy R hRi])
  · exact hexc h

end MildContour

end Chain

end RayCat

end LargeIndecomposable
