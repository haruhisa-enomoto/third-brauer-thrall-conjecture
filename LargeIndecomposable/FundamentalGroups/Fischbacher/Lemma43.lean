module

public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# Fischbacher's Lemma 4.3

Let `(v α, w β)` be an essential contour with value `μ` ending at `a`, with arrows `α`, `β`.
Then `α` and `β` are not joined by a walk of arrows into `a` whose steps are common upper
bounds `f ≫ αᵢ = g ≫ αᵢ₊₁ ≠ 0` not factoring through `μ` (`lemma43`; Fischbacher,
*Zur Kombinatorik der Algebren mit endlich vielen Idealen*, Lemma 4.3: `α` and `β` lie in
different components of `(P/μ)_a`). A shortest such walk, closed up by `w` and `v`, would
form a closed chain unless one of its closing conditions fails, and each failure gives a
shorter counterexample.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P] {a s : P}

/-- Morphisms into `a`. -/
abbrev AIn (a : P) : Type (max u v) := Σ x : P, x ⟶ a

/-- `h` factors through `μ`. -/
def Thr (μ : s ⟶ a) {t : P} (h : t ⟶ a) : Prop := ∃ (p : t ⟶ s), h = p ≫ μ

variable (μ : s ⟶ a)

/-- A step between two arrows into `a`: a common upper bound not factoring through `μ`. -/
structure UpStep (A B : AIn a) where
  t : P
  f : t ⟶ A.1
  g : t ⟶ B.1
  eq : f ≫ A.2 = g ≫ B.2
  ne : f ≫ A.2 ≠ 0
  good : ¬Thr μ (f ≫ A.2)
  irrA : IsIrreducible A.2
  irrB : IsIrreducible B.2

/-- A walk of steps between arrows into `a`. -/
inductive UpWalk : AIn a → AIn a → Type (max u v)
  | nil (A : AIn a) : UpWalk A A
  | cons {A B C : AIn a} (st : UpStep μ A B) (W : UpWalk B C) : UpWalk A C

/-- An essential contour `(v α, w β)` with value `μ`. -/
structure EssCfg where
  x : P
  y : P
  α : RayVert.mk x ⟶ RayVert.mk a
  β : RayVert.mk y ⟶ RayVert.mk a
  v : Quiver.Path (RayVert.mk s) (RayVert.mk x)
  w : Quiver.Path (RayVert.mk s) (RayVert.mk y)
  hv : pathVal v ≫ α.1 = μ
  hw : pathVal w ≫ β.1 = μ
  hess : ¬Interlaced (v.cons α) (w.cons β)

variable {μ}

/-- Two paths followed by the same arrow, with equal nonzero values, are interlaced. -/
lemma interlaced_cons_same (hR : RightCancel P) {x : P} (α : RayVert.mk x ⟶ RayVert.mk a)
    (v w : Quiver.Path (RayVert.mk s) (RayVert.mk x)) (h : pathVal v ≫ α.1 = pathVal w ≫ α.1)
    (h0 : pathVal v ≫ α.1 ≠ 0) : Interlaced (v.cons α) (w.cons α) := by
  have hvw : pathVal v = pathVal w := hR _ _ _ h h0
  have hv0 : pathVal v ≠ 0 := fun h' ↦ h0 (by rw [h', zero_comp])
  exact Relation.EqvGen.rel _ _ (interStep_suffix v w α.toPath (by simp) hvw hv0)

/-- An arrow `β = c ≫ α` with `α` an arrow is `α` itself. -/
lemma aIn_eq_of_comp {x y : P} {α : x ⟶ a} {β : y ⟶ a} (hα : IsIrreducible α)
    (hβ : IsIrreducible β) (c : y ⟶ x) (h : c ≫ α = β) : (⟨y, β⟩ : AIn a) = ⟨x, α⟩ := by
  have hc : IsIso c := by
    rcases hβ.2.2 _ c α h.symm with hc | hc
    · exact hc
    · exact absurd hc hα.2.1
  obtain ⟨hyx, hc'⟩ := eq_eqToHom_of_isIso c
  subst hyx
  rw [hc', eqToHom_refl, Category.id_comp] at h
  rw [h]

/-- The contour of a configuration cannot have `α = β`. -/
lemma EssCfg.ne (hR : RightCancel P) (hμ : μ ≠ 0) (C : EssCfg μ) :
    (⟨C.x, C.α.1⟩ : AIn a) ≠ ⟨C.y, C.β.1⟩ := by
  intro h
  obtain ⟨x, y, α, β, v, w, hv, hw, hess⟩ := C
  simp only [Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  have hαβ : α = β := Subtype.ext (eq_of_heq h2)
  subst hαβ
  exact hess (interlaced_cons_same hR α v w (hv.trans hw.symm) (hv ▸ hμ))

namespace UpWalk

/-- The number of steps. -/
def length : ∀ {A C : AIn a}, UpWalk μ A C → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ W => W.length + 1

/-- Appending a step at the end. -/
def snoc : ∀ {A B C : AIn a}, UpWalk μ A B → UpStep μ B C → UpWalk μ A C
  | _, _, _, nil _, st => cons st (nil _)
  | _, _, _, cons st' W, st => cons st' (W.snoc st)

lemma length_snoc : ∀ {A B C : AIn a} (W : UpWalk μ A B) (st : UpStep μ B C),
    (W.snoc st).length = W.length + 1
  | _, _, _, nil _, _ => rfl
  | _, _, _, cons _ W, st => by simp only [snoc, length, length_snoc W st]

lemma exists_snoc : ∀ {A C : AIn a} (W : UpWalk μ A C), 0 < W.length →
    ∃ (B : AIn a) (W' : UpWalk μ A B) (st : UpStep μ B C), W = W'.snoc st
  | _, _, nil _, h => absurd h (lt_irrefl 0)
  | _, _, cons st (nil _), _ => ⟨_, nil _, st, rfl⟩
  | _, _, cons st (cons st' W), _ => by
    obtain ⟨B, W', st'', h⟩ := exists_snoc (cons st' W) (by simp [length])
    exact ⟨B, cons st W', st'', by rw [h]; rfl⟩

end UpWalk

/-- The first morphism of a step, as a ray morphism. -/
def UpStep.fM {A B : AIn a} (st : UpStep μ A B) : RayMor P := ⟨st.t, A.1, st.f⟩

/-- The second morphism of a step, as a ray morphism. -/
def UpStep.gM {A B : AIn a} (st : UpStep μ A B) : RayMor P := ⟨st.t, B.1, st.g⟩

lemma UpStep.f_ne {A B : AIn a} (st : UpStep μ A B) : st.f ≠ 0 :=
  fun h ↦ st.ne (by rw [h, zero_comp])

lemma UpStep.g_ne {A B : AIn a} (st : UpStep μ A B) : st.g ≠ 0 :=
  fun h ↦ st.ne (by rw [st.eq, h, zero_comp])

/-- A failing valley at a step makes it a loop. -/
lemma UpStep.eq_of_not_valley (hL : LeftCancel P) {A B : AIn a} (st : UpStep μ A B)
    (h : ¬Valley st.fM st.gM) : A = B := by
  by_contra hne
  apply h
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ : ∃ c' : A.1 ⟶ B.1, c' = c := ⟨c, rfl⟩
    have hc' : st.f ≫ c = st.g := by
      have := hc
      change eqToHom (rfl : st.t = st.t) ≫ st.f ≫ c = st.g at this
      simpa using this
    apply hne
    have h1 : st.f ≫ A.2 = st.f ≫ (c ≫ B.2) := by
      rw [st.eq, ← hc']
      exact Category.assoc _ _ _
    exact aIn_eq_of_comp st.irrB st.irrA c (hL _ _ _ h1 st.ne).symm
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ : ∃ c' : B.1 ⟶ A.1, c' = c := ⟨c, rfl⟩
    have hc' : st.g ≫ c = st.f := by
      have := hc
      change eqToHom (rfl : st.t = st.t) ≫ st.g ≫ c = st.f at this
      simpa using this
    apply hne
    have h1 : st.g ≫ B.2 = st.g ≫ (c ≫ A.2) := by
      rw [← st.eq, ← hc']
      exact Category.assoc _ _ _
    exact (aIn_eq_of_comp st.irrA st.irrB c (hL _ _ _ h1 (st.eq ▸ st.ne)).symm).symm

/-- A failing peak between consecutive steps merges them. -/
lemma UpStep.merge_of_not_peak {A B C : AIn a} (st : UpStep μ A B) (st' : UpStep μ B C)
    (h : ¬Peak st.gM st'.fM) : Nonempty (UpStep μ A C) := by
  by_contra hne
  apply h
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ : ∃ c' : st.t ⟶ st'.t, c' = c := ⟨c, rfl⟩
    have hc : c ≫ st'.f = st.g := by
      have := hc
      simp only [UpStep.fM, UpStep.gM] at this
      simpa using this
    have e : st.f ≫ A.2 = (c ≫ st'.g) ≫ C.2 := by
      calc st.f ≫ A.2 = st.g ≫ B.2 := st.eq
        _ = (c ≫ st'.f) ≫ B.2 := by rw [hc]
        _ = c ≫ (st'.f ≫ B.2) := Category.assoc _ _ _
        _ = c ≫ (st'.g ≫ C.2) := by rw [st'.eq]
        _ = (c ≫ st'.g) ≫ C.2 := (Category.assoc _ _ _).symm
    exact hne ⟨{ t := st.t, f := st.f, g := c ≫ st'.g, eq := e, ne := st.ne, good := st.good,
                 irrA := st.irrA, irrB := st'.irrB }⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ : ∃ c' : st'.t ⟶ st.t, c' = c := ⟨c, rfl⟩
    have hc : c ≫ st.g = st'.f := by
      have := hc
      simp only [UpStep.fM, UpStep.gM] at this
      simpa using this
    have e : (c ≫ st.f) ≫ A.2 = st'.f ≫ B.2 := by
      calc (c ≫ st.f) ≫ A.2 = c ≫ (st.f ≫ A.2) := Category.assoc _ _ _
        _ = c ≫ (st.g ≫ B.2) := by rw [st.eq]
        _ = (c ≫ st.g) ≫ B.2 := (Category.assoc _ _ _).symm
        _ = st'.f ≫ B.2 := by rw [hc]
    exact hne ⟨{ t := st'.t, f := c ≫ st.f, g := st'.g, eq := e.trans st'.eq,
                 ne := e ▸ st'.ne, good := e ▸ st'.good, irrA := st.irrA, irrB := st'.irrB }⟩

namespace UpWalk

/-- All inner peak and valley conditions hold. -/
def Reduced : ∀ {A C : AIn a}, UpWalk μ A C → Prop
  | _, _, nil _ => True
  | _, _, cons st (nil _) => Valley st.fM st.gM
  | _, _, cons st (cons st' W) => Valley st.fM st.gM ∧ Peak st.gM st'.fM ∧ Reduced (cons st' W)

/-- **Shortening.** A walk that is not reduced can be shortened. -/
lemma shorten (hL : LeftCancel P) : ∀ {A C : AIn a} (W : UpWalk μ A C), ¬W.Reduced →
    ∃ W' : UpWalk μ A C, W'.length < W.length
  | _, _, nil _, h => absurd trivial h
  | _, _, cons st (nil _), h => by
    obtain rfl := st.eq_of_not_valley hL h
    exact ⟨nil _, by simp [length]⟩
  | _, _, cons st (cons st' W), h => by
    by_cases hv : Valley st.fM st.gM
    · by_cases hp : Peak st.gM st'.fM
      · have hr : ¬(cons st' W).Reduced := fun hr ↦ h ⟨hv, hp, hr⟩
        obtain ⟨W', hW'⟩ := shorten hL (cons st' W) hr
        exact ⟨cons st W', by simp only [length] at hW' ⊢; omega⟩
      · obtain ⟨st''⟩ := st.merge_of_not_peak st' hp
        exact ⟨cons st'' W, by simp [length]⟩
    · obtain rfl := st.eq_of_not_valley hL hv
      exact ⟨cons st' W, by simp [length]⟩

/-- The sequence of morphisms along a walk, followed by `T`. -/
def seqW : ∀ {A C : AIn a}, UpWalk μ A C → (ℕ → RayMor P) → ℕ → RayMor P
  | _, _, nil _, T, k => T k
  | _, _, cons st _, _, 0 => st.fM
  | _, _, cons st _, _, 1 => st.gM
  | _, _, cons _ W, T, k + 2 => seqW W T k

lemma seqW_tail : ∀ {A C : AIn a} (W : UpWalk μ A C) (T : ℕ → RayMor P) (j : ℕ),
    W.seqW T (2 * W.length + j) = T j
  | _, _, nil _, _, _ => by simp [seqW, length]
  | _, _, cons _ W, T, j => by
    rw [length, show 2 * (W.length + 1) + j = (2 * W.length + j) + 2 by ring, seqW, seqW_tail W T j]

/-- The continuation after a final step. -/
def stepCont {B C : AIn a} (st : UpStep μ B C) (T : ℕ → RayMor P) : ℕ → RayMor P
  | 0 => st.fM
  | 1 => st.gM
  | k + 2 => T k

lemma seqW_snoc : ∀ {A B C : AIn a} (W : UpWalk μ A B) (st : UpStep μ B C)
    (T : ℕ → RayMor P) (k : ℕ), (W.snoc st).seqW T k = W.seqW (stepCont st T) k
  | _, _, _, nil _, st, T, k => by
    rcases k with _ | _ | k <;> rfl
  | _, _, _, cons st' W, st, T, k => by
    rcases k with _ | _ | k
    · rfl
    · rfl
    · exact seqW_snoc W st T k

lemma valley_seqW : ∀ {A C : AIn a} (W : UpWalk μ A C), W.Reduced → ∀ (T : ℕ → RayMor P) (k : ℕ),
    k < W.length → Valley (W.seqW T (2 * k)) (W.seqW T (2 * k + 1))
  | _, _, nil _, _, _, _, h => by simp [length] at h
  | _, _, cons st (nil _), hr, T, k, h => by
    have : k = 0 := by simp [length] at h; omega
    subst this
    exact hr
  | _, _, cons st (cons st' W), hr, T, k, h => by
    rcases k with _ | k
    · exact hr.1
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by ring]
      exact valley_seqW (cons st' W) hr.2.2 T k (by simp only [length] at h ⊢; omega)

lemma peak_seqW : ∀ {A C : AIn a} (W : UpWalk μ A C), W.Reduced → ∀ (T : ℕ → RayMor P) (k : ℕ),
    k + 1 < W.length → Peak (W.seqW T (2 * k + 1)) (W.seqW T (2 * k + 2))
  | _, _, nil _, _, _, _, h => by simp [length] at h
  | _, _, cons st (nil _), _, T, k, h => by simp [length] at h
  | _, _, cons st (cons st' W), hr, T, k, h => by
    rcases k with _ | k
    · exact hr.2.1
    · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring,
        show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring]
      exact peak_seqW (cons st' W) hr.2.2 T k (by simp only [length] at h ⊢; omega)

lemma ne_seqW : ∀ {A C : AIn a} (W : UpWalk μ A C) (T : ℕ → RayMor P) (k : ℕ),
    k < 2 * W.length → (W.seqW T k).2.2 ≠ 0
  | _, _, nil _, _, _, h => by simp [length] at h
  | _, _, cons st W, T, k, h => by
    rcases k with _ | _ | k
    · exact st.f_ne
    · exact st.g_ne
    · exact ne_seqW W T k (by simp only [length] at h; omega)

end UpWalk

/-- Rerouting `v α` through a factorization `v = c f` and a step `f α = g α'` keeps it interlaced. -/
lemma interlaced_reroute {x x' t : P} (α : RayVert.mk x ⟶ RayVert.mk a)
    (α' : RayVert.mk x' ⟶ RayVert.mk a) (v : Quiver.Path (RayVert.mk s) (RayVert.mk x))
    (c : s ⟶ t) (f : t ⟶ x) (g : t ⟶ x') (hc : c ≫ f = pathVal v) (hfg : f ≫ α.1 = g ≫ α'.1)
    (h0 : f ≫ α.1 ≠ 0) (hv0 : pathVal v ≠ 0) (hc0 : c ≠ 0) (hci : ¬IsIso c) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) :
    Interlaced (v.cons α) (((pathOf (P := P) c hc0).comp (pathOf (P := P) g hg0)).cons α') := by
  have pc := pathVal_pathOf (P := P) c hc0
  have pf := pathVal_pathOf (P := P) f hf0
  have pg := pathVal_pathOf (P := P) g hg0
  have e1 : InterStep (v.comp α.toPath)
      (((pathOf (P := P) c hc0).comp (pathOf (P := P) f hf0)).comp α.toPath) :=
    interStep_suffix v _ α.toPath (by simp) (by rw [pathVal_comp, pc, pf, hc]) hv0
  have e2 : InterStep ((pathOf (P := P) c hc0).comp ((pathOf (P := P) f hf0).comp α.toPath))
      ((pathOf (P := P) c hc0).comp ((pathOf (P := P) g hg0).comp α'.toPath)) :=
    interStep_prefix _ (length_pathOf_pos c hc0 hci) _ _
      (by rw [pathVal_comp, pathVal_comp, pf, pg, pathVal_toPath, pathVal_toPath, hfg])
      (by rw [pathVal_comp, pf, pathVal_toPath]; exact h0)
  rw [Quiver.Path.comp_assoc] at e1
  have e3 : ((pathOf (P := P) c hc0).comp (pathOf (P := P) g hg0)).cons α' =
      (pathOf (P := P) c hc0).comp ((pathOf (P := P) g hg0).comp α'.toPath) := by
    rw [← Quiver.Path.comp_assoc]; rfl
  rw [e3]
  exact (Relation.EqvGen.rel _ _ e1).trans _ _ _ (Relation.EqvGen.rel _ _ e2)

omit [IsRayCategory P] in
lemma factor_of_not_peak {x₁ x₂ z : P} (f : x₁ ⟶ z) (g : x₂ ⟶ z)
    (h : ¬Peak (⟨x₁, z, f⟩ : RayMor P) ⟨x₂, z, g⟩) : (∃ c, c ≫ g = f) ∨ ∃ c, c ≫ f = g := by
  by_contra hc
  push Not at hc
  apply h
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc'⟩
    exact hc.1 c (by simpa using hc')
  · rintro ⟨c, hc'⟩
    exact hc.2 c (by simpa using hc')

omit [IsRayCategory P] in
lemma factor_of_not_valley {x z₁ z₂ : P} (f : x ⟶ z₁) (g : x ⟶ z₂)
    (h : ¬Valley (⟨x, z₁, f⟩ : RayMor P) ⟨x, z₂, g⟩) : (∃ c, f ≫ c = g) ∨ ∃ c, g ≫ c = f := by
  by_contra hc
  push Not at hc
  apply h
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc'⟩
    exact hc.1 c (by simpa using hc')
  · rintro ⟨c, hc'⟩
    exact hc.2 c (by simpa using hc')

omit [IsRayCategory P] in
lemma mod_two_mul (m t e : ℕ) :
    (2 * t + e) % (2 * (m + 1)) = (2 * (t % (m + 1)) + e) % (2 * (m + 1)) := by
  have key : 2 * t + e = (2 * (t % (m + 1)) + e) + 2 * (m + 1) * (t / (m + 1)) := by
    have h := Nat.mod_add_div t (m + 1)
    nlinarith [h]
  rw [key, Nat.add_mul_mod_self_left]

omit [IsRayCategory P] in
/-- A cyclic sequence with alternating peaks and valleys makes chains unbounded (any
universe). -/
theorem not_chainBounded_of_cyclic' (m : ℕ) (f : ℕ → RayMor P) (hne : ∀ t, (f t).2.2 ≠ 0)
    (hP : ∀ i ≤ m, Peak (f (2 * i)) (f (2 * i + 1)))
    (hV : ∀ i < m, Valley (f (2 * i + 1)) (f (2 * i + 2))) (hV' : Valley (f (2 * m + 1)) (f 0)) :
    ¬ChainBounded P := by
  rintro ⟨N, hN⟩
  let g : ℕ → RayMor P := fun t ↦ f (t % (2 * (m + 1)))
  have hr : ∀ t, t % (m + 1) ≤ m := fun t ↦ Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos m))
  have hlink : ∀ j, Link j (g j) (g (j + 1)) := by
    intro j
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · have h1 : (2 * t) % (2 * (m + 1)) = 2 * (t % (m + 1)) := by
        have := mod_two_mul m t 0
        simp only [add_zero] at this
        rw [this, Nat.mod_eq_of_lt (by have := hr t; omega)]
      have h2 : (2 * t + 1) % (2 * (m + 1)) = 2 * (t % (m + 1)) + 1 := by
        rw [mod_two_mul m t 1, Nat.mod_eq_of_lt (by have := hr t; omega)]
      simp only [Link, g, h1, h2, show 2 * t % 2 = 0 by omega, if_true]
      exact hP _ (hr t)
    · have hrt := hr t
      have h1 : (2 * t + 1) % (2 * (m + 1)) = 2 * (t % (m + 1)) + 1 := by
        rw [mod_two_mul m t 1, Nat.mod_eq_of_lt (by omega)]
      have h2 : (2 * t + 1 + 1) % (2 * (m + 1)) = (2 * (t % (m + 1)) + 2) % (2 * (m + 1)) := by
        rw [show 2 * t + 1 + 1 = 2 * t + 2 by ring, mod_two_mul m t 2]
      have hodd : (2 * t + 1) % 2 ≠ 0 := by omega
      simp only [Link, g, if_neg hodd]
      rw [h1, h2]
      rcases Nat.lt_or_ge (t % (m + 1)) m with h | h
      · rw [Nat.mod_eq_of_lt (show 2 * (t % (m + 1)) + 2 < 2 * (m + 1) by omega)]
        exact hV _ h
      · have e : t % (m + 1) = m := by omega
        rw [e, show 2 * m + 2 = 2 * (m + 1) by ring, Nat.mod_self]
        exact hV'
  have h := hN (List.ofFn fun k : Fin (N + 1) ↦ g k) ⟨fun x hx ↦ ?_, fun j hj ↦ ?_⟩
  · simp at h
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact hne _
  · simp only [List.getElem_ofFn, Nat.add_zero]
    exact hlink j

/-- **Fischbacher's Lemma 4.3.** The arrows of an essential contour with value `μ` are not
joined by a walk of common upper bounds avoiding `μ`. -/
theorem lemma43 (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P) (hμ : μ ≠ 0) :
    ∀ (n : ℕ) (C : EssCfg μ) {A B : AIn a} (W : UpWalk μ A B), A = ⟨C.x, C.α.1⟩ →
      B = ⟨C.y, C.β.1⟩ → W.length = n → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C A B W hA hB hn
  by_cases hred : W.Reduced
  swap
  · obtain ⟨W', hW'⟩ := W.shorten hL hred
    exact ih _ (hn ▸ hW') C W' hA hB rfl
  rcases W with _ | ⟨st, W₁⟩
  · exact C.ne hR hμ (hA.symm.trans hB)
  subst hA hB
  have hv0 : pathVal C.v ≠ 0 := fun h ↦ hμ (by rw [← C.hv, h, zero_comp])
  have hw0 : pathVal C.w ≠ 0 := fun h ↦ hμ (by rw [← C.hw, h, zero_comp])
  -- the first peak
  by_cases hP₁ : Peak (⟨s, C.x, pathVal C.v⟩ : RayMor P) st.fM
  swap
  · change ¬Peak (⟨s, C.x, pathVal C.v⟩ : RayMor P) ⟨st.t, C.x, st.f⟩ at hP₁
    rcases factor_of_not_peak _ _ hP₁ with ⟨c, hc⟩ | ⟨c, hc⟩
    · by_cases hci : IsIso c
      · apply st.good
        refine ⟨inv c, ?_⟩
        change st.f ≫ C.α.1 = inv c ≫ μ
        calc st.f ≫ C.α.1 = inv c ≫ (pathVal C.v ≫ C.α.1) := by
              rw [← hc, Category.assoc, IsIso.inv_hom_id_assoc]
          _ = inv c ≫ μ := by rw [C.hv]
      · have hc0 : c ≠ 0 := fun h ↦ hv0 (by rw [← hc, h, zero_comp])
        rename_i B'
        let α' : RayVert.mk B'.1 ⟶ RayVert.mk a := ⟨B'.2, st.irrB⟩
        have hg0 := st.g_ne
        refine ih W₁.length (by simp only [UpWalk.length] at hn; omega)
          { x := B'.1, y := C.y, α := α', β := C.β
            v := (pathOf (P := P) c hc0).comp (pathOf (P := P) st.g hg0), w := C.w
            hv := ?_, hw := C.hw, hess := ?_ } W₁ rfl rfl rfl
        · rw [pathVal_comp, pathVal_pathOf (P := P) c hc0, pathVal_pathOf (P := P) st.g hg0]
          calc (c ≫ st.g) ≫ B'.2 = c ≫ (st.f ≫ C.α.1) := by rw [Category.assoc, ← st.eq]
            _ = pathVal C.v ≫ C.α.1 := by rw [← Category.assoc, hc]
            _ = μ := C.hv
        · intro h
          exact C.hess ((interlaced_reroute C.α α' C.v c st.f st.g hc st.eq st.ne hv0 hc0 hci
            st.f_ne hg0).trans _ _ _ h)
    · apply st.good
      refine ⟨c, ?_⟩
      change st.f ≫ C.α.1 = c ≫ μ
      calc st.f ≫ C.α.1 = c ≫ (pathVal C.v ≫ C.α.1) := by rw [← hc, Category.assoc]
        _ = c ≫ μ := by rw [C.hv]
  -- the last step
  obtain ⟨B', W₀, stl, hW⟩ := (UpWalk.cons st W₁).exists_snoc (by simp [UpWalk.length])
  have hlen : W₀.length + 1 = n := by rw [← hn, hW, UpWalk.length_snoc]
  by_cases hP₂ : Peak stl.gM (⟨s, C.y, pathVal C.w⟩ : RayMor P)
  swap
  · change ¬Peak (⟨stl.t, C.y, stl.g⟩ : RayMor P) ⟨s, C.y, pathVal C.w⟩ at hP₂
    rcases factor_of_not_peak _ _ hP₂ with ⟨c, hc⟩ | ⟨c, hc⟩
    · apply stl.good
      refine ⟨c, ?_⟩
      change stl.f ≫ B'.2 = c ≫ μ
      calc stl.f ≫ B'.2 = stl.g ≫ C.β.1 := stl.eq
        _ = c ≫ (pathVal C.w ≫ C.β.1) := by rw [← hc, Category.assoc]
        _ = c ≫ μ := by rw [C.hw]
    · by_cases hci : IsIso c
      · apply stl.good
        refine ⟨inv c, ?_⟩
        change stl.f ≫ B'.2 = inv c ≫ μ
        calc stl.f ≫ B'.2 = stl.g ≫ C.β.1 := stl.eq
          _ = inv c ≫ (pathVal C.w ≫ C.β.1) := by
              rw [← hc, Category.assoc, IsIso.inv_hom_id_assoc]
          _ = inv c ≫ μ := by rw [C.hw]
      · have hc0 : c ≠ 0 := fun h ↦ hw0 (by rw [← hc, h, zero_comp])
        let β' : RayVert.mk B'.1 ⟶ RayVert.mk a := ⟨B'.2, stl.irrA⟩
        have hf0 := stl.f_ne
        refine ih W₀.length (by omega)
          { x := C.x, y := B'.1, α := C.α, β := β', v := C.v
            w := (pathOf (P := P) c hc0).comp (pathOf (P := P) stl.f hf0)
            hv := C.hv, hw := ?_, hess := ?_ } W₀ rfl rfl rfl
        · rw [pathVal_comp, pathVal_pathOf (P := P) c hc0, pathVal_pathOf (P := P) stl.f hf0]
          calc (c ≫ stl.f) ≫ B'.2 = c ≫ (stl.g ≫ C.β.1) := by rw [Category.assoc, stl.eq]
            _ = pathVal C.w ≫ C.β.1 := by rw [← Category.assoc, hc]
            _ = μ := C.hw
        · intro h
          have hr := interlaced_reroute C.β β' C.w c stl.g stl.f hc stl.eq.symm
            (by rw [← stl.eq]; exact stl.ne) hw0 hc0 hci stl.g_ne hf0
          exact C.hess (h.trans _ _ _ hr.symm)
  -- the closing valley
  by_cases hV : Valley (⟨s, C.y, pathVal C.w⟩ : RayMor P) ⟨s, C.x, pathVal C.v⟩
  swap
  · rcases factor_of_not_valley _ _ hV with ⟨c, hc⟩ | ⟨c, hc⟩
    · have h1 : pathVal C.w ≫ (c ≫ C.α.1) = pathVal C.w ≫ C.β.1 := by
        rw [← Category.assoc, hc, C.hv, C.hw]
      have h2 := hL _ _ _ h1 (by rw [← Category.assoc, hc, C.hv]; exact hμ)
      exact C.ne hR hμ (aIn_eq_of_comp C.α.2 C.β.2 c h2).symm
    · have h1 : pathVal C.v ≫ (c ≫ C.β.1) = pathVal C.v ≫ C.α.1 := by
        rw [← Category.assoc, hc, C.hv, C.hw]
      have h2 := hL _ _ _ h1 (by rw [← Category.assoc, hc, C.hw]; exact hμ)
      exact C.ne hR hμ (aIn_eq_of_comp C.β.2 C.α.2 c h2)
  -- a closed chain
  set W := UpWalk.cons st W₁ with hWdef
  let T : ℕ → RayMor P := fun _ ↦ ⟨s, C.y, pathVal C.w⟩
  let F : ℕ → RayMor P := fun t ↦ if t = 0 then ⟨s, C.x, pathVal C.v⟩ else W.seqW T (t - 1)
  have hF0 : F 0 = ⟨s, C.x, pathVal C.v⟩ := by simp [F]
  have hF : ∀ t, F (t + 1) = W.seqW T t := fun t ↦ by simp [F]
  have hWn : W.length = n := hn
  have hlast : W.seqW T (2 * n - 1) = stl.gM := by
    rw [hW, UpWalk.seqW_snoc, show 2 * n - 1 = 2 * W₀.length + 1 by omega, UpWalk.seqW_tail]
    rfl
  have htail : ∀ j, W.seqW T (2 * n + j) = ⟨s, C.y, pathVal C.w⟩ := fun j ↦ by
    rw [← hWn, UpWalk.seqW_tail]
  refine not_chainBounded_of_cyclic' n F (fun t ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_) ?_ hCB
  · rcases t with _ | t
    · rw [hF0]; exact hv0
    · rw [hF]
      rcases Nat.lt_or_ge t (2 * n) with h | h
      · exact UpWalk.ne_seqW W T t (by omega)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [htail]; exact hw0
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hF0, show 2 * 0 + 1 = 0 + 1 from rfl, hF]
      exact hP₁
    · rcases Nat.lt_or_ge i n with hin | hin
      · have e1 : F (2 * i) = W.seqW T (2 * (i - 1) + 1) := by
          rw [show 2 * i = (2 * (i - 1) + 1) + 1 by omega, hF]
        have e2 : F (2 * i + 1) = W.seqW T (2 * (i - 1) + 2) := by
          rw [show 2 * i + 1 = (2 * (i - 1) + 2) + 1 by omega, hF]
        rw [e1, e2]
        exact UpWalk.peak_seqW W hred T (i - 1) (by omega)
      · have hi : i = n := by omega
        subst hi
        have e1 : F (2 * i) = stl.gM := by
          rw [show 2 * i = (2 * i - 1) + 1 by omega, hF, hlast]
        have e2 : F (2 * i + 1) = ⟨s, C.y, pathVal C.w⟩ := by
          rw [hF]
          have := htail 0
          simpa using this
        rw [e1, e2]
        exact hP₂
  · have e1 : F (2 * i + 1) = W.seqW T (2 * i) := hF _
    have e2 : F (2 * i + 2) = W.seqW T (2 * i + 1) := hF _
    rw [e1, e2]
    exact UpWalk.valley_seqW W hred T i (by omega)
  · have e2 : F (2 * n + 1) = ⟨s, C.y, pathVal C.w⟩ := by
      rw [hF]
      have := htail 0
      simpa using this
    rw [e2, hF0]
    exact hV

end LargeIndecomposable.RayCat
