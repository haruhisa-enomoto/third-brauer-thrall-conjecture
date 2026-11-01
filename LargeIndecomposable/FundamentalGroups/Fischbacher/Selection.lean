module

public import LargeIndecomposable.RayCategories.Basic.RayFirstArrow

/-!
# The selection in Fischbacher's reduction lemma

Fix a point `b` of a finite, chain-bounded ray category with cancellation.
`R₀` consists of the arrows from `b` and the values of essential contours
starting at `b`; `R` is the component of `R₀` (for comparability in the prefix
order) containing a fixed arrow `β`. This file develops the combinatorics of
`R` used to choose the arrows `αᵢ` and the path `u` of Fischbacher's
Lemma 2.1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

section Defs

variable {b : P}

/-- An arrow from `b`. -/
def IsArr (α : BMor b) : Prop := IsIrreducible α.2

/-- The value of an essential contour starting at `b`. -/
def IsEssVal (ν : BMor b) : Prop :=
  ∃ v w : Quiver.Path (RayVert.mk b) (RayVert.mk ν.1), pathVal v = ν.2 ∧ pathVal w = ν.2 ∧
    ν.2 ≠ 0 ∧ ¬Interlaced v w

/-- Fischbacher's set `R₀`. -/
def InR0 (ν : BMor b) : Prop := IsArr ν ∨ IsEssVal ν

/-- Comparability in the prefix order. -/
def Comp (ν μ : BMor b) : Prop := BLe ν μ ∨ BLe μ ν

/-- Adjacency within `S`: comparable elements of `S`. -/
def Adj (S : BMor b → Prop) (x y : BMor b) : Prop := S x ∧ S y ∧ Comp x y

/-- Connectedness within `S`. -/
def Conn (S : BMor b → Prop) (x y : BMor b) : Prop := S x ∧ Relation.ReflTransGen (Adj S) x y

variable {S S' : BMor b → Prop} {x y z : BMor b}

omit [HasZeroMorphisms P] in
lemma Comp.symm (h : Comp x y) : Comp y x := Or.symm h

omit [HasZeroMorphisms P] in
lemma Conn.refl (hx : S x) : Conn S x x := ⟨hx, .refl⟩

omit [HasZeroMorphisms P] in
lemma Conn.mem_right (h : Conn S x y) : S y := by
  obtain ⟨hx, h⟩ := h
  induction h with
  | refl => exact hx
  | tail _ h _ => exact h.2.1

omit [HasZeroMorphisms P] in
lemma Conn.trans (h₁ : Conn S x y) (h₂ : Conn S y z) : Conn S x z :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

omit [HasZeroMorphisms P] in
lemma Conn.symm (h : Conn S x y) : Conn S y x := by
  refine ⟨h.mem_right, ?_⟩
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact .refl
  | tail _ hac ih => exact .head ⟨hac.2.1, hac.1, Or.symm hac.2.2⟩ ih

omit [HasZeroMorphisms P] in
lemma Conn.of_comp (hx : S x) (hy : S y) (h : Comp x y) : Conn S x y :=
  ⟨hx, .single ⟨hx, hy, h⟩⟩

omit [HasZeroMorphisms P] in
lemma Conn.mono (h : Conn S x y) (hS : ∀ z, S z → S' z) : Conn S' x y := by
  refine ⟨hS _ h.1, ?_⟩
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact .refl
  | tail _ hac ih => exact .tail ih ⟨hS _ hac.1, hS _ hac.2.1, hac.2.2⟩

lemma IsArr.ne_zero {α : BMor b} (h : IsArr α) : α.2 ≠ 0 := h.1

variable [IsRayCategory P]

/-- Paths of an essential contour are nonempty. -/
lemma IsEssVal.exists {ν : BMor b} (h : IsEssVal ν) :
    ∃ v w : Quiver.Path (RayVert.mk b) (RayVert.mk ν.1), pathVal v = ν.2 ∧ pathVal w = ν.2 ∧
      ν.2 ≠ 0 ∧ ¬Interlaced v w ∧ 0 < v.length ∧ 0 < w.length := by
  obtain ⟨v, w, hv, hw, h0, hi⟩ := h
  have key : ∀ (v w : Quiver.Path (RayVert.mk b) (RayVert.mk ν.1)), pathVal v = ν.2 →
      pathVal w = ν.2 → ¬Interlaced v w → 0 < v.length := by
    intro v w hv hw hi
    by_contra hl
    have hl : v.length = 0 := by omega
    have hb := Quiver.Path.eq_of_length_zero v hl
    obtain ⟨y, f⟩ := ν
    change b = y at hb
    subst hb
    have hvn := Quiver.Path.eq_nil_of_length_zero v hl
    subst hvn
    by_cases hwl : w.length = 0
    · exact hi (by rw [Quiver.Path.eq_nil_of_length_zero w hwl]; exact .refl _)
    · exact not_isIso_pathVal w (by omega) (by rw [hw, ← hv]; exact IsIso.id _)
  exact ⟨v, w, hv, hw, h0, hi, key v w hv hw hi,
    key w v hw hv (fun h ↦ hi (Relation.EqvGen.symm _ _ h))⟩

omit [IsRayCategory P] in
lemma IsEssVal.ne_zero {ν : BMor b} (h : IsEssVal ν) : ν.2 ≠ 0 := h.choose_spec.choose_spec.2.2.1

lemma InR0.ne_zero {ν : BMor b} (h : InR0 ν) : ν.2 ≠ 0 := h.elim IsArr.ne_zero IsEssVal.ne_zero

/-- Every element of `R₀` has an arrow below it. -/
lemma InR0.exists_arr {ν : BMor b} (h : InR0 ν) : ∃ α, IsArr α ∧ BLe α ν := by
  rcases h with h | h
  · exact ⟨ν, h, BLe.refl _⟩
  · obtain ⟨v, -, hv, -, -, -, hl, -⟩ := h.exists
    obtain ⟨α, hα⟩ := exists_isFirst v hl
    refine ⟨α, hα.isIrreducible, ?_⟩
    have := hα.bLe
    rwa [hv] at this

/-- Elements of `R₀` are not invertible. -/
lemma InR0.not_isIso {ν : BMor b} (h : InR0 ν) : ¬IsIso ν.2 := by
  rcases h with h | h
  · exact h.2.1
  · obtain ⟨v, -, hv, -, -, -, hl, -⟩ := h.exists
    rw [← hv]
    exact not_isIso_pathVal v hl

/-- Arrows are minimal in `R₀`. -/
lemma IsArr.eq_of_bLe {α ν : BMor b} (hα : IsArr α) (hν : InR0 ν) (h : BLe ν α) : ν = α := by
  obtain ⟨ρ, hρ⟩ := h
  rcases hα.2.2 _ _ _ hρ.symm with h1 | h1
  · exact absurd h1 hν.not_isIso
  · exact eq_of_comp_isIso ρ hρ

end Defs

section Walk

variable {b : P}

/-- A walk of length `k` from `g 0` to `g k` through upper terms in `T`:
`g 0 ≤ m 0 ≥ g 1 ≤ m 1 ≥ … ≥ g k`, the `g i` arrows. -/
def IsWalk (T : BMor b → Prop) (k : ℕ) (g m : ℕ → BMor b) : Prop :=
  (∀ i ≤ k, IsArr (g i)) ∧ ∀ i < k, T (m i) ∧ BLe (g i) (m i) ∧ BLe (g (i + 1)) (m i)

/-- Arrows joined by a walk through `T`. -/
def WalkConn (T : BMor b → Prop) (γ γ' : BMor b) : Prop :=
  ∃ k g m, IsWalk T k g m ∧ g 0 = γ ∧ g k = γ'

variable {T : BMor b → Prop}

lemma walkConn_refl {γ : BMor b} (hγ : IsArr γ) : WalkConn T γ γ :=
  ⟨0, fun _ ↦ γ, fun _ ↦ γ, ⟨fun _ _ ↦ hγ, fun i hi ↦ absurd hi (by omega)⟩, rfl, rfl⟩

lemma WalkConn.isArr_left {γ γ' : BMor b} (h : WalkConn T γ γ') : IsArr γ := by
  obtain ⟨k, g, m, hw, rfl, -⟩ := h
  exact hw.1 0 (by omega)

lemma WalkConn.snoc {γ g₀ : BMor b} (h : WalkConn T γ g₀) {M : BMor b} (hM : T M)
    (hg : BLe g₀ M) {g' : BMor b} (hg' : IsArr g') (hg'M : BLe g' M) : WalkConn T γ g' := by
  obtain ⟨k, g, m, hw, h0, hk⟩ := h
  refine ⟨k + 1, fun j ↦ if j ≤ k then g j else g', fun j ↦ if j < k then m j else M,
    ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩, by simp [h0], by simp⟩
  · dsimp only
    split_ifs with h
    · exact hw.1 i h
    · exact hg'
  · dsimp only
    by_cases hik : i < k
    · rw [if_pos hik, if_pos hik.le, if_pos (by omega : i + 1 ≤ k)]
      exact hw.2 i hik
    · have hik' : i = k := by omega
      subst hik'
      rw [if_neg (lt_irrefl _), if_pos le_rfl, if_neg (by omega), hk]
      exact ⟨hM, hg, hg'M⟩

/-- Deleting a repeated lower term. -/
lemma IsWalk.del_g {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk T k g m) (i : ℕ) (hi : i < k)
    (he : g i = g (i + 1)) : IsWalk T (k - 1) (fun j ↦ if j ≤ i then g j else g (j + 1))
      (fun j ↦ if j < i then m j else m (j + 1)) := by
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · dsimp only
    split_ifs
    · exact hw.1 j (by omega)
    · exact hw.1 (j + 1) (by omega)
  · dsimp only
    by_cases hji : j < i
    · rw [if_pos hji.le, if_pos (by omega : j + 1 ≤ i), if_pos hji]
      exact hw.2 j (by omega)
    · rw [if_neg (by omega : ¬j + 1 ≤ i), if_neg hji]
      by_cases hj' : j = i
      · subst hj'
        rw [if_pos le_rfl, he]
        exact hw.2 (j + 1) (by omega)
      · rw [if_neg (by omega : ¬j ≤ i)]
        exact hw.2 (j + 1) (by omega)

/-- Deleting a repeated upper term. -/
lemma IsWalk.del_m {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk T k g m) (i : ℕ) (hi : i + 1 < k)
    (he : m i = m (i + 1)) : IsWalk T (k - 1) (fun j ↦ if j ≤ i then g j else g (j + 1))
      (fun j ↦ if j ≤ i then m j else m (j + 1)) := by
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · dsimp only
    split_ifs
    · exact hw.1 j (by omega)
    · exact hw.1 (j + 1) (by omega)
  · dsimp only
    by_cases hji : j < i
    · simp only [show j ≤ i from hji.le, show j + 1 ≤ i by omega, ↓reduceIte]
      exact hw.2 j (by omega)
    · by_cases hj' : j = i
      · subst hj'
        simp only [le_refl, show ¬j + 1 ≤ j by omega, ↓reduceIte]
        refine ⟨(hw.2 j (by omega)).1, (hw.2 j (by omega)).2.1, ?_⟩
        rw [he]
        exact (hw.2 (j + 1) (by omega)).2.2
      · simp only [show ¬j ≤ i by omega, show ¬j + 1 ≤ i by omega, ↓reduceIte]
        exact hw.2 (j + 1) (by omega)

/-- A shortest walk has no repeated consecutive terms. -/
lemma exists_walk_min {γ γ' : BMor b} (h : WalkConn T γ γ') :
    ∃ k g m, IsWalk T k g m ∧ g 0 = γ ∧ g k = γ' ∧ (∀ i < k, g i ≠ g (i + 1)) ∧
      ∀ i, i + 1 < k → m i ≠ m (i + 1) := by
  classical
  have hex : ∃ k, ∃ (g m : ℕ → BMor b), IsWalk T k g m ∧ g 0 = γ ∧ g k = γ' := h
  have hs := Nat.find_spec hex
  obtain ⟨g, m, hw, h0, hk⟩ := hs
  refine ⟨Nat.find hex, g, m, hw, h0, hk, fun i hi he ↦ ?_, fun i hi he ↦ ?_⟩
  · refine Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex)
      ⟨_, _, hw.del_g i hi he, by simp [h0], ?_⟩
    split_ifs with h1
    · rw [show Nat.find hex - 1 = i by omega, he, show i + 1 = Nat.find hex by omega, hk]
    · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega, hk]
  · refine Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex)
      ⟨_, _, hw.del_m i hi he, by simp [h0], ?_⟩
    rw [if_neg (by omega), show Nat.find hex - 1 + 1 = Nat.find hex by omega, hk]

variable [IsRayCategory P]

/-- A walk without consecutive repetitions, closed up by an upper term `W`
incomparable with its first and last upper terms, is a crown. -/
theorem not_chainBounded_of_walk (hR : RightCancel P)
    (hanti : ∀ m m', T m → T m' → BLe m m' → m = m') (hT0 : ∀ m, T m → m.2 ≠ 0)
    {W : BMor b} (hW0 : W.2 ≠ 0) {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk T k g m) (hk0 : 0 < k)
    (hg : ∀ i < k, g i ≠ g (i + 1)) (hm : ∀ i, i + 1 < k → m i ≠ m (i + 1)) (hne : g 0 ≠ g k)
    (hγ : BLe (g 0) W) (hγ' : BLe (g k) W) (hW1 : ¬BLe (m 0) W ∧ ¬BLe W (m 0))
    (hW2 : ¬BLe (m (k - 1)) W ∧ ¬BLe W (m (k - 1))) : ¬ChainBounded P := by
  intro hCB
  have h0 : g 0 = g 0 := rfl
  have hk : g k = g k := rfl
  have hmod : ∀ j, (j + 1) % (k + 1) = if j % (k + 1) < k then j % (k + 1) + 1 else 0 := by
    intro j
    have hlt := Nat.mod_lt j (show 0 < k + 1 by omega)
    rw [Nat.add_mod]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (show 1 < k + 1 by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (show 1 < k + 1 by omega), show j % (k + 1) = k by omega,
        Nat.mod_self]
  have harr : ∀ i, i ≤ k → IsArr (g i) := hw.1
  have hinc : ∀ i j, i ≤ k → j ≤ k → g i ≠ g j → ¬BLe (g i) (g j) := fun i j hi hj hne' hle ↦
    hne' (eq_of_bLe_irreducible hle (harr i hi) (harr j hj))
  refine not_chainBounded_of_zigzag (fun j ↦ g (j % (k + 1)))
    (fun j ↦ if j % (k + 1) < k then m (j % (k + 1)) else W) (fun j ↦ ?_) (fun j ↦ ?_) hR
    (fun j ↦ ?_) (fun j ↦ ?_) (fun j ↦ ?_) hCB
  · split_ifs with h
    · exact (hw.2 _ h).2.1
    · rw [show j % (k + 1) = k by have := Nat.mod_lt j (show 0 < k + 1 by omega); omega, hk]
      exact hγ'
  · rw [hmod]
    split_ifs with h
    · exact (hw.2 _ h).2.2
    · rw [h0]
      exact hγ
  · show (if j % (k + 1) < k then m (j % (k + 1)) else W).2 ≠ 0
    by_cases h : j % (k + 1) < k
    · rw [if_pos h]
      exact hT0 _ (hw.2 _ h).1
    · rw [if_neg h]
      exact hW0
  · have hlt := Nat.mod_lt j (show 0 < k + 1 by omega)
    rw [hmod]
    split_ifs with h
    · exact ⟨hinc _ _ (by omega) (by omega) (hg _ h),
        hinc _ _ (by omega) (by omega) (Ne.symm (hg _ h))⟩
    · have hj : j % (k + 1) = k := by omega
      rw [hj]
      exact ⟨hinc k 0 le_rfl (by omega) (Ne.symm hne),
        hinc 0 k (by omega) le_rfl hne⟩
  · have hlt := Nat.mod_lt j (show 0 < k + 1 by omega)
    rw [hmod]
    by_cases h : j % (k + 1) < k
    · rw [if_pos h, if_pos h]
      by_cases h' : j % (k + 1) + 1 < k
      · rw [if_pos h']
        have hT := (hw.2 _ h).1
        have hT' := (hw.2 _ h').1
        exact ⟨fun hle ↦ hm _ h' (hanti _ _ hT hT' hle),
          fun hle ↦ hm _ h' (hanti _ _ hT' hT hle).symm⟩
      · rw [if_neg h', show j % (k + 1) = k - 1 by omega]
        exact hW2
    · rw [if_neg h, if_neg h, if_pos hk0]
      exact ⟨hW1.2, hW1.1⟩


/-- **No cycles.** Two arrows below `W` joined by a walk through an antichain
`T` of elements incomparable with `W` coincide (chain-boundedness). -/
theorem eq_of_walkConn (hR : RightCancel P) (hCB : ChainBounded P)
    (hanti : ∀ m m', T m → T m' → BLe m m' → m = m') (hT0 : ∀ m, T m → m.2 ≠ 0)
    {W : BMor b} (hW0 : W.2 ≠ 0) (hTW : ∀ m, T m → ¬BLe m W ∧ ¬BLe W m) {γ γ' : BMor b}
    (h : WalkConn T γ γ') (hγ : BLe γ W) (hγ' : BLe γ' W) : γ = γ' := by
  by_contra hne
  obtain ⟨k, g, m, hw, h0, hk, hg, hm⟩ := exists_walk_min h
  subst h0 hk
  have hk0 : 0 < k := by
    by_contra hk0
    exact hne (by rw [show k = 0 by omega])
  exact not_chainBounded_of_walk hR hanti hT0 hW0 hw hk0 hg hm hne hγ hγ'
    (hTW _ (hw.2 0 hk0).1) (hTW _ (hw.2 (k - 1) (by omega)).1) hCB

omit [IsRayCategory P] in
/-- Reversing a walk. -/
lemma IsWalk.reverse {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk T k g m) :
    IsWalk T k (fun i ↦ g (k - i)) (fun i ↦ m (k - 1 - i)) := by
  refine ⟨fun i hi ↦ hw.1 _ (by omega), fun i hi ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hw.2 (k - 1 - i) (by omega)
  refine ⟨h1, ?_, ?_⟩
  · show BLe (g (k - i)) (m (k - 1 - i))
    rwa [show k - i = k - 1 - i + 1 by omega]
  · show BLe (g (k - (i + 1))) (m (k - 1 - i))
    rwa [show k - (i + 1) = k - 1 - i by omega]

omit [IsRayCategory P] in
/-- Dropping the first step of a walk. -/
lemma IsWalk.shift {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk T (k + 1) g m) :
    IsWalk T k (fun i ↦ g (i + 1)) (fun i ↦ m (i + 1)) :=
  ⟨fun i hi ↦ hw.1 _ (by omega), fun i hi ↦ hw.2 _ (by omega)⟩

end Walk

section Sel

variable [IsRayCategory P] {b : P} (β : BMor b)

/-- Fischbacher's `R`: the component of `R₀` containing `β`. -/
def InR (x : BMor b) : Prop := Conn InR0 β x

/-- Maximal elements of `R`. -/
def IsMaxR (μ : BMor b) : Prop := InR β μ ∧ ∀ ν, InR β ν → BLe μ ν → ν = μ

variable {β}

omit [IsRayCategory P] in
lemma InR.inR0 {x : BMor b} (h : InR β x) : InR0 x := Conn.mem_right h

omit [IsRayCategory P] in
lemma InR.of_comp {x y : BMor b} (hx : InR β x) (hy : InR0 y) (h : Comp x y) : InR β y :=
  hx.trans (Conn.of_comp hx.inR0 hy h)

omit [IsRayCategory P] in
lemma IsMaxR.eq_of_bLe {μ μ' : BMor b} (h : IsMaxR β μ) (h' : IsMaxR β μ') (hle : BLe μ μ') :
    μ = μ' := (h.2 μ' h'.1 hle).symm

/-- Every element of `R` lies below a maximal element. -/
lemma exists_isMaxR [Finite P] {x : BMor b} (hx : InR β x) : ∃ μ, IsMaxR β μ ∧ BLe x μ := by
  have : ∀ y : P, Finite (b ⟶ y) := fun y ↦ IsRayCategory.finite_hom b y
  obtain ⟨μ, ⟨hμ, hxμ⟩, hmax⟩ := Set.exists_max_image {y : BMor b | InR β y ∧ BLe x y}
    (fun y ↦ depth y.2) (Set.toFinite _) ⟨x, hx, BLe.refl _⟩
  refine ⟨μ, ⟨hμ, fun ν hν hle ↦ ?_⟩, hxμ⟩
  obtain ⟨ρ, hρ⟩ := hle
  have hν0 := hν.inR0.ne_zero
  by_cases hi : IsIso ρ
  · exact (eq_of_comp_isIso ρ hρ).symm
  · have h1 := depth_lt_comp_right μ.2 ρ (by rw [hρ]; exact hν0) hi
    have h2 := hmax ν ⟨hν, hxμ.trans ⟨ρ, hρ⟩⟩
    rw [hρ] at h1
    omega

/-- The arrows of `R` other than a non-arrow `μ`, and the elements of `R ∖ {μ}`. -/
abbrev Off (β μ : BMor b) (x : BMor b) : Prop := InR β x ∧ x ≠ μ

omit [IsRayCategory P] in
lemma off_of_arr_le {μ α : BMor b} (hμ : InR β μ) (hμa : ¬IsArr μ) (hα : IsArr α)
    (h : BLe α μ) : Off β μ α :=
  ⟨hμ.of_comp (Or.inl hα) (Or.inr h), fun he ↦ hμa (he ▸ hα)⟩

/-- **Well-definedness.** Paths from `b` whose common value lies below `μ` and
which are interlaced, or have a value other than `μ`, start with arrows in one
component of `R ∖ {μ}`. -/
theorem conn_off_of_paths {μ : BMor b} (hμ : InR β μ) (hμa : ¬IsArr μ) :
    ∀ (n : ℕ) {z : RayVert P} (v w : Quiver.Path (RayVert.mk b) z), depth (pathVal v) = n →
      pathVal v = pathVal w → pathVal v ≠ 0 → BLe ⟨z.out, pathVal v⟩ μ →
      (Interlaced v w ∨ (⟨z.out, pathVal v⟩ : BMor b) ≠ μ) →
      ∀ α α', IsFirst v α → IsFirst w α' → Conn (Off β μ) α α' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z v w hn hvw h0 hle hor α α' hα hα'
  have hoffα : Off β μ α := off_of_arr_le hμ hμa (IsFirst.isIrreducible hα) ((IsFirst.bLe hα).trans hle)
  by_cases hi : Interlaced v w
  · -- induction along the interlacing, at fixed value
    have key : ∀ (v' w' : Quiver.Path (RayVert.mk b) z), Interlaced v' w' →
        pathVal v' = pathVal v → ∀ γ γ', IsFirst v' γ → IsFirst w' γ' → Conn (Off β μ) γ γ' := by
      intro v' w' h
      induction h with
      | rel v' w' hs =>
        intro hv γ γ' hγ hγ'
        have hoffγ : Off β μ γ :=
          off_of_arr_le hμ hμa (IsFirst.isIrreducible hγ) ((IsFirst.bLe hγ).trans (hv ▸ hle))
        obtain ⟨a, c, p, v₁, w₁, q, rfl, rfl, hval, hv0, hlen⟩ := hs
        by_cases hp : 0 < p.length
        · obtain ⟨δ, hδ⟩ := exists_isFirst p hp
          have e1 := (IsFirst.unique hγ) (((IsFirst.comp hδ) v₁).comp q)
          have e2 := (IsFirst.unique hγ') (((IsFirst.comp hδ) w₁).comp q)
          have e3 : γ = γ' := e1.trans e2.symm
          subst e3
          exact Conn.refl hoffγ
        · have hp0 : p.length = 0 := by omega
          have ha := Quiver.Path.eq_of_length_zero p hp0
          subst ha
          have hpn := Quiver.Path.eq_nil_of_length_zero p hp0
          subst hpn
          have hq : 0 < q.length := hlen.resolve_left hp
          simp only [Quiver.Path.nil_comp] at hγ hγ' hv
          by_cases hv1 : 0 < v₁.length
          · have hw1 : 0 < w₁.length := by
              by_contra hw
              apply not_isIso_pathVal v₁ hv1
              rw [hval]
              exact isIso_pathVal_of_length_zero w₁ (by omega)
            obtain ⟨δ, hδ⟩ := exists_isFirst v₁ hv1
            obtain ⟨δ', hδ'⟩ := exists_isFirst w₁ hw1
            rw [(IsFirst.unique hγ) ((IsFirst.comp hδ) q), (IsFirst.unique hγ') ((IsFirst.comp hδ') q)]
            have hq' : ¬IsIso (pathVal q) := not_isIso_pathVal q hq
            have hvq : pathVal v₁ ≫ pathVal q ≠ 0 := by
              rw [← pathVal_comp, hv]
              exact h0
            have hd : depth (pathVal v₁) < n := by
              rw [← hn, ← hv, pathVal_comp]
              exact depth_lt_comp_right _ _ hvq hq'
            refine ih _ hd v₁ w₁ rfl hval (fun h ↦ hvq (by rw [h, zero_comp])) ?_ (Or.inr ?_) δ δ'
              hδ hδ'
            · exact BLe.trans ⟨pathVal q, rfl⟩ (by
                have := hle
                rwa [← hv, pathVal_comp] at this)
            · intro he
              have h1 : depth (pathVal v) ≤ depth μ.2 := by
                obtain ⟨ρ, hρ⟩ := hle
                rw [← hρ]
                exact depth_le_comp_right _ _ (by rw [hρ]; exact hμ.inR0.ne_zero)
              have h2 : depth (pathVal v₁) = depth μ.2 := by
                rw [← he]
              omega
          · have hv0' : v₁.length = 0 := by omega
            have hw0 : w₁.length = 0 := by
              by_contra hw
              apply not_isIso_pathVal w₁ (by omega)
              rw [← hval]
              exact isIso_pathVal_of_length_zero v₁ hv0'
            have hc := Quiver.Path.eq_of_length_zero v₁ hv0'
            subst hc
            have e1 := Quiver.Path.eq_nil_of_length_zero v₁ hv0'
            subst e1
            have e2 := Quiver.Path.eq_nil_of_length_zero w₁ hw0
            subst e2
            have e3 := IsFirst.unique hγ hγ'
            subst e3
            exact Conn.refl hoffγ
      | refl v' =>
        intro hv γ γ' hγ hγ'
        rw [(IsFirst.unique hγ) hγ']
        exact Conn.refl (off_of_arr_le hμ hμa (IsFirst.isIrreducible hγ') ((IsFirst.bLe hγ').trans (hv ▸ hle)))
      | symm v' w' h ih' =>
        intro hv γ γ' hγ hγ'
        exact (ih' ((interlaced_val h).trans hv) γ' γ hγ' hγ).symm
      | trans v' u' w' h₁ h₂ ih₁ ih₂ =>
        intro hv γ γ' hγ hγ'
        have hu : 0 < u'.length := by
          by_contra hu
          apply not_isIso_pathVal v' (IsFirst.length_pos hγ)
          rw [interlaced_val h₁]
          exact isIso_pathVal_of_length_zero u' (by omega)
        obtain ⟨δ, hδ⟩ := exists_isFirst u' hu
        exact (ih₁ hv γ δ hγ hδ).trans (ih₂ ((interlaced_val h₁).symm.trans hv) δ γ' hδ hγ')
    exact key v w hi rfl α α' hα hα'
  · have hne : (⟨z.out, pathVal v⟩ : BMor b) ≠ μ := hor.resolve_left hi
    have hess : IsEssVal (⟨z.out, pathVal v⟩ : BMor b) := ⟨v, w, rfl, hvw.symm, h0, hi⟩
    have hR : Off β μ ⟨z.out, pathVal v⟩ := ⟨hμ.of_comp (Or.inr hess) (Or.inr hle), hne⟩
    have hoffα' : Off β μ α' :=
      off_of_arr_le hμ hμa (IsFirst.isIrreducible hα') ((IsFirst.bLe hα').trans (hvw ▸ hle))
    refine (Conn.of_comp hoffα hR (Or.inl (IsFirst.bLe hα))).trans (Conn.of_comp hR hoffα' (Or.inr ?_))
    have := (IsFirst.bLe hα')
    rwa [← hvw] at this

omit [IsRayCategory P] in
/-- The lower terms of a walk through maxima of `R` lie in `R`. -/
lemma IsWalk.inR {k : ℕ} {g m : ℕ → BMor b} (hw : IsWalk (IsMaxR β) k g m) (hk : 0 < k) (i : ℕ)
    (hi : i ≤ k) : InR β (g i) := by
  by_cases hik : i < k
  · exact (hw.2 i hik).1.1.of_comp (Or.inl (hw.1 i hi)) (Or.inr (hw.2 i hik).2.1)
  · have : i = k := by omega
    subst this
    exact (hw.2 (i - 1) (by omega)).1.1.of_comp (Or.inl (hw.1 i hi))
      (Or.inr (by rw [show i = i - 1 + 1 by omega]; exact (hw.2 (i - 1) (by omega)).2.2))

omit [IsRayCategory P] in
/-- A walk through maxima other than a non-arrow `μ` stays in one component of
`R ∖ {μ}`. -/
lemma IsWalk.conn_off {μ : BMor b} (hμa : ¬IsArr μ) {k : ℕ} {g m : ℕ → BMor b}
    (hw : IsWalk (IsMaxR β) k g m) (hk : 0 < k) (hm : ∀ i < k, m i ≠ μ) :
    Conn (Off β μ) (g 0) (g k) := by
  have hoff : ∀ i ≤ k, Off β μ (g i) := fun i hi ↦
    ⟨hw.inR hk i hi, fun he ↦ hμa (he ▸ hw.1 i hi)⟩
  have : ∀ j ≤ k, Conn (Off β μ) (g 0) (g j) := by
    intro j
    induction j with
    | zero => exact fun _ ↦ Conn.refl (hoff 0 (by omega))
    | succ j ih =>
      intro hj
      obtain ⟨hM, h1, h2⟩ := hw.2 j (by omega)
      have hMo : Off β μ (m j) := ⟨hM.1, hm j (by omega)⟩
      exact ((ih (by omega)).trans (Conn.of_comp (hoff j (by omega)) hMo (Or.inl h1))).trans
        (Conn.of_comp hMo (hoff (j + 1) hj) (Or.inr h2))
  exact this k le_rfl

/-- Arrows of `R` are joined by walks through maxima of `R`. -/
lemma walkConn_of_inR [Finite P] {γ γ' : BMor b} (hγ : IsArr γ) (hγR : InR β γ) (hγ' : IsArr γ')
    (hγ'R : InR β γ') : WalkConn (IsMaxR β) γ γ' := by
  have key : ∀ y, Relation.ReflTransGen (Adj InR0) γ y → ∀ δ, IsArr δ → BLe δ y →
      WalkConn (IsMaxR β) γ δ := by
    intro y hy
    induction hy with
    | refl =>
      intro δ hδ hle
      rw [hγ.eq_of_bLe (Or.inl hδ) hle]
      exact walkConn_refl hγ
    | @tail x y hxy hadj ih =>
      intro δ hδ hδy
      obtain ⟨hx, hy, hc⟩ := hadj
      have hyR : InR β y := hγR.trans ⟨hγR.mem_right, hxy.tail ⟨hx, hy, hc⟩⟩
      obtain ⟨M, hM, hyM⟩ := exists_isMaxR hyR
      rcases hc with hc | hc
      · obtain ⟨ε, hε, hεx⟩ := hx.exists_arr
        exact (ih ε hε hεx).snoc hM (hεx.trans (hc.trans hyM)) hδ (hδy.trans hyM)
      · exact ih δ hδ (hδy.trans hc)
  have hc : Conn InR0 γ γ' := hγR.symm.trans hγ'R
  exact key γ' hc.2 γ' hγ' (BLe.refl _)

/-- Paths of value `μ` starting with `γ` and with `α` are interlaced. -/
def Cls (μ γ α : BMor b) : Prop :=
  ∀ v w : Quiver.Path (RayVert.mk b) (RayVert.mk μ.1), pathVal v = μ.2 → pathVal w = μ.2 →
    IsFirst v γ → IsFirst w α → Interlaced v w

/-- The path `γ · ρ`. -/
lemma exists_path_first {γ μ : BMor b} (hγ : IsArr γ) (h : BLe γ μ) (h0 : μ.2 ≠ 0) :
    ∃ v : Quiver.Path (RayVert.mk b) (RayVert.mk μ.1), pathVal v = μ.2 ∧ IsFirst v γ := by
  obtain ⟨ρ, hρ⟩ := h
  have hρ0 : ρ ≠ 0 := fun h ↦ h0 (by rw [← hρ, h, comp_zero])
  let e : RayVert.mk b ⟶ RayVert.mk γ.1 := ⟨γ.2, hγ⟩
  refine ⟨e.toPath.comp
    (pathOf ρ hρ0), ?_,
    ⟨_, _, rfl, rfl⟩⟩
  rw [pathVal_comp, pathVal_toPath, pathVal_pathOf, hρ]

omit [IsRayCategory P] in
lemma Cls.refl (hL : LeftCancel P) {μ γ : BMor b} (h0 : μ.2 ≠ 0) : Cls μ γ γ :=
  fun _ _ hv hw hv' hw' ↦ interlaced_of_isFirst hL hv' hw' (hv.trans hw.symm) (hv ▸ h0)

omit [IsRayCategory P] in
lemma Cls.symm {μ γ α : BMor b} (h : Cls μ γ α) : Cls μ α γ :=
  fun _ _ hv hw hv' hw' ↦ Relation.EqvGen.symm _ _ (h _ _ hw hv hw' hv')

lemma Cls.trans {μ γ α δ : BMor b} (hα : IsArr α) (hαμ : BLe α μ) (h0 : μ.2 ≠ 0)
    (h₁ : Cls μ γ α) (h₂ : Cls μ α δ) : Cls μ γ δ := by
  intro v w hv hw hv' hw'
  obtain ⟨z, hz, hz'⟩ := exists_path_first hα hαμ h0
  exact (h₁ v z hv hz hv' hz').trans _ _ _ (h₂ z w hz hw hz' hw')

/-- Arrows below a common element `x < μ` give interlaced paths of value `μ`. -/
lemma cls_of_le (hL : LeftCancel P) {μ x γ γ' : BMor b} (hγ : IsArr γ) (hγ' : IsArr γ')
    (h : BLe γ x) (h' : BLe γ' x) (hx : BLe x μ) (hne : x ≠ μ) (h0 : μ.2 ≠ 0) : Cls μ γ γ' := by
  intro v w hv hw hv' hw'
  obtain ⟨ρ, hρ⟩ := hx
  have hx0 : x.2 ≠ 0 := fun h ↦ h0 (by rw [← hρ, h, zero_comp])
  have hρ0 : ρ ≠ 0 := fun h ↦ h0 (by rw [← hρ, h, comp_zero])
  have hρi : ¬IsIso ρ := fun hi ↦ hne (eq_of_comp_isIso ρ hρ)
  obtain ⟨v₁, hv₁, hv₁'⟩ := exists_path_first hγ h hx0
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_path_first hγ' h' hx0
  let q := pathOf ρ hρ0
  have hq : pathVal q = ρ := pathVal_pathOf ρ hρ0
  have hvq : pathVal (v₁.comp q) = μ.2 := by rw [pathVal_comp, hv₁, hq, hρ]
  have hwq : pathVal (w₁.comp q) = μ.2 := by rw [pathVal_comp, hw₁, hq, hρ]
  have h1 := interlaced_of_isFirst hL hv' (IsFirst.comp hv₁' q) (hv.trans hvq.symm) (hv ▸ h0)
  have h2 := interlaced_of_isFirst hL (IsFirst.comp hw₁' q) hw' (hwq.trans hw.symm) (hwq ▸ h0)
  have h3 : Interlaced (v₁.comp q) (w₁.comp q) :=
    Relation.EqvGen.rel _ _ (interStep_suffix v₁ w₁ q (length_pathOf_pos ρ hρ0 hρi)
      (hv₁.trans hw₁.symm) (hv₁ ▸ hx0))
  exact h1.trans _ _ _ (h3.trans _ _ _ h2)

/-- **Injectivity.** Arrows below a maximal `μ` in one component of `R ∖ {μ}`
give interlaced paths of value `μ`. -/
theorem cls_of_conn [Finite P] (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    {μ : BMor b} (hμ : IsMaxR β μ) {α α' : BMor b} (hα : IsArr α)
    (hαμ : BLe α μ) (hα'a : IsArr α') (hα'μ : BLe α' μ) (h : Conn (Off β μ) α α') :
    Cls μ α' α := by
  have hμ0 : μ.2 ≠ 0 := hμ.1.inR0.ne_zero
  let T : BMor b → Prop := fun m ↦ IsMaxR β m ∧ m ≠ μ
  have hNC : ∀ γ γ', WalkConn T γ γ' → BLe γ μ → BLe γ' μ → γ = γ' := fun γ γ' hw hγ hγ' ↦
    eq_of_walkConn hR hCB (fun m m' hm hm' hle ↦ hm.1.eq_of_bLe hm'.1 hle)
      (fun m hm ↦ hm.1.1.inR0.ne_zero) hμ0
      (fun m hm ↦ ⟨fun hle ↦ hm.2 (hm.1.eq_of_bLe hμ hle), fun hle ↦ hm.2 (hμ.eq_of_bLe hm.1 hle).symm⟩)
      hw hγ hγ'
  -- a maximal element above an element not below `μ` is in `T`
  have hmaxT : ∀ x, InR β x → ¬BLe x μ → ∃ M, T M ∧ BLe x M := by
    intro x hx hxμ
    obtain ⟨M, hM, hxM⟩ := exists_isMaxR hx
    exact ⟨M, ⟨hM, fun he ↦ hxμ (he ▸ hxM)⟩, hxM⟩
  have key : ∀ y, Relation.ReflTransGen (Adj (Off β μ)) α y →
      (BLe y μ → ∀ γ, IsArr γ → BLe γ y → Cls μ γ α) ∧
      (¬BLe y μ → ∃ γ g, IsArr γ ∧ BLe γ μ ∧ Cls μ γ α ∧ BLe g y ∧ WalkConn T γ g) := by
    intro y hy
    induction hy with
    | refl =>
      refine ⟨fun _ γ hγ hle ↦ ?_, fun h ↦ absurd hαμ h⟩
      rw [hα.eq_of_bLe (Or.inl hγ) hle]
      exact Cls.refl hL hμ0
    | @tail x y _ hadj ih =>
      obtain ⟨hx, hy, hxy⟩ := hadj
      obtain ⟨δ, hδ, hδy⟩ := hy.1.inR0.exists_arr
      by_cases hxμ : BLe x μ
      · obtain ⟨δx, hδx, hδxx⟩ := hx.1.inR0.exists_arr
        have hcx := ih.1 hxμ δx hδx hδxx
        by_cases hyμ : BLe y μ
        · refine ⟨fun _ γ hγ hγy ↦ ?_, fun h ↦ absurd hyμ h⟩
          rcases hxy with hxy | hxy
          · exact (cls_of_le hL hγ hδx hγy (hδxx.trans hxy) hyμ hy.2 hμ0).trans hδx
              (hδxx.trans hxμ) hμ0 hcx
          · exact ih.1 hxμ γ hγ (hγy.trans hxy)
        · have hxy' : BLe x y := hxy.resolve_right (fun h ↦ hyμ (h.trans hxμ))
          exact ⟨fun h ↦ absurd h hyμ, fun _ ↦ ⟨δx, δx, hδx, hδxx.trans hxμ, hcx,
            hδxx.trans hxy', walkConn_refl hδx⟩⟩
      · obtain ⟨γ, g, hγ, hγμ, hcγ, hgx, hw⟩ := ih.2 hxμ
        obtain ⟨M, hM, hxM⟩ := hmaxT x hx.1 hxμ
        by_cases hyμ : BLe y μ
        · have hyx : BLe y x := hxy.resolve_left (fun h ↦ hxμ (h.trans hyμ))
          refine ⟨fun _ γ' hγ' hγ'y ↦ ?_, fun h ↦ absurd hyμ h⟩
          have hw' : WalkConn T γ γ' :=
            hw.snoc hM (hgx.trans hxM) hγ' (hγ'y.trans (hyx.trans hxM))
          rw [← hNC γ γ' hw' hγμ (hγ'y.trans hyμ)]
          exact hcγ
        · refine ⟨fun h ↦ absurd h hyμ, fun _ ↦ ?_⟩
          rcases hxy with hxy | hxy
          · exact ⟨γ, g, hγ, hγμ, hcγ, hgx.trans hxy, hw⟩
          · exact ⟨γ, δ, hγ, hγμ, hcγ, hδy,
              hw.snoc hM (hgx.trans hxM) hδ (hδy.trans (hxy.trans hxM))⟩
  exact (key α' h.2).1 hα'μ α' hα'a (BLe.refl _)

/-- Arrows of `R` below `τ` (Fischbacher's non-efficient arrows). -/
def IsNArr (β τ α : BMor b) : Prop := IsArr α ∧ InR β α ∧ BLe α τ

/-- A walk through maxima of `R` between non-efficient arrows lying in different
components of `R ∖ {μ}`. -/
def BadWalk (β τ μ : BMor b) (k : ℕ) : Prop :=
  ∃ g m : ℕ → BMor b, IsWalk (IsMaxR β) k g m ∧ IsNArr β τ (g 0) ∧ IsNArr β τ (g k) ∧
    ¬Conn (Off β μ) (g 0) (g k)

/-- The case of Claim 1 where `τ` is comparable with the first maximum. -/
lemma claim1_first [Finite P] (hL : LeftCancel P) {τ μ : BMor b} (hμ : IsMaxR β μ)
    (hμa : ¬IsArr μ) {e : BMor b} (he : ¬BLe e τ) (heμ : BLe e μ) {k : ℕ}
    (hmin : ∀ k' < k, ¬BadWalk β τ μ k') {g m : ℕ → BMor b} (hw : IsWalk (IsMaxR β) k g m)
    (hφ : IsNArr β τ (g 0)) (hψ : IsNArr β τ (g k)) (hc : ¬Conn (Off β μ) (g 0) (g k))
    (hk : 0 < k) (hcomp : Comp τ (m 0)) : False := by
  have hμ0 : μ.2 ≠ 0 := hμ.1.inR0.ne_zero
  have hoff : ∀ i ≤ k, Off β μ (g i) := fun i hi ↦
    ⟨hw.inR hk i hi, fun h ↦ hμa (h ▸ hw.1 i hi)⟩
  rcases hcomp with hτm | hmτ
  · -- `τ ≤ m 0`: a walk of length one, so `k = 1` and `m 0 = μ`
    have hψm : BLe (g k) (m 0) := hψ.2.2.trans hτm
    have hk1 : k = 1 := by
      by_contra hk1
      refine hmin 1 (by omega) ⟨fun i ↦ if i = 0 then g 0 else g k, fun _ ↦ m 0,
        ⟨fun i _ ↦ ?_, fun i hi ↦ ?_⟩, by simpa using hφ, by simpa using hψ, by simpa using hc⟩
      · show IsArr (if i = 0 then g 0 else g k)
        split_ifs
        · exact hw.1 0 (by omega)
        · exact hw.1 k le_rfl
      · have : i = 0 := by omega
        subst this
        exact ⟨(hw.2 0 hk).1, by simpa using (hw.2 0 hk).2.1, by simpa using hψm⟩
    subst hk1
    have hm0 : m 0 = μ := by
      by_contra hne
      exact hc (hw.conn_off hμa hk (fun i hi ↦ by rw [show i = 0 by omega]; exact hne))
    rw [hm0] at hτm
    have hτμ : τ ≠ μ := fun h ↦ he (h ▸ heμ)
    have hcls := cls_of_le hL hφ.1 hψ.1 hφ.2.2 hψ.2.2 hτm hτμ hμ0
    obtain ⟨v, hv, hv'⟩ := exists_path_first hφ.1 (hφ.2.2.trans hτm) hμ0
    obtain ⟨w, hw', hw''⟩ := exists_path_first hψ.1 (hψ.2.2.trans hτm) hμ0
    apply hc
    refine conn_off_of_paths hμ.1 hμa _ v w rfl (hv.trans hw'.symm) (hv ▸ hμ0) ?_
      (Or.inl (hcls v w hv hw' hv' hw'')) _ _ hv' hw''
    rw [hv]
    exact BLe.refl _
  · -- `m 0 ≤ τ`: the next arrow is also non-efficient
    have hm0 : m 0 ≠ μ := fun h ↦ he ((heμ.trans (h ▸ BLe.refl _)).trans hmτ)
    have hk2 : 1 < k := by
      by_contra hk2
      exact hc (hw.conn_off hμa hk (fun i hi ↦ by rw [show i = 0 by omega]; exact hm0))
    have hN1 : IsNArr β τ (g 1) := ⟨hw.1 1 (by omega), hw.inR hk 1 (by omega),
      (hw.2 0 hk).2.2.trans hmτ⟩
    have hMo : Off β μ (m 0) := ⟨(hw.2 0 hk).1.1, hm0⟩
    have hc01 : Conn (Off β μ) (g 0) (g 1) :=
      (Conn.of_comp (hoff 0 (by omega)) hMo (Or.inl (hw.2 0 hk).2.1)).trans
        (Conn.of_comp hMo (hoff 1 (by omega)) (Or.inr (hw.2 0 hk).2.2))
    have hw' := (show IsWalk (IsMaxR β) (k - 1 + 1) g m by rwa [Nat.sub_add_cancel hk]).shift
    refine hmin (k - 1) (by omega) ⟨_, _, hw', hN1, ?_, fun h ↦ hc (hc01.trans ?_)⟩
    · simpa [Nat.sub_add_cancel hk] using hψ
    · simpa [Nat.sub_add_cancel hk] using h

/-- **Claim 1** (Fischbacher 2.1 c)). If a maximum `μ` of `R` lies above an
arrow `e ≰ τ`, all arrows of `R` below `τ` lie in one component of `R ∖ {μ}`. -/
theorem claim1 [Finite P] (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    {τ μ : BMor b} (hτ0 : τ.2 ≠ 0) (hμ : IsMaxR β μ) (hμa : ¬IsArr μ) {e : BMor b}
    (he : ¬BLe e τ) (heμ : BLe e μ) {φ ψ : BMor b} (hφ : IsNArr β τ φ) (hψ : IsNArr β τ ψ) :
    Conn (Off β μ) φ ψ := by
  classical
  by_contra hc
  have hex : ∃ k, BadWalk β τ μ k := by
    obtain ⟨k, g, m, hw, h0, hk⟩ := walkConn_of_inR hφ.1 hφ.2.1 hψ.1 hψ.2.1
    subst h0 hk
    exact ⟨k, g, m, hw, hφ, hψ, hc⟩
  obtain ⟨g, m, hw, hg0, hgk, hc'⟩ := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hmin : ∀ k' < k, ¬BadWalk β τ μ k' := fun k' hk' ↦ Nat.find_min hex hk'
  have hoff : ∀ i ≤ k, 0 < k → Off β μ (g i) := fun i hi hk ↦
    ⟨hw.inR hk i hi, fun h ↦ hμa (h ▸ hw.1 i hi)⟩
  have hk : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this] at hc'
    exact hc' (Conn.refl ⟨hg0.2.1, fun h ↦ hμa (h ▸ hg0.1)⟩)
  have hne : g 0 ≠ g k := fun h ↦ hc' (by rw [← h]; exact Conn.refl (hoff 0 (by omega) hk))
  -- no consecutive repetitions (minimality)
  have hgr : ∀ i < k, g i ≠ g (i + 1) := by
    intro i hi he'
    have e0 : (fun j ↦ if j ≤ i then g j else g (j + 1)) 0 = g 0 := by simp
    have ek : (fun j ↦ if j ≤ i then g j else g (j + 1)) (k - 1) = g k := by
      show (if k - 1 ≤ i then g (k - 1) else g (k - 1 + 1)) = g k
      split_ifs with h1
      · rw [show k - 1 = i by omega, he', show i + 1 = k by omega]
      · rw [show k - 1 + 1 = k by omega]
    refine hmin (k - 1) (by omega) ⟨_, _, hw.del_g i hi he', ?_, ?_, ?_⟩
    · exact (congrArg (IsNArr β τ) e0).mpr hg0
    · exact (congrArg (IsNArr β τ) ek).mpr hgk
    · exact fun h ↦ hc' ((congrArg₂ (Conn (Off β μ)) e0 ek).mp h)
  have hmr : ∀ i, i + 1 < k → m i ≠ m (i + 1) := by
    intro i hi he'
    have e0 : (fun j ↦ if j ≤ i then g j else g (j + 1)) 0 = g 0 := by simp
    have ek : (fun j ↦ if j ≤ i then g j else g (j + 1)) (k - 1) = g k := by
      show (if k - 1 ≤ i then g (k - 1) else g (k - 1 + 1)) = g k
      rw [if_neg (by omega), show k - 1 + 1 = k by omega]
    refine hmin (k - 1) (by omega) ⟨_, _, hw.del_m i hi he', ?_, ?_, ?_⟩
    · exact (congrArg (IsNArr β τ) e0).mpr hg0
    · exact (congrArg (IsNArr β τ) ek).mpr hgk
    · exact fun h ↦ hc' ((congrArg₂ (Conn (Off β μ)) e0 ek).mp h)
  by_cases h1 : Comp τ (m 0)
  · exact claim1_first hL hμ hμa he heμ hmin hw hg0 hgk hc' hk h1
  by_cases h2 : Comp τ (m (k - 1))
  · refine claim1_first hL hμ hμa he heμ hmin hw.reverse ?_ ?_ ?_ hk ?_
    · simpa using hgk
    · simpa using hg0
    · simpa using fun h ↦ hc' h.symm
    · simpa using h2
  exact not_chainBounded_of_walk hR (fun m m' hm hm' hle ↦ hm.eq_of_bLe hm' hle)
    (fun m hm ↦ hm.1.inR0.ne_zero) hτ0 hw hk hgr hmr hne hg0.2.2 hgk.2.2
    ⟨fun h ↦ h1 (Or.inr h), fun h ↦ h1 (Or.inl h)⟩ ⟨fun h ↦ h2 (Or.inr h), fun h ↦ h2 (Or.inl h)⟩
    hCB

/-- Essential values are not arrows. -/
lemma IsEssVal.not_isArr {ν : BMor b} (h : IsEssVal ν) : ¬IsArr ν := by
  intro ha
  obtain ⟨v, w, hv, hw, -, hi⟩ := h
  have key : ∀ {z : RayVert P} (v : Quiver.Path (RayVert.mk b) z), IsIrreducible (pathVal v) →
      ∃ e : RayVert.mk b ⟶ z, v = e.toPath := by
    intro z v hv
    cases v with
    | nil => exact absurd (IsIso.id _) hv.2.1
    | cons v₁ e =>
      by_cases h1 : v₁.length = 0
      · have hb := Quiver.Path.eq_of_length_zero v₁ h1
        subst hb
        rw [Quiver.Path.eq_nil_of_length_zero v₁ h1]
        exact ⟨e, rfl⟩
      · exfalso
        rcases hv.2.2 _ _ _ rfl with h2 | h2
        · exact not_isIso_pathVal v₁ (by omega) h2
        · exact e.2.2.1 h2
  obtain ⟨e, rfl⟩ := key v (by rw [hv]; exact ha)
  obtain ⟨e', rfl⟩ := key w (by rw [hw]; exact ha)
  have : e = e' := Subtype.ext (by
    have h1 := hv.trans hw.symm
    rwa [pathVal_toPath, pathVal_toPath] at h1)
  subst this
  exact hi (.refl _)

/-- If `β` lies below an essential value, maxima of `R` are not arrows. -/
lemma IsMaxR.not_isArr {ν : BMor b} (hβ : IsArr β) (hν : IsEssVal ν) (hβν : BLe β ν)
    {m : BMor b} (hm : IsMaxR β m) : ¬IsArr m := by
  intro hma
  -- every element connected to `m` in `R₀` equals `m`
  have key : ∀ y, Relation.ReflTransGen (Adj InR0) m y → y = m := by
    intro y hy
    induction hy with
    | refl => rfl
    | @tail x y _ hadj ih =>
      subst ih
      obtain ⟨-, hy, hc⟩ := hadj
      rcases hc with hc | hc
      · exact hm.2 y (hm.1.of_comp hy (Or.inl hc)) hc
      · exact hma.eq_of_bLe hy hc
  have hβm : β = m := key β (hm.1.symm).2
  subst hβm
  have := hm.2 ν (hm.1.of_comp (Or.inr hν) (Or.inl hβν)) hβν
  exact hν.not_isArr (this ▸ hβ)

omit [IsRayCategory P] in
/-- A component of `R ∖ {μ}` meets an element comparable with `μ`. -/
lemma exists_comp_of_off {μ d : BMor b} (hμ : InR β μ) (hd : Off β μ d) :
    ∃ z, Conn (Off β μ) d z ∧ Comp z μ := by
  have key : ∀ y, Relation.ReflTransGen (Adj InR0) d y →
      Conn (Off β μ) d y ∨ ∃ z, Conn (Off β μ) d z ∧ Comp z μ := by
    intro y hy
    induction hy with
    | refl => exact Or.inl (Conn.refl hd)
    | @tail x y _ hadj ih =>
      rcases ih with ih | ih
      · obtain ⟨-, hy, hc⟩ := hadj
        by_cases hyμ : y = μ
        · subst hyμ
          exact Or.inr ⟨x, ih, hc⟩
        · exact Or.inl (ih.trans (Conn.of_comp ih.mem_right
            ⟨ih.mem_right.1.of_comp hy hc, hyμ⟩ hc))
      · exact Or.inr ih
  rcases key μ (hd.1.symm.trans hμ).2 with h | h
  · exact absurd rfl h.mem_right.2
  · exact h

omit [IsRayCategory P] in
/-- Restricting a component of `R ∖ {μ}` that avoids `μ'` to `R ∖ {μ'}`. -/
lemma Conn.off_change {μ μ' d x : BMor b} (hμ' : InR β μ) (hμμ' : μ ≠ μ')
    (h : Conn (Off β μ) d x) (hav : ¬Conn (Off β μ) d μ') : Conn (Off β μ') d x := by
  have hoff : ∀ z, Conn (Off β μ) d z → Off β μ' z := fun z hz ↦
    ⟨hz.mem_right.1, fun he ↦ hav (he ▸ hz)⟩
  obtain ⟨hd, h⟩ := h
  have : ∀ y, Relation.ReflTransGen (Adj (Off β μ)) d y → Conn (Off β μ') d y := by
    intro y hy
    induction hy with
    | refl => exact Conn.refl (hoff d (Conn.refl hd))
    | @tail x y hxy hadj ih =>
      exact ih.trans (Conn.of_comp (hoff x ⟨hd, hxy⟩) (hoff y ⟨hd, hxy.tail hadj⟩) hadj.2.2)
  exact this x h

/-- **Fischbacher's selection** (Lemma 2.1 b)–d)). Let `β` be an arrow from `b`
with `β ≰ τ` below an essential value. Then there are a maximum `μ` of `R`, a
path `u` of value `μ` and a nonempty set `A` of arrows `α ≤ μ` with `α ≰ τ`
such that every essential value above some `α ∈ A` lies below `μ`, and a path
of value `μ` starts with an arrow of `A` exactly when it is not interlaced
with `u`. -/
theorem exists_selection [Finite P] (hL : LeftCancel P) (hR : RightCancel P)
    (hCB : ChainBounded P) {τ : BMor b} (hτ0 : τ.2 ≠ 0) (hβ : IsArr β) (hβτ : ¬BLe β τ)
    {ν : BMor b} (hν : IsEssVal ν) (hβν : BLe β ν) :
    ∃ (μ : BMor b) (u : Quiver.Path (RayVert.mk b) (RayVert.mk μ.1)) (A : BMor b → Prop),
      μ.2 ≠ 0 ∧ pathVal u = μ.2 ∧
      (∀ α, A α → IsArr α ∧ ¬BLe α τ ∧ BLe α μ) ∧
      (∀ α, A α → ∀ ν', IsEssVal ν' → BLe α ν' → BLe ν' μ) ∧
      (∀ w : Quiver.Path (RayVert.mk b) (RayVert.mk μ.1), pathVal w = μ.2 → ∀ α, IsFirst w α →
        (A α ↔ ¬Interlaced w u)) ∧
      ∃ α, A α := by
  classical
  have : ∀ y : P, Finite (b ⟶ y) := fun y ↦ IsRayCategory.finite_hom b y
  have hmaxna : ∀ m, IsMaxR β m → ¬IsArr m := fun m hm ↦ hm.not_isArr hβ hν hβν
  have hβR : InR β β := Conn.refl (Or.inl hβ)
  have hνR : InR β ν := hβR.of_comp (Or.inr hν) (Or.inl hβν)
  -- good pairs `(μ, d)`: the component of `d` in `R ∖ {μ}` contains all N-arrows
  let Good : BMor b × BMor b → Prop := fun p ↦
    IsMaxR β p.1 ∧ Off β p.1 p.2 ∧ ∀ φ, IsNArr β τ φ → Conn (Off β p.1) p.2 φ
  have hgood : ∃ p, Good p := by
    obtain ⟨μ₀, hμ₀, hνμ₀⟩ := exists_isMaxR hνR
    have hoffβ : Off β μ₀ β := ⟨hβR, fun h ↦ hmaxna μ₀ hμ₀ (h ▸ hβ)⟩
    by_cases hN : ∃ φ, IsNArr β τ φ
    · obtain ⟨φ, hφ⟩ := hN
      refine ⟨(μ₀, φ), hμ₀, ⟨hφ.2.1, fun h ↦ hmaxna μ₀ hμ₀ ?_⟩, fun ψ hψ ↦
        claim1 hL hR hCB hτ0 hμ₀ (hmaxna μ₀ hμ₀) hβτ (hβν.trans hνμ₀) hφ hψ⟩
      change φ = μ₀ at h
      exact h ▸ hφ.1
    · exact ⟨(μ₀, β), hμ₀, hoffβ, fun φ hφ ↦ absurd ⟨φ, hφ⟩ hN⟩
  obtain ⟨⟨μ, d⟩, ⟨hμ, hd, hNd⟩, hopt⟩ := Set.exists_max_image {p | Good p}
    (fun p ↦ Set.ncard {x | Conn (Off β p.1) p.2 x}) (Set.toFinite _) hgood
  dsimp only at hμ hd hNd hopt
  have hμa := hmaxna μ hμ
  have hμ0 : μ.2 ≠ 0 := hμ.1.inR0.ne_zero
  -- every other maximum lies in the component of `d`
  have hP1 : ∀ M, IsMaxR β M → M ≠ μ → Conn (Off β μ) d M := by
    intro M hM hMμ
    by_contra hc
    obtain ⟨z, hz, hzμ⟩ := exists_comp_of_off hμ.1 hd
    have hzM : Conn (Off β M) d z := hz.off_change hμ.1 (Ne.symm hMμ) hc
    have hμM : Off β M μ := ⟨hμ.1, Ne.symm hMμ⟩
    have hdμ : Conn (Off β M) d μ := hzM.trans (Conn.of_comp hzM.mem_right hμM hzμ)
    have hgood' : Good (M, μ) := ⟨hM, hμM, fun φ hφ ↦
      hdμ.symm.trans ((hNd φ hφ).off_change hμ.1 (Ne.symm hMμ) hc)⟩
    have hsub : {x | Conn (Off β μ) d x} ⊂ {x | Conn (Off β M) μ x} := by
      refine ⟨fun x hx ↦ hdμ.symm.trans (Conn.off_change hμ.1 (Ne.symm hMμ) hx hc), fun h ↦ ?_⟩
      have := (h (Conn.refl hμM : Conn (Off β M) μ μ)).mem_right
      exact this.2 rfl
    have := Set.ncard_lt_ncard hsub (Set.toFinite _)
    have h2 := hopt (M, μ) hgood'
    dsimp only at h2
    omega
  -- the path `u`
  obtain ⟨z, hz, hzμ⟩ := exists_comp_of_off hμ.1 hd
  have hzμ' : BLe z μ := hzμ.resolve_right (fun h ↦ hz.mem_right.2 (hμ.2 z hz.mem_right.1 h))
  obtain ⟨δ, hδ, hδz⟩ := hz.mem_right.1.inR0.exists_arr
  have hδμ : BLe δ μ := hδz.trans hzμ'
  have hoffδ : Off β μ δ := off_of_arr_le hμ.1 hμa hδ hδμ
  have hdδ : Conn (Off β μ) d δ := hz.trans (Conn.of_comp hz.mem_right hoffδ (Or.inr hδz))
  obtain ⟨u, hu, huδ⟩ := exists_path_first hδ hδμ hμ0
  let A : BMor b → Prop := fun α ↦ IsArr α ∧ BLe α μ ∧ ¬Conn (Off β μ) d α
  have hS5 : ∀ w : Quiver.Path (RayVert.mk b) (RayVert.mk μ.1), pathVal w = μ.2 → ∀ α,
      IsFirst w α → (A α ↔ ¬Interlaced w u) := by
    intro w hw α hα
    have hαa : IsArr α := hα.isIrreducible
    have hαμ : BLe α μ := by
      have := hα.bLe
      rwa [hw] at this
    refine ⟨fun hA hi ↦ hA.2.2 ?_, fun hi ↦ ⟨hαa, hαμ, fun hc ↦ hi ?_⟩⟩
    · have := conn_off_of_paths hμ.1 hμa _ w u rfl (hw.trans hu.symm) (hw ▸ hμ0)
        (by rw [hw]; exact BLe.refl _) (Or.inl hi) α δ hα huδ
      exact hdδ.trans this.symm
    · exact cls_of_conn hL hR hCB hμ hδ hδμ hαa hαμ (hdδ.symm.trans hc) w u hw hu hα huδ
  refine ⟨μ, u, A, hμ0, hu, fun α hA ↦ ⟨hA.1, fun hτ ↦ hA.2.2 (hNd α ⟨hA.1,
    hμ.1.of_comp (Or.inl hA.1) (Or.inr hA.2.1), hτ⟩), hA.2.1⟩, fun α hA ν' hν' hαν' ↦ ?_, hS5, ?_⟩
  · have hαR : InR β α := hμ.1.of_comp (Or.inl hA.1) (Or.inr hA.2.1)
    have hν'R : InR β ν' := hαR.of_comp (Or.inr hν') (Or.inl hαν')
    obtain ⟨M, hM, hν'M⟩ := exists_isMaxR hν'R
    by_cases hMμ : M = μ
    · exact hMμ ▸ hν'M
    · exfalso
      have hMo : Off β μ M := ⟨hM.1, hMμ⟩
      exact hA.2.2 ((hP1 M hM hMμ).trans
        (Conn.of_comp hMo (off_of_arr_le hμ.1 hμa hA.1 hA.2.1) (Or.inr (hαν'.trans hν'M))))
  · have hess : IsEssVal μ := hμ.1.inR0.resolve_left hμa
    obtain ⟨v, w, hv, hw, -, hi, hvl, hwl⟩ := hess.exists
    by_cases hvu : Interlaced v u
    · obtain ⟨α, hα⟩ := exists_isFirst w hwl
      refine ⟨α, (hS5 w hw α hα).2 fun hwu ↦ hi ?_⟩
      exact hvu.trans _ _ _ (Relation.EqvGen.symm _ _ hwu)
    · obtain ⟨α, hα⟩ := exists_isFirst v hvl
      exact ⟨α, (hS5 v hv α hα).2 hvu⟩

end Sel

end RayCat

end LargeIndecomposable
