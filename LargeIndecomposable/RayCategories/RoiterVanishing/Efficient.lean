module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Fischbacher
public import Mathlib.Data.Set.Finite.List

/-!
# Efficient tackles and the hypothesis (K')

Fischbacher's tackles end in an arrow lying in an essential contour
(`RayCat.InEss`). For an efficient tackle whose last link is a valley, with
last arrow `β` and previous entry `τ`, replacing `β` by any arrow `γ ≰ τ`
lying in an essential contour gives an efficient tackle again, so the key
lemma shows (K'): such `γ` occur in essential contours only first
(`RayCat.keyProp_of_efficient`). Efficient tackles exist in finite
chain-bounded ray categories with an essential contour
(`RayCat.exists_efficient`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The morphism `f` is an arrow lying in an essential contour. -/
def InEss (f : RayMor P) : Prop :=
  ∃ (x y : RayVert P) (v w : Quiver.Path x y) (p : Quiver.Path x (RayVert.mk f.1))
    (e : RayVert.mk f.1 ⟶ RayVert.mk f.2.1) (q : Quiver.Path (RayVert.mk f.2.1) y),
    pathVal v = pathVal w ∧ pathVal v ≠ 0 ∧ ¬Interlaced v w ∧ e.1 = f.2.2 ∧ v = (p.cons e).comp q

/-- A path whose value is irreducible is a single arrow. -/
lemma eq_toPath_of_isIrreducible {x : RayVert P} : ∀ {z : RayVert P} (v : Quiver.Path x z),
    IsIrreducible (pathVal v) → ∃ e : x ⟶ z, v = e.toPath
  | _, .nil, hv => absurd (IsIso.id _) hv.2.1
  | _, .cons v₁ e, hv => by
    by_cases h1 : v₁.length = 0
    · have hb := Quiver.Path.eq_of_length_zero v₁ h1
      subst hb
      rw [Quiver.Path.eq_nil_of_length_zero v₁ h1]
      exact ⟨e, rfl⟩
    · exfalso
      rcases hv.2.2 _ _ _ rfl with h2 | h2
      · exact not_isIso_pathVal v₁ (by omega) h2
      · exact e.2.2.1 h2

/-- Irreducible morphisms have depth one. -/
lemma depth_of_isIrreducible {x y : P} {f : x ⟶ y} (hf : IsIrreducible f) : depth f = 1 := by
  obtain ⟨p, hl, hp⟩ := exists_path_depth hf.1
  obtain ⟨e, rfl⟩ := eq_toPath_of_isIrreducible p (hp ▸ hf)
  rw [← hl]
  rfl

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma getElem_eq_cast {f g : RayMor P} (h : f = g) (hX : f.1 = g.1) (hZ : f.2.1 = g.2.1) :
    g.2.2 = eqToHom hX.symm ≫ f.2.2 ≫ eqToHom hZ := by
  subst h
  simp

omit [IsRayCategory P] in
/-- Replacing the last entry of a chain. -/
lemma isChain_replace_last {o : ℕ} (l : List (RayMor P)) (hl : IsChain o l) (m : ℕ)
    (hm : m + 1 = l.length) (f : RayMor P) (hf : f.2.2 ≠ 0)
    (hlink : ∀ h : 0 < m, Link (m - 1 + o) (l[m - 1]'(by omega)) f) :
    IsChain o (l.take m ++ [f]) := by
  refine ⟨fun g hg ↦ ?_, fun j hj ↦ ?_⟩
  · rcases List.mem_append.1 hg with hg | hg
    · exact hl.1 g (List.mem_of_mem_take hg)
    · rw [List.mem_singleton.1 hg]
      exact hf
  · have hlen : (l.take m ++ [f]).length = m + 1 := by simp; omega
    rw [hlen] at hj
    rcases Nat.lt_or_ge (j + 1) m with h1 | h1
    · simp only [List.getElem_append_left (by simp; omega : j < (l.take m).length),
        List.getElem_append_left (by simp; omega : j + 1 < (l.take m).length), List.getElem_take]
      exact hl.2 j (by omega)
    · have hj1 : j + 1 = m := by omega
      subst hj1
      rw [List.getElem_append_left (by simp; omega : j < (l.take (j + 1)).length),
        List.getElem_append_right (by simp)]
      simp only [List.getElem_take, List.length_take, Nat.min_eq_left (by omega : j + 1 ≤ l.length),
        Nat.sub_self, List.getElem_cons_zero]
      exact hlink (by omega)

omit [IsRayCategory P] in
lemma efficiency_replace_last (l : List (RayMor P)) (m : ℕ) (hm : m + 1 = l.length)
    (f : RayMor P) (hf : depth f.2.2 = depth (l[m]'(by omega)).2.2) :
    efficiency (l.take m ++ [f]) = efficiency l := by
  unfold efficiency
  rw [List.map_append, List.map_take]
  conv_rhs => rw [← List.take_append_drop m (l.map fun f ↦ depth f.2.2)]
  congr 1
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [hf, List.drop_eq_nil_of_le (by simp; omega : (l.map fun f ↦ depth f.2.2).length ≤ m + 1)]

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma exists_eq_cons {V : Type*} [Quiver V] {x y : V} (w : Quiver.Path x y) (hw : 0 < w.length) :
    ∃ (z : V) (w₂ : Quiver.Path x z) (ζ : z ⟶ y), w = w₂.cons ζ := by
  cases w with
  | nil => simp at hw
  | cons w₂ ζ => exact ⟨_, w₂, ζ, rfl⟩

/-- **(K') from the key lemma.** -/
theorem keyProp_of_efficient (hL : LeftCancel P) (hR : RightCancel P) {o : ℕ}
    {l : List (RayMor P)} (hl : IsEfficient InEss o l) (m : ℕ) (hm : m + 1 = l.length)
    (hev : (m + o) % 2 = 0) (τ : BMor (l[m]'(by omega)).1)
    (hτ : (m = 0 ∧ τ = ⟨_, 𝟙 _⟩) ∨ ∃ (h0 : 0 < m) (h : (l[m - 1]'(by omega)).1 = (l[m]'(by omega)).1),
      τ = ⟨(l[m - 1]'(by omega)).2.1, eqToHom h.symm ≫ (l[m - 1]'(by omega)).2.2⟩) :
    KeyProp (l[m]'(by omega)).1 τ := by
  intro γ hγ hγτ x y v w hvw h0 hi p e q he hv
  let γ' : RayMor P := ⟨_, γ.1, γ.2⟩
  have hchain : IsChain o (l.take m ++ [γ']) := by
    refine isChain_replace_last l hl.1.choose_spec.1 m hm γ' hγ.1 fun h0m ↦ ?_
    obtain ⟨h0', h, hτeq⟩ := hτ.resolve_left (fun h' ↦ by omega)
    subst hτeq
    simp only [Link, show (m - 1 + o) % 2 ≠ 0 by omega, ↓reduceIte]
    refine ⟨h, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      rcases hγ.2.2 _ (eqToHom h.symm ≫ (l[m - 1]'(by omega)).2.2) c
        (by rw [Category.assoc]; exact hc.symm) with h2 | h2
      · exact not_isIso_entry hl.1 (m - 1) _ (IsIso.of_isIso_comp_left (eqToHom h.symm) _)
      · exact hγτ ⟨inv c, by
          show _ = eqToHom h.symm ≫ (l[m - 1]'(by omega)).2.2
          rw [← hc]
          simp⟩
    · rintro ⟨c, hc⟩
      exact hγτ ⟨c, by
        show _ = eqToHom h.symm ≫ (l[m - 1]'(by omega)).2.2
        rw [← hc]
        simp
        rfl⟩
  have hlast : (l.take m ++ [γ'])[m]'(by simp; omega) = γ' := by
    rw [List.getElem_append_right (by simp)]
    simp [show (l.take m).length = m by simp; omega]
  have hirr : IsIrreducible (l[m]'(by omega)).2.2 := by
    obtain ⟨hne, -, hirr, -⟩ := hl.1
    have e1 : l.getLast hne = l[m]'(by omega) := by
      simp [List.getLast_eq_getElem, show l.length - 1 = m by omega]
    rwa [e1] at hirr
  have heff : efficiency (l.take m ++ [γ']) = efficiency l :=
    efficiency_replace_last l m hm γ' (by rw [depth_of_isIrreducible hγ,
      depth_of_isIrreducible hirr])
  have hl' : IsEfficient InEss o (l.take m ++ [γ']) := by
    refine ⟨⟨by simp, hchain, ?_, ?_⟩, fun l'' hl'' ↦ heff ▸ hl.2 l'' hl''⟩
    · rw [List.getLast_append_singleton]
      exact hγ
    · rw [List.getLast_append_singleton]
      exact ⟨x, y, v, w, p, e, q, hvw, h0, hi, he, hv⟩
  -- the first and the last arrow of `w`
  have hwl : 0 < w.length := by
    by_contra hw
    apply not_isIso_pathVal v (by rw [hv]; simp)
    rw [hvw]
    exact isIso_pathVal_of_length_zero w (by omega)
  obtain ⟨yα, α, w₃, -, hwα⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ w
    (Nat.succ_pred_eq_of_pos hwl).symm
  obtain ⟨yζ, w₂, ζ, hwζ⟩ := exists_eq_cons w hwl
  have hni : ¬Interlaced w v := fun h ↦ hi (Relation.EqvGen.symm _ _ h)
  refine key_hook hL hR hl' m (by simp; omega) hev α w₃ hwα
    ⟨x, y, w, v, .nil, α, w₃, hvw.symm, hvw ▸ h0, hni, rfl, hwα⟩ w₂ ζ hwζ
    ⟨x, y, w, v, w₂, ζ, .nil, hvw.symm, hvw ▸ h0, hni, rfl, hwζ⟩ hvw h0 hi _ γ.1
    (congrArg (fun f : RayMor P ↦ f.1) hlast) (congrArg (fun f : RayMor P ↦ f.2.1) hlast) p
    e.toPath q ?_ hv
  rw [pathVal_toPath, he]
  exact getElem_eq_cast hlast (congrArg (fun f : RayMor P ↦ f.1) hlast)
    (congrArg (fun f : RayMor P ↦ f.2.1) hlast)

/-- The last entry of a tackle as an element of the list. -/
lemma IsTackle.getLast_eq {adm : RayMor P → Prop} {o : ℕ} {l : List (RayMor P)}
    (hl : IsTackle adm o l) (m : ℕ) (hm : m + 1 = l.length) :
    l.getLast hl.choose = l[m]'(by omega) := by
  simp [List.getLast_eq_getElem, show l.length - 1 = m by omega]

/-- Depths of nonzero morphisms are bounded in a finite ray category. -/
lemma depth_le_card [Finite P] {x y : P} {f : x ⟶ y} (hf : f ≠ 0) :
    depth f ≤ Nat.card (RayMor P) := by
  have : ∀ x y : P, Finite (x ⟶ y) := IsRayCategory.finite_hom
  obtain ⟨p, hl, hp⟩ := exists_path_depth hf
  have h1 := length_le_ncard_below p (hp ▸ hf)
  have h2 : (IsRayCategory.below (rm p)).ncard ≤ Nat.card (RayMor P) := Set.ncard_le_card _
  omega

/-- **Efficient tackles exist** in a finite chain-bounded ray category with an
essential contour. -/
theorem exists_efficient [Finite P] (hCB : ChainBounded P) {x y : RayVert P}
    (v w : Quiver.Path x y) (hvw : pathVal v = pathVal w) (h0 : pathVal v ≠ 0)
    (hi : ¬Interlaced v w) : ∃ l : List (RayMor P), IsEfficient InEss 0 l := by
  classical
  obtain ⟨N, hN⟩ := hCB
  set D := Nat.card (RayMor P)
  -- a tackle: the last arrow of `v`
  have hvl : 0 < v.length := by
    by_contra hl
    have hwl : w.length = 0 := by
      by_contra hw
      apply not_isIso_pathVal w (by omega)
      rw [← hvw]
      exact isIso_pathVal_of_length_zero v (by omega)
    have hxy := Quiver.Path.eq_of_length_zero v (by omega)
    subst hxy
    rw [Quiver.Path.eq_nil_of_length_zero v (by omega),
      Quiver.Path.eq_nil_of_length_zero w hwl] at hi
    exact hi (.refl _)
  obtain ⟨z, v₂, ζ, hv⟩ := exists_eq_cons v hvl
  let f : RayMor P := ⟨z.out, y.out, ζ.1⟩
  have ht : IsTackle InEss 0 [f] := ⟨by simp, ⟨fun g hg ↦ by rw [List.mem_singleton.1 hg]; exact ζ.2.1,
    fun j hj ↦ absurd hj (by simp)⟩, ζ.2, ⟨x, y, v, w, v₂, ζ, .nil, hvw, h0, hi, rfl, hv.trans rfl⟩⟩
  -- the efficiency words form a finite set
  let W : Set (List ℕ) := {e | ∃ l : List (RayMor P), IsTackle InEss 0 l ∧ efficiency l = e}
  have hWfin : W.Finite := by
    refine ((List.finite_length_le (Fin (D + 1)) N).image
      (List.map Fin.val)).subset ?_
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨(l.map fun f ↦ (⟨min (depth f.2.2) D, by omega⟩ : Fin (D + 1))), ?_, ?_⟩
    · simpa using hN l hl.choose_spec.1
    · rw [List.map_map, efficiency]
      refine List.map_congr_left fun g hg ↦ ?_
      simp only [Function.comp_apply]
      exact min_eq_left (depth_le_card (hl.choose_spec.1.1 g hg))
  have hWne : W.Nonempty := ⟨_, [f], ht, rfl⟩
  obtain ⟨M, ⟨l, hl, rfl⟩, hmax⟩ := Set.Finite.exists_maximal hWfin hWne
  refine ⟨l, hl, fun l' hl' hlex ↦ ?_⟩
  have := hmax ⟨l', hl', rfl⟩ (le_of_lt hlex)
  exact absurd (lt_of_lt_of_le hlex this) (lt_irrefl _)

/-- From an efficient tackle whose last link is a valley, the inputs of the
selection: `b`, `τ`, `β`, an essential value above `β`, and (K'). -/
theorem selection_inputs (hL : LeftCancel P) (hR : RightCancel P) {o : ℕ} {l : List (RayMor P)}
    (hl : IsEfficient InEss o l) (m : ℕ) (hm : m + 1 = l.length) (hev : (m + o) % 2 = 0) :
    ∃ (b : P) (τ β ν : BMor b), τ.2 ≠ 0 ∧ IsArr β ∧ ¬BLe β τ ∧ IsEssVal ν ∧ BLe β ν ∧
      KeyProp b τ := by
  have hlast := hl.1.getLast_eq m hm
  obtain ⟨hne, hch, hirr, hadm⟩ := hl.1
  rw [hlast] at hirr hadm
  let b := (l[m]'(by omega)).1
  let β : BMor b := ⟨(l[m]'(by omega)).2.1, (l[m]'(by omega)).2.2⟩
  -- `τ`: the previous entry, or the identity
  obtain ⟨τ, hτ, hτ0, hβτ⟩ : ∃ τ : BMor b, ((m = 0 ∧ τ = ⟨_, 𝟙 _⟩) ∨
      ∃ (h0 : 0 < m) (h : (l[m - 1]'(by omega)).1 = (l[m]'(by omega)).1),
        τ = ⟨(l[m - 1]'(by omega)).2.1, eqToHom h.symm ≫ (l[m - 1]'(by omega)).2.2⟩) ∧
      τ.2 ≠ 0 ∧ ¬BLe β τ := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · refine ⟨⟨_, 𝟙 _⟩, Or.inl ⟨h0, rfl⟩, IsRayCategory.id_ne_zero _, ?_⟩
      rintro ⟨c, hc⟩
      exact hirr.2.1 (isIso_of_isIso_comp _ c hirr.1 (by
        change IsIso ((l[m]'(by omega)).2.2 ≫ c)
        rw [hc]
        infer_instance))
    · have hv := hch.2 (m - 1) (by omega)
      simp only [Link, show (m - 1 + o) % 2 ≠ 0 by omega, ↓reduceIte] at hv
      have e1 : (l[m - 1 + 1]'(by omega)) = l[m]'(by omega) := by
        congr 1
        omega
      rw [e1] at hv
      obtain ⟨h, -, h2⟩ := hv
      refine ⟨_, Or.inr ⟨h0, h, rfl⟩, ?_, ?_⟩
      · intro hz
        apply hch.1 _ (List.getElem_mem (show m - 1 < l.length by omega))
        have := congrArg (fun t ↦ eqToHom h ≫ t) hz
        simpa using this
      · rintro ⟨c, hc⟩
        refine h2 ⟨c, ?_⟩
        change (l[m]'(by omega)).2.2 ≫ c = eqToHom h.symm ≫ _ at hc
        rw [hc]
        simp
  have hK : KeyProp b τ := keyProp_of_efficient hL hR hl m hm hev τ hτ
  -- an essential value above `β`
  obtain ⟨x, y, v, w, p, e, q, hvw, h0, hi, he, hv⟩ := hadm
  have hp := hK β hirr hβτ v w hvw h0 hi p e q he hv
  have hx := Quiver.Path.eq_of_length_zero p hp
  subst hx
  have hpn := Quiver.Path.eq_nil_of_length_zero p hp
  subst hpn
  refine ⟨b, τ, β, ⟨y.out, pathVal v⟩, hτ0, hirr, hβτ, ⟨v, w, rfl, hvw.symm, h0, hi⟩,
    ⟨pathVal q, ?_⟩, hK⟩
  change _ = pathVal v
  rw [hv, pathVal_comp]
  change _ = (𝟙 _ ≫ e.1) ≫ _
  rw [Category.id_comp, he]

/-- `P` has a long morphism: a nonzero non-invertible morphism that is not
irreducible. -/
def HasLong (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Prop :=
  ∃ (x y : P) (f : x ⟶ y), f ≠ 0 ∧ ¬IsIso f ∧ ¬IsIrreducible f

/-- Without long morphisms there are no essential contours. -/
theorem noEssContour_of_not_hasLong (h : ¬HasLong P) : NoEssContour (P := P) := by
  intro x y s t hst h0
  by_cases hiso : IsIso (pathVal s)
  · have hs : s.length = 0 := by
      by_contra hl
      exact not_isIso_pathVal s (by omega) hiso
    have ht : t.length = 0 := by
      by_contra hl
      exact not_isIso_pathVal t (by omega) (hst ▸ hiso)
    have hxy := Quiver.Path.eq_of_length_zero s hs
    subst hxy
    rw [Quiver.Path.eq_nil_of_length_zero s hs, Quiver.Path.eq_nil_of_length_zero t ht]
    exact .refl _
  · have hirr : IsIrreducible (pathVal s) := by
      by_contra hni
      exact h ⟨_, _, _, h0, hiso, hni⟩
    obtain ⟨e, rfl⟩ := eq_toPath_of_isIrreducible s hirr
    obtain ⟨e', rfl⟩ := eq_toPath_of_isIrreducible t (hst ▸ hirr)
    have : e = e' := Subtype.ext (by
      have := hst
      rwa [pathVal_toPath, pathVal_toPath] at this)
    subst this
    exact .refl _

section Main

omit [IsRayCategory P]

variable [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P]

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- **Fischbacher's Lemma 2.1** (start version): an efficient tackle whose last
link is a valley gives the data and hypotheses of Lemma 2.2. -/
theorem exists_redData_of_efficient (hL : LeftCancel P) (hR : RightCancel P)
    (hCB : ChainBounded P) {o : ℕ} {l : List (RayMor P)} (hl : IsEfficient InEss o l) (m : ℕ)
    (hm : m + 1 = l.length) (hev : (m + o) % 2 = 0) :
    ∃ (b : P) (ι : Type (max u v)) (d : ι → P) (α : ∀ i, b ⟶ d i) (hα : ∀ i, ¬IsIso (α i))
      (D : RedData α), D.EssHyp (hα := hα) ∧ D.EssHypVal ∧ Nonempty ι := by
  obtain ⟨b, τ, β, ν, hτ0, hβ, hβτ, hν, hβν, hK⟩ := selection_inputs hL hR hl m hm hev
  exact ⟨b, exists_redData hL hR hCB hτ0 hβ hβτ hν hβν hK⟩

end Main

end RayCat

end LargeIndecomposable
