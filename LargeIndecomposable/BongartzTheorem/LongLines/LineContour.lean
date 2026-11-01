module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineIndec
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Connected
public import LargeIndecomposable.RayCategories.Linearization.RegularRepresentation

/-!
# Lines of every length exclude contours

If the cover contains lines of every length, a contour of `P` (two different paths with the same
nonzero value `w`) is impossible when `B ≅ k(P)` is minimal representation-infinite: the modules of
the lines are indecomposable, pairwise of different dimensions, and killed by `w`
(`CLine.pdAct_contour_eq_zero`), so `B / (w)` would be representation-infinite
(BO13b, Lemma 7.2 (c), proof; `noContour_of_lines`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver Statement

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

section NonZero

variable (k : Type u) [Field k]

lemma morAct_ne_zero {s t : P} {g : s ⟶ t} (hg : g ≠ 0) : morAct k g ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (Finsupp.single ⟨s, s, 𝟙 s, IsRayCategory.id_ne_zero s⟩ 1)
  rw [morAct_single, actRay_mk_eq, LinearMap.zero_apply] at h1
  unfold compRay at h1
  rw [dif_neg (by rwa [Category.id_comp])] at h1
  exact one_ne_zero (Finsupp.single_eq_zero.1 h1)

/-- **A path with nonzero value is nonzero in the linearization.** -/
lemma linPres_word_ne_zero {l : List (quiver P).A} (hl : l ≠ []) {x y : P}
    {h : PathFrom (D := quiver P) x l y} (hν : pathMor l x y h ≠ 0) :
    linPres P k (word k (quiver P) l) ≠ 0 := by
  intro h0
  rcases l with _ | ⟨c, l⟩
  · exact hl rfl
  have := congrArg (linRep P k) h0
  rw [linRep_linPres, regRep_word (k := k) c l x y h, map_zero] at this
  exact morAct_ne_zero k hν this

end NonZero

section Transfer

variable {A B M : Type u} [Ring A] [Ring B] [AddCommGroup M] [Module A M]

lemma isIndecomposable_compHom (φ : B ≃+* A) (h : IsIndecomposable A M) :
    letI := Module.compHom M φ.toRingHom
    IsIndecomposable B M := by
  letI := Module.compHom M φ.toRingHom
  have toA : ∀ N : Submodule B M, ∃ NA : Submodule A M, (NA : Set M) = N := fun N ↦
    ⟨{ N.toAddSubmonoid with
      smul_mem' := fun a m hm ↦ by
        have : a • m = φ.symm a • m := by
          change a • m = φ (φ.symm a) • m
          rw [RingEquiv.apply_symm_apply]
        rw [this]; exact N.smul_mem _ hm }, rfl⟩
  refine ⟨h.1, fun N N' hc ↦ ?_⟩
  obtain ⟨NA, hNA⟩ := toA N
  obtain ⟨NA', hNA'⟩ := toA N'
  have hmem : ∀ x, x ∈ NA ↔ x ∈ N := fun x ↦ by rw [← SetLike.mem_coe, hNA]; rfl
  have hmem' : ∀ x, x ∈ NA' ↔ x ∈ N' := fun x ↦ by rw [← SetLike.mem_coe, hNA']; rfl
  have hcA : IsCompl NA NA' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      exact (Submodule.disjoint_def.1 hc.1) x ((hmem x).1 hx) ((hmem' x).1 hx')
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro x
      obtain ⟨y, z, hy, hz, hyz⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.2 x
      exact ⟨y, z, (hmem y).2 hy, (hmem' z).2 hz, hyz⟩
  rcases h.2 NA NA' hcA with h1 | h1
  · left
    rw [Submodule.eq_bot_iff] at h1 ⊢
    exact fun x hx ↦ h1 x ((hmem x).2 hx)
  · right
    rw [Submodule.eq_bot_iff] at h1 ⊢
    exact fun x hx ↦ h1 x ((hmem' x).2 hx)

end Transfer

namespace CLine

variable (L : CLine x₀) (k : Type u) [Field k]

lemma card_finset : L.finset.card = L.n + 1 := by
  classical
  unfold finset
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact L.inj a b (by omega) (by omega) hab

lemma finrank_lineMod : Module.finrank k (L.lineMod k) = L.n + 1 := by
  rw [← L.card_finset]
  change Module.finrank k ((pieceQuiver L.finset).V → k) = _
  rw [Module.finrank_fintype_fun_eq_card]
  convert Fintype.card_coe L.finset
  rfl

variable {B : Type u} [Ring B] [Algebra k B] (e : Linearization P k ≃ₐ[k] B)

/-- The module of a line as a `B`-module. -/
def lineModB : AR.FDMod k B where
  carrier := L.lineMod k
  isModule := Module.compHom _ e.symm.toRingHom
  isModuleK := inferInstance
  isScalarTower := by
    letI : Module B (L.lineMod k) := Module.compHom _ e.symm.toRingHom
    exact ⟨fun c b m ↦ by
      change e.symm (c • b) • m = c • (e.symm b • m)
      rw [map_smul, smul_assoc]⟩
  isFD := inferInstance

lemma smul_lineModB (b : B) (m : L.lineModB k e) :
    b • m = (show L.lineMod k from (e.symm b • (show L.lineMod k from m))) := rfl

end CLine

/-- **Lines of every length exclude contours** (BO13b, Lemma 7.2 (c)). -/
theorem noContour_of_lines {k B : Type u} [Field k] [Ring B] [Algebra k B]
    (hB : IsMinimalRepInfinite B) (e : Linearization P k ≃ₐ[k] B)
    (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (hlines : ∀ m, ∃ L : CLine x₀, m ≤ L.n) : NoContour P := by
  intro l l' x y h h' he hν
  by_contra hll'
  -- a nonempty contour path, acting by zero on all line modules
  obtain ⟨l₀, h₀, hl₀, hν₀, hz⟩ : ∃ (l₀ : List (quiver P).A) (h₀ : PathFrom (D := quiver P) x l₀ y),
      l₀ ≠ [] ∧ pathMor l₀ x y h₀ ≠ 0 ∧ ∀ L : CLine x₀,
        (L.lineRep k).pdAct (pieceProj L.finset) (word k (quiver P) l₀) = 0 := by
    by_cases hl : l = []
    · have hl' : l' ≠ [] := by rintro rfl; exact hll' (hl.trans rfl)
      exact ⟨l', h', hl', he ▸ hν, fun L ↦ L.pdAct_contour_eq_zero k he.symm (he ▸ hν)
        (Ne.symm hll')⟩
    · exact ⟨l, h, hl, hν, fun L ↦ L.pdAct_contour_eq_zero k he hν hll'⟩
  set w := linPres P k (word k (quiver P) l₀)
  have hw : w ≠ 0 := linPres_word_ne_zero k hl₀ hν₀
  set b := e w
  have hb : b ≠ 0 := fun h0 ↦ hw (e.injective (h0.trans (map_zero e).symm))
  set I : TwoSidedIdeal B := TwoSidedIdeal.span {b}
  have hI : I ≠ ⊥ := by
    intro h0
    have : b ∈ I := TwoSidedIdeal.subset_span rfl
    rw [h0] at this
    exact hb this
  obtain ⟨n, X, hX⟩ := hB.2 I hI
  -- every line module is one of the listed modules
  have hidx : ∀ L : CLine x₀, ∃ i, Nonempty (L.lineModB k e ≃ₗ[B]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj (X i)) := by
    intro L
    have hind : IsIndecomposable B (L.lineModB k e) :=
      isIndecomposable_compHom e.symm.toRingEquiv (L.isIndecomposable_lineMod k htf)
    haveI : Module.Finite B (L.lineModB k e) :=
      Module.Finite.of_restrictScalars_finite k B (L.lineModB k e)
    refine exists_iso_of_isTorsion I X hX (L.lineModB k e) hind ?_
    let Ann : TwoSidedIdeal B := TwoSidedIdeal.mk' {z | ∀ m : L.lineModB k e, z • m = 0}
      (fun m ↦ zero_smul _ m) (fun ha hb' m ↦ by rw [add_smul, ha, hb', add_zero])
      (fun ha m ↦ by rw [neg_smul, ha, neg_zero]) (fun {z w} hw m ↦ by rw [mul_smul, hw, smul_zero])
      (fun {z w} hz m ↦ by rw [mul_smul, hz])
    have hbA : b ∈ Ann := by
      refine (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ b).2 fun m ↦ ?_
      rw [L.smul_lineModB k e, AlgEquiv.symm_apply_apply]
      change linAct L.convex_finset (L.respectsCover_lineRep k) w m = 0
      rw [linAct_linPres, hz L]
      rfl
    have hle : I ≤ Ann := TwoSidedIdeal.span_le.2 (Set.singleton_subset_iff.2 hbA)
    intro z hzI m
    exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ z).1 (hle hzI) m
  choose Lm hLm using hlines
  choose idx hidx' using fun m ↦ hidx (Lm m)
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber idx
  have hinf : (idx ⁻¹' {i}).Infinite := Set.infinite_coe_iff.1 hi
  obtain ⟨m₁, hm₁⟩ := hinf.nonempty
  obtain ⟨m₂, hm₂, hlt⟩ := hinf.exists_gt ((Lm m₁).n + 1)
  obtain ⟨f₁⟩ := hidx' m₁
  obtain ⟨f₂⟩ := hidx' m₂
  have e₁₂ : (Lm m₁).lineModB k e ≃ₗ[B] (Lm m₂).lineModB k e := by
    have h1 : idx m₁ = i := hm₁
    have h2 : idx m₂ = i := hm₂
    rw [h1] at f₁
    rw [h2] at f₂
    exact f₁.trans f₂.symm
  have hfr := (e₁₂.restrictScalars k).finrank_eq
  change Module.finrank k ((Lm m₁).lineMod k) = Module.finrank k ((Lm m₂).lineMod k) at hfr
  rw [CLine.finrank_lineMod, CLine.finrank_lineMod] at hfr
  have := hLm m₂
  omega

end LargeIndecomposable.RayCat
