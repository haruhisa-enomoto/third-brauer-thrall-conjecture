module

public import LargeIndecomposable.MildContours.Setup.EndCyclic
public import LargeIndecomposable.MultiplicativeBases.Twisted.BGRSDeep
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Tiny
public import LargeIndecomposable.Modules.Corners.Corner
public import LargeIndecomposable.MildContours.Setup.TinySmall

/-!
# From `TinyAt` in the ray category to the algebra (bridge)

For a split basic distributive algebra `B` with ray category
`P = BGRSRayCategory (projective category)`, a `TinyAt` point of `P` gives the
data of `not_minimal_of_tiny`, so a minimal representation-infinite `B` has no
such point. Morphisms `i ⟶ j` of the projective category are elements of
`e_j B e_i`, composed in reverse order.

This file: the basic dictionary — a morphism has a non-invertible ray iff it lies
in the radical of `B`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- The idempotent of an object of the projective category. -/
abbrev ev (i : S.toIdempotents.ProjectiveCategory) : B := S.e (S.toIdempotents.projectiveVertex i)

lemma ev_idem (i : S.toIdempotents.ProjectiveCategory) : ev S i * ev S i = ev S i :=
  (S.complete.toOrthogonalIdempotents.idem _).eq

lemma val_left {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) : ev S j * f.1 = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change ev S j * a * ev S i = f.1 at ha
  rw [← ha, ← mul_assoc, ← mul_assoc, ev_idem]

lemma val_right {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) : f.1 * ev S i = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change ev S j * a * ev S i = f.1 at ha
  rw [← ha, mul_assoc, ev_idem]

/-- The morphism `i ⟶ j` given by `e_j b e_i`. -/
def homOf (i j : S.toIdempotents.ProjectiveCategory) (b : B) : i ⟶ j := ⟨ev S j * b * ev S i, b, rfl⟩

lemma homOf_val (i j : S.toIdempotents.ProjectiveCategory) (b : B) :
    (homOf S i j b).1 = ev S j * b * ev S i := rfl

lemma comp_val {i j l : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) (g : j ⟶ l) :
    (f ≫ g).1 = g.1 * f.1 := rfl

lemma zero_val (i j : S.toIdempotents.ProjectiveCategory) : (0 : i ⟶ j).1 = 0 := rfl

lemma hom_ext' {i j : S.toIdempotents.ProjectiveCategory} {f g : i ⟶ j} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- An idempotent `e_x` is not in the radical. -/
lemma ev_not_mem_jacobson (i : S.toIdempotents.ProjectiveCategory) : ev S i ∉ Ring.jacobson B := by
  intro h
  obtain ⟨n, hn⟩ := Corner.isNilpotent_of_mem_jacobson k h
  have hp : ∀ m, ev S i ^ (m + 1) = ev S i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ev_idem]
  apply S.ne_zero (S.toIdempotents.projectiveVertex i)
  change ev S i = 0
  rcases n with _ | n
  · rw [pow_zero] at hn; rw [← mul_one (ev S i), hn, mul_zero]
  · rw [← hp n]; exact hn

/-- **A morphism in the radical has a non-invertible ray.** -/
lemma not_isIso_rayOf {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) (hf : f.1 ∈ Ring.jacobson B) :
    ¬IsIso (rayOf f) := by
  intro h
  haveI : IsIso (rayOf f) := h
  haveI : IsIso f :=
    BGRSRayCategory.representative_isIso_of_isIso
      (SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S.toIdempotents) f
  apply ev_not_mem_jacobson S i
  have : (f ≫ inv f).1 = ev S i := by rw [IsIso.hom_inv_id]; rfl
  rw [← this, comp_val]
  exact Ideal.mul_mem_left _ _ hf

/-- An isomorphism has an invertible ray. -/
lemma isIso_rayOf {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) [IsIso f] : IsIso (rayOf f) := by
  have hns : ¬IsBGRSSpecialZero f (inv f) := by
    rintro ⟨ρ, hρ⟩
    have e1 : ρ.1.asHom = 𝟙 j := by
      calc ρ.1.asHom = inv f ≫ (f ≫ ρ.1.asHom ≫ inv f) ≫ f := by simp
        _ = inv f ≫ (f ≫ inv f) ≫ f := by rw [hρ]; simp only [Category.assoc]
        _ = 𝟙 j := by simp
    haveI : Nontrivial (End j) :=
      ⟨⟨1, 0, SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S.toIdempotents j⟩⟩
    have h1 : (1 : End j) ∈ Ring.jacobson (End j) := by
      have : ρ.1 = 1 := e1
      rw [← this]; exact ρ.2
    exact (Ring.jacobson_lt_top (End j)).ne ((Ideal.eq_top_iff_one _).2 h1)
  have hns' : ¬IsBGRSSpecialZero (inv f) f := by
    rintro ⟨ρ, hρ⟩
    have e1 : ρ.1.asHom = 𝟙 i := by
      calc ρ.1.asHom = f ≫ (inv f ≫ ρ.1.asHom ≫ f) ≫ inv f := by simp
        _ = f ≫ (inv f ≫ f) ≫ inv f := by rw [hρ]; simp only [Category.assoc]
        _ = 𝟙 i := by simp
    haveI : Nontrivial (End i) :=
      ⟨⟨1, 0, SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S.toIdempotents i⟩⟩
    have h1 : (1 : End i) ∈ Ring.jacobson (End i) := by
      have : ρ.1 = 1 := e1
      rw [← this]; exact ρ.2
    exact (Ring.jacobson_lt_top (End i)).ne ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨⟨rayOf (inv f), ?_, ?_⟩⟩
  · rw [rayOf_comp, bgrsRayRepresentativeProduct_eq_comp_of_not_special hns, IsIso.hom_inv_id]
    rfl
  · rw [rayOf_comp, bgrsRayRepresentativeProduct_eq_comp_of_not_special hns', IsIso.inv_hom_id]
    rfl

/-- **A morphism with a non-invertible ray lies in the radical.** -/
lemma mem_jacobson_of_not_isIso_rayOf {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j)
    (hf : ¬IsIso (rayOf f)) : f.1 ∈ Ring.jacobson B := by
  by_cases hv : S.toIdempotents.projectiveVertex i = S.toIdempotents.projectiveVertex j
  · have hij : i = j := SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents hv
    subst hij
    have he : IsIdempotentElem (ev S i) := ev_idem S i
    obtain ⟨c, hc⟩ := S.corner_diag (S.toIdempotents.projectiveVertex i) f.1
    have hf1 : ev S i * f.1 * ev S i = f.1 := by rw [val_left, val_right]
    change ev S i * f.1 * ev S i - c • ev S i ∈ Ring.jacobson B at hc
    rw [hf1] at hc
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, sub_zero] at hc; exact hc
    exfalso
    apply hf
    have hmem : ∀ a : B, ev S i * a = a → a * ev S i = a → a ∈ Subsemigroup.corner (ev S i) :=
      fun a h1 h2 ↦ (Corner.mem_iff he).2 ⟨h1, h2⟩
    let x : he.Corner := Corner.mk he f.1 (hmem _ (val_left S f) (val_right S f))
    have hr1 : ev S i * (f.1 - c • ev S i) = f.1 - c • ev S i := by
      rw [mul_sub, val_left, mul_smul_comm, ev_idem]
    have hr2 : (f.1 - c • ev S i) * ev S i = f.1 - c • ev S i := by
      rw [sub_mul, val_right, smul_mul_assoc, ev_idem]
    let r : he.Corner := Corner.mk he _ (hmem _ hr1 hr2)
    have hx : x = algebraMap k he.Corner c + r := Corner.ext he (by
      change f.1 = (c • (1 : he.Corner)).1 + (f.1 - c • ev S i)
      rw [show (c • (1 : he.Corner)).1 = c • ev S i from rfl]; abel)
    have hrn : IsNilpotent r := by
      obtain ⟨n, hn⟩ := Corner.isNilpotent_of_mem_jacobson k hc
      refine ⟨n + 1, Corner.ext he ?_⟩
      rw [Corner.val_pow, Corner.val_zero]
      change (f.1 - c • ev S i) ^ (n + 1) = 0
      rw [pow_succ, hn, zero_mul]
    have hu : IsUnit x := by
      rw [hx]
      exact hrn.isUnit_add_left_of_commute ((isUnit_iff_ne_zero.2 hc0).map _)
        (Algebra.commutes c r).symm
    obtain ⟨y, hy⟩ := hu.exists_left_inv
    obtain ⟨y', hy'⟩ := hu.exists_right_inv
    have hyy : y = y' := by
      calc y = y * (x * y') := by rw [hy', mul_one]
        _ = y' := by rw [← mul_assoc, hy, one_mul]
    let g : i ⟶ i := ⟨Corner.val he y, Corner.val he y, by
      change ev S i * Corner.val he y * ev S i = _
      rw [Corner.mul_val, Corner.val_mul_e]⟩
    haveI : IsIso f := ⟨⟨g, hom_ext' S (by
      rw [comp_val]
      change Corner.val he y * Corner.val he x = ev S i
      rw [← Corner.val_mul, hy, Corner.val_one]), hom_ext' S (by
      rw [comp_val]
      change Corner.val he x * Corner.val he y = ev S i
      rw [← Corner.val_mul, hyy, hy', Corner.val_one])⟩⟩
    exact isIso_rayOf S f
  · have := S.corner_offdiag _ _ (Ne.symm hv) f.1
    change ev S j * f.1 * ev S i ∈ Ring.jacobson B at this
    rwa [val_left, val_right] at this

/-- The object of a vertex. -/
def objOf (v : ι) : S.toIdempotents.ProjectiveCategory := S.toIdempotents.projectiveVertexEquiv.symm v

lemma ev_objOf (v : ι) : ev S (objOf S v) = S.e v := by
  simp [ev, objOf, SplitBasicIdempotents.projectiveVertex]

lemma sum_e : ∑ v, S.e v = 1 := S.complete.complete

lemma decomp_left (b : B) : b = ∑ v, S.e v * b := by rw [← Finset.sum_mul, sum_e, one_mul]

lemma decomp_right (b : B) : b = ∑ v, b * S.e v := by rw [← Finset.mul_sum, sum_e, mul_one]

lemma hidC : ∀ X : S.toIdempotents.ProjectiveCategory, (𝟙 X : X ⟶ X) ≠ 0 :=
  SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S.toIdempotents

lemma hnilC : ∀ Y : S.toIdempotents.ProjectiveCategory, ∃ N : ℕ, ∀ l : List (End Y), l.length = N →
    (∀ a ∈ l, a ∈ Ring.jacobson (End Y)) → l.prod = 0 := by
  intro Y
  letI : Module.Finite k (End Y) := by change Module.Finite k (Y ⟶ Y); infer_instance
  haveI : IsArtinianRing (End Y) := IsArtinianRing.of_finite k (End Y)
  exact jacobson_listProd

/-- A right-deep ray: its representatives are killed by the radical of `B` on the
left. -/
lemma rad_mul_eq_zero {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) (hf : RightDeep (rayOf f))
    (x : B) (hx : x ∈ Ring.jacobson B) : x * f.1 = 0 := by
  rw [← val_left S f, ← mul_assoc, decomp_left S (x * ev S j), Finset.sum_mul]
  refine Finset.sum_eq_zero fun v _ ↦ ?_
  let g : j ⟶ objOf S v := homOf S j (objOf S v) x
  have hg : g.1 ∈ Ring.jacobson B := by
    rw [homOf_val]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
  have := rightDeep_kill (hidC S) (hnilC S) f hf g (not_isIso_rayOf S g hg)
  have h2 := congrArg Subtype.val this
  rw [comp_val, homOf_val, ev_objOf, zero_val] at h2
  rw [← h2]; simp only [mul_assoc]

/-- A left-deep ray: its representatives are killed by the radical of `B` on the
right. -/
lemma mul_rad_eq_zero {i j : S.toIdempotents.ProjectiveCategory} (f : i ⟶ j) (hf : LeftDeep (rayOf f))
    (x : B) (hx : x ∈ Ring.jacobson B) : f.1 * x = 0 := by
  rw [← val_right S f, mul_assoc, decomp_right S (ev S i * x), Finset.mul_sum]
  refine Finset.sum_eq_zero fun v _ ↦ ?_
  let g : objOf S v ⟶ i := homOf S (objOf S v) i x
  have hg : g.1 ∈ Ring.jacobson B := by
    rw [homOf_val]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
  have := leftDeep_kill (hidC S) (hnilC S) f hf g (not_isIso_rayOf S g hg)
  have h2 := congrArg Subtype.val this
  rw [comp_val, homOf_val, ev_objOf, zero_val] at h2
  rw [← h2]

/-- An element of the corner `e_j B e_j` is a scalar plus a radical element. -/
lemma corner_scalar {j : S.toIdempotents.ProjectiveCategory} (a : j ⟶ j) :
    ∃ c : k, a.1 - algebraMap k B c * ev S j ∈ Ring.jacobson B := by
  obtain ⟨c, hc⟩ := S.corner_diag (S.toIdempotents.projectiveVertex j) a.1
  refine ⟨c, ?_⟩
  change ev S j * a.1 * ev S j - c • ev S j ∈ Ring.jacobson B at hc
  rwa [val_left, val_right, Algebra.smul_def] at hc

/-- **Orbits of a two-sided socle element are its scalar multiples.** -/
lemma orbit_scalar {i j : S.toIdempotents.ProjectiveCategory} (f g : i ⟶ j)
    (hl : ∀ x ∈ Ring.jacobson B, ev S j * x = x → x * ev S j = x → x * f.1 = 0)
    (hr : ∀ x ∈ Ring.jacobson B, ev S i * x = x → x * ev S i = x → f.1 * x = 0)
    (h : UnitRayEquivalent f g) : ∃ c : k, g.1 = algebraMap k B c * f.1 := by
  obtain ⟨a, b, rfl⟩ := h
  obtain ⟨c₁, h₁⟩ := corner_scalar S b.hom
  obtain ⟨c₂, h₂⟩ := corner_scalar S a.hom
  refine ⟨c₁ * c₂, ?_⟩
  rw [comp_val, comp_val]
  have e1 : b.hom.1 * f.1 = algebraMap k B c₁ * f.1 := by
    have := hl _ h₁ (by rw [mul_sub, val_left, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      ev_idem]) (by rw [sub_mul, val_right, mul_assoc, ev_idem])
    rw [sub_mul, sub_eq_zero, mul_assoc, val_left] at this
    exact this
  have e2 : f.1 * a.hom.1 = algebraMap k B c₂ * f.1 := by
    have := hr _ h₂ (by rw [mul_sub, val_left, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      ev_idem]) (by rw [sub_mul, val_right, mul_assoc, ev_idem])
    rw [mul_sub, sub_eq_zero, ← mul_assoc, ← Algebra.commutes, mul_assoc, val_right] at this
    exact this
  rw [e1, mul_assoc, e2, ← mul_assoc, ← map_mul]

/-- A nonzero scalar multiple has the same ray. -/
lemma rayOf_smul {i j : S.toIdempotents.ProjectiveCategory} (f g : i ⟶ j) (c : k) (hc : c ≠ 0)
    (h : g.1 = algebraMap k B c * f.1) : rayOf g = rayOf f := by
  rw [rayOf, rayOf, unitRay_eq_iff]
  have hcj : ∀ d : k, (d • 𝟙 j : j ⟶ j).1 = algebraMap k B d * ev S j := fun d ↦ by
    rw [← Algebra.smul_def]; rfl
  let u : j ≅ j :=
    { hom := c⁻¹ • 𝟙 j
      inv := c • 𝟙 j
      hom_inv_id := by rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
      inv_hom_id := by rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
        mul_inv_cancel₀ hc, one_smul] }
  refine ⟨Iso.refl i, u, hom_ext' S ?_⟩
  rw [comp_val, comp_val]
  change f.1 = ((c⁻¹ • 𝟙 j : j ⟶ j).1 * g.1) * ev S i
  rw [hcj, mul_assoc _ g.1, val_right, h, mul_assoc, ← mul_assoc (ev S j), ← Algebra.commutes,
    mul_assoc, val_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]

lemma one_sub_e (u : ι) : 1 - S.e u = ∑ v ∈ Finset.univ.erase u, S.e v := by
  rw [← sum_e S, ← Finset.add_sum_erase _ _ (Finset.mem_univ u), add_sub_cancel_left]

lemma offdiag_right_mem (u : ι) (b : B) : S.e u * b * (1 - S.e u) ∈ Ring.jacobson B := by
  rw [one_sub_e, Finset.mul_sum]
  exact Ideal.sum_mem _ fun v hv ↦ S.corner_offdiag u v (Finset.ne_of_mem_erase hv).symm b

lemma offdiag_left_mem (u : ι) (b : B) : (1 - S.e u) * b * S.e u ∈ Ring.jacobson B := by
  rw [one_sub_e, Finset.sum_mul, Finset.sum_mul]
  exact Ideal.sum_mem _ fun v hv ↦ S.corner_offdiag v u (Finset.ne_of_mem_erase hv) b

lemma local_e (u : ι) (b : B) : ∃ l : k, S.e u * b - algebraMap k B l * S.e u ∈ Ring.jacobson B ∧
    b * S.e u - algebraMap k B l * S.e u ∈ Ring.jacobson B := by
  obtain ⟨l, hl⟩ := S.corner_diag u b
  rw [Algebra.smul_def] at hl
  refine ⟨l, ?_, ?_⟩
  · have : S.e u * b - algebraMap k B l * S.e u =
        (S.e u * b * S.e u - algebraMap k B l * S.e u) + S.e u * b * (1 - S.e u) := by
      rw [mul_sub, mul_one]; abel
    rw [this]; exact Ideal.add_mem _ hl (offdiag_right_mem S u b)
  · have : b * S.e u - algebraMap k B l * S.e u =
        (S.e u * b * S.e u - algebraMap k B l * S.e u) + (1 - S.e u) * b * S.e u := by
      rw [sub_mul, sub_mul, one_mul]; abel
    rw [this]; exact Ideal.add_mem _ hl (offdiag_left_mem S u b)

/-- **No tiny penny-farthing point** in the ray category of a minimal
representation-infinite algebra. -/
theorem not_tinyAt (hB : IsMinimalRepInfinite B) {X Z Bp : S.toIdempotents.RayCategory} (s : X ⟶ Z)
    (t : X ⟶ Bp) : ¬TinyAt s t := by
  rintro ⟨hs0, ht0, hzb, hib, hsR, hsL, htR, htirr, hRu, hLu, hfac⟩
  obtain ⟨i⟩ := X
  obtain ⟨z⟩ := Z
  obtain ⟨bb⟩ := Bp
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  set s' : i ⟶ z := Quotient.out s with hs'def
  set t' : i ⟶ bb := Quotient.out t with ht'def
  have hs' : rayOf s' = s := unitRay_out s
  have ht' : rayOf t' = t := unitRay_out t
  rw [← hs'] at hs0 hsR hsL hRu hLu
  rw [← ht'] at ht0 htR htirr hRu hfac
  have hzb' : z ≠ bb := fun h ↦ hzb (congrArg BGRSRayCategory.mk h)
  have hvzb : S.toIdempotents.projectiveVertex z ≠ S.toIdempotents.projectiveVertex bb :=
    fun h ↦ hzb' (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents h)
  have hs0' : s'.1 ≠ 0 := fun h ↦ hs0 (by rw [(rayOf_eq_zero_iff s').2 (hom_ext' S h)])
  have ht0' : t'.1 ≠ 0 := fun h ↦ ht0 (by rw [(rayOf_eq_zero_iff t').2 (hom_ext' S h)])
  have hsl := rad_mul_eq_zero S s' hsR
  have hsr := mul_rad_eq_zero S s' hsL
  have htl := rad_mul_eq_zero S t' htR
  refine not_minimal_of_tiny (k := k) hB (e := ev S i) (e' := ev S z) (s := s'.1) (t := t'.1)
    (eb := ev S bb) (R := (Ring.jacobson B : Set B)) (ev_idem S i) (ev_idem S z) hs0'
    (val_right S s') (val_left S s') (val_right S t') (val_left S t') jacobson_listProd htl
    ?_ ?_ ?_ ?_ ?_
  · -- `e' B t = 0`
    intro c hc
    have hm : ev S z * c * ev S bb ∈ Ring.jacobson B := S.corner_offdiag _ _ hvzb c
    have e1 : c * t'.1 = (ev S z * c * ev S bb) * t'.1 := by rw [hc, mul_assoc, val_left]
    rw [e1]; exact htl _ hm
  · -- the left socle of `B e` modulo `k t` is in `k s + k t`
    intro b hb hbJ
    have hvib : S.toIdempotents.projectiveVertex i ≠ S.toIdempotents.projectiveVertex bb := fun h ↦ hib
      (congrArg BGRSRayCategory.mk (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents h))
    have htJ : t'.1 ∈ Ring.jacobson B := by
      have := S.corner_offdiag _ _ (Ne.symm hvib) t'.1
      change ev S bb * t'.1 * ev S i ∈ Ring.jacobson B at this
      rwa [val_left, val_right] at this
    have htni : ¬IsIso (rayOf t') := not_isIso_rayOf S t' htJ
    -- `s` lies in the radical
    have hsJ : s'.1 ∈ Ring.jacobson B := by
      by_contra hn
      have hiso : IsIso (rayOf s') := by
        by_contra h; exact hn (mem_jacobson_of_not_isIso_rayOf S s' h)
      haveI := hiso
      haveI : IsIso s' := BGRSRayCategory.representative_isIso_of_isIso (hidC S) s'
      have h1 := rightDeep_kill (hidC S) (hnilC S) s' hsR (inv s' ≫ t')
        (not_isIso_rayOf S _ (by rw [comp_val]; exact Ideal.mul_mem_right _ _ htJ))
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] at h1
      exact ht0' (congrArg Subtype.val h1)
    -- `t` is killed on the right by radical endomorphisms of `x`
    have htr : ∀ x ∈ Ring.jacobson B, ev S i * x = x → x * ev S i = x → t'.1 * x = 0 := by
      intro x hx hx1 hx2
      have hker : ∀ ρ : End i, ρ ∈ Ring.jacobson (End i) → rayOf ρ.asHom ≫ rayOf t' = 0 := by
        intro ρ hρ
        by_contra hne
        have hνR : RightDeep (rayOf ρ.asHom ≫ rayOf t') := by
          intro w ζ hζ; rw [Category.assoc, htR ζ hζ, comp_zero]
        rcases hRu _ hne hνR with ⟨h, _⟩ | ⟨h, he⟩
        · exact hzb h.symm
        · rw [eqToHom_refl, Category.comp_id] at he
          rcases htirr _ _ he with h' | h'
          · exact not_isIso_rayOf_of_mem_jacobson (hidC S) ρ hρ h'
          · exact htni h'
      let ρ : End i := homOf S i i x
      have hρv : ρ.1 = x := by
        change ev S i * x * ev S i = x; rw [hx1, hx2]
      have hρJ : ρ ∈ Ring.jacobson (End i) :=
        S.mem_jacobson_of_not_isIso ρ (not_isIso_rayOf S (ρ : i ⟶ i) (by
          change (ρ : i ⟶ i).1 ∈ _; rw [hρv]; exact hx))
      have := leftDeep_kill_endo' (hidC S) (hnilC S) t' hker ρ hρJ
      have h2 := congrArg Subtype.val this
      rw [comp_val, zero_val] at h2
      change t'.1 * ρ.1 = 0 at h2
      rwa [hρv] at h2
    have hortho : ∀ {u v : ι}, u ≠ v → S.e u * S.e v = 0 :=
      fun h ↦ S.complete.toOrthogonalIdempotents.ortho h
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ c d : k,
        ev S y * b = algebraMap k B c * s'.1 + algebraMap k B d * t'.1 := by
      intro y
      let m : i ⟶ y := homOf S i y b
      have hmv : m.1 = ev S y * b := by rw [homOf_val, mul_assoc, hb]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, 0, by rw [← hmv, hm0]; simp⟩
      have hmr0 : rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      have hmR : RightDeep (rayOf m) := by
        intro W' ζ' hζ'
        obtain ⟨w⟩ := W'
        set ζ : y ⟶ w := Quotient.out ζ'
        have hζ : rayOf ζ = ζ' := unitRay_out ζ'
        rw [← hζ] at hζ' ⊢
        rw [rayOf_comp]
        by_cases hsp : IsBGRSSpecialZero m ζ
        · rw [bgrsRayRepresentativeProduct_eq_zero_of_special hsp]
          exact (rayOf_eq_zero_iff _).2 rfl
        rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp]
        have hζJ := mem_jacobson_of_not_isIso_rayOf S ζ hζ'
        obtain ⟨d, hd⟩ := hbJ ζ.1 hζJ
        have hmz : (m ≫ ζ).1 = algebraMap k B d * t'.1 := by
          rw [comp_val, hmv, ← mul_assoc, val_right, hd]
        by_cases hd0 : d = 0
        · exact (rayOf_eq_zero_iff _).2 (hom_ext' S (by rw [hmz, hd0, map_zero, zero_mul]; rfl))
        by_cases hwb : w = bb
        · subst hwb
          exfalso
          have hr : rayOf m ≫ rayOf ζ = rayOf t' := by
            rw [rayOf_comp, bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp]
            exact rayOf_smul S t' (m ≫ ζ) d hd0 hmz
          rcases htirr _ _ hr with h | h
          · have hyi : y = i := by
              by_contra hne
              have hv : S.toIdempotents.projectiveVertex y ≠ S.toIdempotents.projectiveVertex i := fun hv ↦
                hne (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents hv)
              apply not_isIso_rayOf S m _ h
              have := S.corner_offdiag _ _ hv m.1
              change ev S y * m.1 * ev S i ∈ _ at this
              rwa [val_left, val_right] at this
            subst hyi
            haveI := h
            haveI : IsIso m := BGRSRayCategory.representative_isIso_of_isIso (hidC S) m
            obtain ⟨d', hd'⟩ := hbJ s'.1 hsJ
            have h1 : (m ≫ s').1 = 0 := by
              rw [← val_left S (m ≫ s'), comp_val, hmv, ← mul_assoc s'.1, val_right, hd',
                ← mul_assoc, ← Algebra.commutes, mul_assoc, ← val_left S t', ← mul_assoc (ev S z),
                hortho hvzb, zero_mul, mul_zero]
            have h2 : m ≫ s' = 0 := hom_ext' S h1
            apply hs0'
            have : s' = inv m ≫ m ≫ s' := by simp
            rw [this, h2, comp_zero]; rfl
          · exact hζ' h
        · have hv : S.toIdempotents.projectiveVertex w ≠ S.toIdempotents.projectiveVertex bb := fun hv ↦
            hwb (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents hv)
          have h0 : (m ≫ ζ).1 = 0 := by
            rw [← val_left S (m ≫ ζ), hmz, ← mul_assoc, ← Algebra.commutes, mul_assoc,
              ← val_left S t', ← mul_assoc (ev S w), hortho hv, zero_mul, mul_zero]
          exact (rayOf_eq_zero_iff _).2 (hom_ext' S (by rw [h0]; rfl))
      rcases hRu (rayOf m) hmr0 hmR with ⟨h, he⟩ | ⟨h, he⟩
      · have hyz : y = z := congrArg BGRSRayCategory.as h
        subst hyz
        rw [eqToHom_refl, Category.comp_id] at he
        obtain ⟨c, hc⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
          ((unitRay_eq_iff _ _).1 he.symm)
        exact ⟨c, 0, by rw [← hmv, hc]; simp⟩
      · have hyb : y = bb := congrArg BGRSRayCategory.as h
        subst hyb
        rw [eqToHom_refl, Category.comp_id] at he
        obtain ⟨d, hd⟩ := orbit_scalar S t' m (fun x hx _ _ ↦ htl x hx) htr ((unitRay_eq_iff _ _).1 he.symm)
        exact ⟨0, d, by rw [← hmv, hd]; simp⟩
    choose c d hcd using key
    refine ⟨∑ v, c (objOf S v), ∑ v, d (objOf S v), ?_⟩
    rw [decomp_left S b, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← hcd, ev_objOf]
  · -- the right socle of `e' B` is `k s`
    intro c hc hcJ
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ a : k, c * ev S y = algebraMap k B a * s'.1 := by
      intro y
      let m : y ⟶ z := homOf S y z c
      have hmv : m.1 = c * ev S y := by rw [homOf_val, hc]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, by rw [← hmv, hm0, map_zero, zero_mul]⟩
      have hmL : LeftDeep (rayOf m) := leftDeep_of_kill m (fun ζ hζ ↦ hom_ext' S (by
        rw [comp_val, hmv, zero_val, mul_assoc, val_left]
        exact hcJ _ (mem_jacobson_of_not_isIso_rayOf S ζ hζ)))
      have hmr0 : rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      obtain ⟨h, he⟩ := hLu (rayOf m) hmr0 hmL
      have hyi : y = i := congrArg BGRSRayCategory.as h
      subst hyi
      rw [eqToHom_refl, Category.id_comp] at he
      obtain ⟨a, ha⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
        ((unitRay_eq_iff _ _).1 he.symm)
      exact ⟨a, by rw [← hmv, ha]⟩
    choose a ha using key
    refine ⟨∑ v, a (objOf S v), ?_⟩
    rw [decomp_right S c, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← ha, ev_objOf]
  · -- `e_b R ⊆ t B`
    intro j hj
    have key : ∀ v : ι, ∃ b' : B, ev S bb * j * S.e v = t'.1 * b' := by
      intro v
      let n : objOf S v ⟶ bb := homOf S (objOf S v) bb j
      have hnv : n.1 = ev S bb * j * S.e v := by rw [homOf_val, ev_objOf]
      by_cases hn0 : n.1 = 0
      · exact ⟨0, by rw [← hnv, hn0, mul_zero]⟩
      have hnJ : n.1 ∈ Ring.jacobson B := by
        rw [homOf_val]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hj)
      obtain ⟨ν', hν'⟩ := hfac (rayOf n) (not_isIso_rayOf S n hnJ)
      set ν : objOf S v ⟶ i := Quotient.out ν'
      have hν : rayOf ν = ν' := unitRay_out ν'
      rw [← hν, rayOf_comp] at hν'
      by_cases hsp : IsBGRSSpecialZero ν t'
      · rw [bgrsRayRepresentativeProduct_eq_zero_of_special hsp] at hν'
        exact absurd (congrArg Subtype.val ((rayOf_eq_zero_iff n).1 hν')) hn0
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp] at hν'
      obtain ⟨a, b, hab⟩ := (unitRay_eq_iff _ _).1 hν'
      have hn : n = a.inv ≫ (ν ≫ t') ≫ b.inv := by rw [hab]; simp
      obtain ⟨c, hc⟩ := corner_scalar S b.inv
      have e1 : b.inv.1 * t'.1 = algebraMap k B c * t'.1 := by
        have := htl _ hc
        rw [sub_mul, sub_eq_zero, mul_assoc, val_left] at this
        exact this
      refine ⟨algebraMap k B c * ν.1 * a.inv.1, ?_⟩
      rw [← hnv, hn, comp_val, comp_val, comp_val, ← mul_assoc, ← mul_assoc, e1]
      rw [Algebra.commutes c t'.1]
      simp only [mul_assoc]
    choose b' hb' using key
    refine ⟨∑ v, b' v, ?_⟩
    rw [decomp_right S (ev S bb * j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ ↦ hb' v
  · exact fun b ↦ local_e S _ b

/-- **No projective-injective point** in the ray category of a minimal
representation-infinite algebra (the tiny lemma with `t = 0`). -/
theorem not_projInjAt (hB : IsMinimalRepInfinite B) {X Z : S.toIdempotents.RayCategory} (s : X ⟶ Z) :
    ¬ProjInjAt s := by
  rintro ⟨hs0, hsR, hsL, hRu, hLu⟩
  obtain ⟨i⟩ := X
  obtain ⟨z⟩ := Z
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  set s' : i ⟶ z := Quotient.out s with hs'def
  have hs' : rayOf s' = s := unitRay_out s
  rw [← hs'] at hs0 hsR hsL hRu hLu
  have hs0' : s'.1 ≠ 0 := fun h ↦ hs0 (by rw [(rayOf_eq_zero_iff s').2 (hom_ext' S h)])
  have hsl := rad_mul_eq_zero S s' hsR
  have hsr := mul_rad_eq_zero S s' hsL
  refine not_minimal_of_tiny (k := k) hB (e := ev S i) (e' := ev S z) (s := s'.1) (t := 0)
    (eb := 0) (R := (Ring.jacobson B : Set B)) (ev_idem S i) (ev_idem S z) hs0'
    (val_right S s') (val_left S s') (zero_mul _) (mul_zero _) jacobson_listProd
    (fun _ _ ↦ mul_zero _) (fun _ _ ↦ mul_zero _) ?_ ?_ (fun _ _ ↦ ⟨0, by simp⟩)
    (fun _ ↦ ⟨0, by simp [Ideal.zero_mem]⟩)
  · intro b hb hbJ
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ c : k,
        ev S y * b = algebraMap k B c * s'.1 := by
      intro y
      let m : i ⟶ y := homOf S i y b
      have hmv : m.1 = ev S y * b := by rw [homOf_val, mul_assoc, hb]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, by rw [← hmv, hm0]; simp⟩
      have hmr0 : rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      have hmR : RightDeep (rayOf m) := rightDeep_of_kill m (fun ζ hζ ↦ hom_ext' S (by
        obtain ⟨d, hd⟩ := hbJ ζ.1 (mem_jacobson_of_not_isIso_rayOf S ζ hζ)
        rw [comp_val, hmv, ← mul_assoc, val_right, hd, mul_zero, zero_val]))
      obtain ⟨h, he⟩ := hRu (rayOf m) hmr0 hmR
      have hyz : y = z := congrArg BGRSRayCategory.as h
      subst hyz
      rw [eqToHom_refl, Category.comp_id] at he
      obtain ⟨c, hc⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
        ((unitRay_eq_iff _ _).1 he.symm)
      exact ⟨c, by rw [← hmv, hc]⟩
    choose c hc using key
    refine ⟨∑ v, c (objOf S v), 0, ?_⟩
    rw [decomp_left S b, map_sum, Finset.sum_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← hc, ev_objOf]
  · intro c hc hcJ
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ a : k, c * ev S y = algebraMap k B a * s'.1 := by
      intro y
      let m : y ⟶ z := homOf S y z c
      have hmv : m.1 = c * ev S y := by rw [homOf_val, hc]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, by rw [← hmv, hm0, map_zero, zero_mul]⟩
      have hmL : LeftDeep (rayOf m) := leftDeep_of_kill m (fun ζ hζ ↦ hom_ext' S (by
        rw [comp_val, hmv, zero_val, mul_assoc, val_left]
        exact hcJ _ (mem_jacobson_of_not_isIso_rayOf S ζ hζ)))
      have hmr0 : rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      obtain ⟨h, he⟩ := hLu (rayOf m) hmr0 hmL
      have hyi : y = i := congrArg BGRSRayCategory.as h
      subst hyi
      rw [eqToHom_refl, Category.id_comp] at he
      obtain ⟨a, ha⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
        ((unitRay_eq_iff _ _).1 he.symm)
      exact ⟨a, by rw [← hmv, ha]⟩
    choose a ha using key
    refine ⟨∑ v, a (objOf S v), ?_⟩
    rw [decomp_right S c, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← ha, ev_objOf]

/-- **`NoTiny` for the small ray category** of a minimal representation-infinite
algebra. -/
theorem noTiny_small (hB : IsMinimalRepInfinite B) [LocallySmall.{0} S.toIdempotents.RayCategory] :
    NoTiny (RaySmall.{0} S.toIdempotents.RayCategory) := fun s t h ↦
  S.not_tinyAt hB _ _ (RaySmall.tinyAt_of_small h)

/-- **`NoProjInj` for the small ray category** of a minimal representation-infinite
algebra. -/
theorem noProjInj_small (hB : IsMinimalRepInfinite B) [LocallySmall.{0} S.toIdempotents.RayCategory] :
    NoProjInj (RaySmall.{0} S.toIdempotents.RayCategory) := fun s h ↦
  S.not_projInjAt hB _ (RaySmall.projInjAt_of_small h)

end SplitBasicData

end LargeIndecomposable
