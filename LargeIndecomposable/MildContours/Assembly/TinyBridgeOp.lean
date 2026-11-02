module

public import LargeIndecomposable.MildContours.Assembly.TinyBridge
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisFromDeep

/-!
# The dual bridge: no dual tiny point

A dual tiny point of the ray category of `B` (a tiny point of its opposite) gives
the data of `not_minimal_of_tiny` for the opposite algebra `Bᵐᵒᵖ`, which is also
minimal representation-infinite (`isMinimalRepInfinite_mop`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat MulOpposite

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- **No dual tiny point** in the ray category of a minimal representation-infinite
algebra. -/
theorem not_tinyAtDual (hB : IsMinimalRepInfinite B) {X Z Bp : S.toIdempotents.RayCategory} (s : Z ⟶ X)
    (t : Bp ⟶ X) : ¬TinyAtDual s t := by
  rintro ⟨hs0, ht0, hzb, hxb, hsL, hsR, htL, hirr, hLu, hRu, hfac⟩
  obtain ⟨i⟩ := X
  obtain ⟨z⟩ := Z
  obtain ⟨bb⟩ := Bp
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  set s' : z ⟶ i := Quotient.out s with hs'def
  set t' : bb ⟶ i := Quotient.out t with ht'def
  have hs' : LargeIndecomposable.rayOf s' = s := unitRay_out s
  have ht' : LargeIndecomposable.rayOf t' = t := unitRay_out t
  rw [← hs'] at hs0 hsL hsR hLu hRu
  rw [← ht'] at ht0 htL hirr hLu hfac
  have hzb' : z ≠ bb := fun h ↦ hzb (congrArg BGRSRayCategory.mk h)
  have hvzb : S.toIdempotents.projectiveVertex z ≠ S.toIdempotents.projectiveVertex bb :=
    fun h ↦ hzb' (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents h)
  have hvib : S.toIdempotents.projectiveVertex i ≠ S.toIdempotents.projectiveVertex bb := fun h ↦ hxb
    (congrArg BGRSRayCategory.mk (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents h))
  have hs0' : s'.1 ≠ 0 := fun h ↦ hs0 (by rw [(rayOf_eq_zero_iff s').2 (hom_ext' S h)])
  have ht0' : t'.1 ≠ 0 := fun h ↦ ht0 (by rw [(rayOf_eq_zero_iff t').2 (hom_ext' S h)])
  have hsl := rad_mul_eq_zero S s' hsR
  have hsr := mul_rad_eq_zero S s' hsL
  have htr := mul_rad_eq_zero S t' htL
  have htJ : t'.1 ∈ Ring.jacobson B := by
    have := S.corner_offdiag _ _ hvib t'.1
    change ev S i * t'.1 * ev S bb ∈ Ring.jacobson B at this
    rwa [val_left, val_right] at this
  have htni : ¬IsIso (LargeIndecomposable.rayOf t') := not_isIso_rayOf S t' htJ
  have hortho : ∀ {u v : ι}, u ≠ v → S.e u * S.e v = 0 :=
    fun h ↦ S.complete.toOrthogonalIdempotents.ortho h
  -- `s` lies in the radical
  have hsJ : s'.1 ∈ Ring.jacobson B := by
    by_contra hn
    have hiso : IsIso (LargeIndecomposable.rayOf s') := by
      by_contra h; exact hn (mem_jacobson_of_not_isIso_rayOf S s' h)
    haveI := hiso
    haveI : IsIso s' := BGRSRayCategory.representative_isIso_of_isIso (hidC S) s'
    have h1 := leftDeep_kill (hidC S) (hnilC S) s' hsL (t' ≫ inv s')
      (not_isIso_rayOf S _ (by rw [comp_val]; exact Ideal.mul_mem_left _ _ htJ))
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h1
    exact ht0' (congrArg Subtype.val h1)
  -- `t` is killed on the left by radical endomorphisms of `x`
  have htl : ∀ x ∈ Ring.jacobson B, ev S i * x = x → x * ev S i = x → x * t'.1 = 0 := by
    intro x hx hx1 hx2
    have hker : ∀ ρ : End i, ρ ∈ Ring.jacobson (End i) → LargeIndecomposable.rayOf t' ≫ LargeIndecomposable.rayOf ρ.asHom = 0 := by
      intro ρ hρ
      by_contra hne
      have hνL : LeftDeep (LargeIndecomposable.rayOf t' ≫ LargeIndecomposable.rayOf ρ.asHom) := by
        intro w ζ hζ; rw [← Category.assoc, htL ζ hζ, zero_comp]
      rcases hLu _ hne hνL with ⟨h, _⟩ | ⟨h, he⟩
      · exact hzb h.symm
      · rw [eqToHom_refl, Category.id_comp] at he
        rcases hirr _ _ he with h' | h'
        · exact htni h'
        · exact not_isIso_rayOf_of_mem_jacobson (hidC S) ρ hρ h'
    let ρ : End i := homOf S i i x
    have hρv : ρ.1 = x := by
      change ev S i * x * ev S i = x; rw [hx1, hx2]
    have hρJ : ρ ∈ Ring.jacobson (End i) :=
      S.mem_jacobson_of_not_isIso ρ (not_isIso_rayOf S (ρ : i ⟶ i) (by
        change (ρ : i ⟶ i).1 ∈ _; rw [hρv]; exact hx))
    have := rightDeep_kill_endo' (hidC S) (hnilC S) t' hker ρ hρJ
    have h2 := congrArg Subtype.val this
    rw [comp_val, zero_val] at h2
    change ρ.1 * t'.1 = 0 at h2
    rwa [hρv] at h2
  -- the B-level conditions
  have hsocR_B : ∀ c : B, c * ev S z = c → (∀ j ∈ Ring.jacobson B, j * c = 0) →
      ∃ a : k, c = algebraMap k B a * s'.1 := by
    intro c hc hcJ
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ a : k, ev S y * c = algebraMap k B a * s'.1 := by
      intro y
      let m : z ⟶ y := homOf S z y c
      have hmv : m.1 = ev S y * c := by rw [homOf_val, mul_assoc, hc]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, by rw [← hmv, hm0, map_zero, zero_mul]⟩
      have hmR : RightDeep (LargeIndecomposable.rayOf m) := rightDeep_of_kill m (fun ζ hζ ↦ hom_ext' S (by
        rw [comp_val, hmv, zero_val, ← mul_assoc, val_right]
        exact hcJ _ (mem_jacobson_of_not_isIso_rayOf S ζ hζ)))
      have hmr0 : LargeIndecomposable.rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      obtain ⟨h, he⟩ := hRu (LargeIndecomposable.rayOf m) hmr0 hmR
      have hyi : y = i := congrArg BGRSRayCategory.as h
      subst hyi
      rw [eqToHom_refl, Category.comp_id] at he
      obtain ⟨a, ha⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
        ((unitRay_eq_iff _ _).1 he.symm)
      exact ⟨a, by rw [← hmv, ha]⟩
    choose a ha using key
    refine ⟨∑ v, a (objOf S v), ?_⟩
    rw [decomp_left S c, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← ha, ev_objOf]
  have hsocL_B : ∀ b : B, ev S i * b = b →
      (∀ j ∈ Ring.jacobson B, ∃ d : k, b * j = algebraMap k B d * t'.1) →
      ∃ c d : k, b = algebraMap k B c * s'.1 + algebraMap k B d * t'.1 := by
    intro b hb hbJ
    have key : ∀ y : S.toIdempotents.ProjectiveCategory, ∃ c d : k,
        b * ev S y = algebraMap k B c * s'.1 + algebraMap k B d * t'.1 := by
      intro y
      let m : y ⟶ i := homOf S y i b
      have hmv : m.1 = b * ev S y := by rw [homOf_val, hb]
      by_cases hm0 : m.1 = 0
      · exact ⟨0, 0, by rw [← hmv, hm0]; simp⟩
      have hmr0 : LargeIndecomposable.rayOf m ≠ 0 := fun h ↦ hm0 (congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h))
      have hmL : LeftDeep (LargeIndecomposable.rayOf m) := by
        intro W' ζ' hζ'
        obtain ⟨w⟩ := W'
        set ζ : w ⟶ y := Quotient.out ζ'
        have hζ : LargeIndecomposable.rayOf ζ = ζ' := unitRay_out ζ'
        rw [← hζ] at hζ' ⊢
        rw [rayOf_comp]
        by_cases hsp : IsBGRSSpecialZero ζ m
        · rw [bgrsRayRepresentativeProduct_eq_zero_of_special hsp]
          exact (rayOf_eq_zero_iff _).2 rfl
        rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp]
        have hζJ := mem_jacobson_of_not_isIso_rayOf S ζ hζ'
        obtain ⟨d, hd⟩ := hbJ ζ.1 hζJ
        have hmz : (ζ ≫ m).1 = algebraMap k B d * t'.1 := by
          rw [comp_val, hmv, mul_assoc, val_left, hd]
        by_cases hd0 : d = 0
        · exact (rayOf_eq_zero_iff _).2 (hom_ext' S (by rw [hmz, hd0, map_zero, zero_mul]; rfl))
        by_cases hwb : w = bb
        · subst hwb
          exfalso
          have hr : LargeIndecomposable.rayOf ζ ≫ LargeIndecomposable.rayOf m = LargeIndecomposable.rayOf t' := by
            rw [rayOf_comp, bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp]
            exact rayOf_smul S t' (ζ ≫ m) d hd0 hmz
          rcases hirr _ _ hr with h | h
          · exact hζ' h
          · have hyi : y = i := by
              by_contra hne
              have hv : S.toIdempotents.projectiveVertex y ≠ S.toIdempotents.projectiveVertex i := fun hv ↦
                hne (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents hv)
              apply not_isIso_rayOf S m _ h
              have := S.corner_offdiag _ _ (Ne.symm hv) m.1
              change ev S i * m.1 * ev S y ∈ _ at this
              rwa [val_left, val_right] at this
            subst hyi
            haveI := h
            haveI : IsIso m := BGRSRayCategory.representative_isIso_of_isIso (hidC S) m
            obtain ⟨d', hd'⟩ := hbJ s'.1 hsJ
            have h1 : (s' ≫ m).1 = 0 := by
              rw [← val_right S (s' ≫ m), comp_val, hmv, mul_assoc b, val_left, hd',
                mul_assoc, ← val_right S t', mul_assoc t'.1, hortho (Ne.symm hvzb), mul_zero,
                mul_zero]
            have h2 : s' ≫ m = 0 := hom_ext' S h1
            apply hs0'
            have : s' = s' ≫ m ≫ inv m := by simp
            rw [this, ← Category.assoc, h2, zero_comp]; rfl
        · have hv : S.toIdempotents.projectiveVertex w ≠ S.toIdempotents.projectiveVertex bb := fun hv ↦
            hwb (SplitBasicIdempotents.projectiveVertex_injective S.toIdempotents hv)
          have h0 : (ζ ≫ m).1 = 0 := by
            rw [← val_right S (ζ ≫ m), hmz, mul_assoc, ← val_right S t', mul_assoc t'.1,
              hortho (Ne.symm hv), mul_zero, mul_zero]
          exact (rayOf_eq_zero_iff _).2 (hom_ext' S (by rw [h0]; rfl))
      rcases hLu (LargeIndecomposable.rayOf m) hmr0 hmL with ⟨h, he⟩ | ⟨h, he⟩
      · have hyz : y = z := congrArg BGRSRayCategory.as h
        subst hyz
        rw [eqToHom_refl, Category.id_comp] at he
        obtain ⟨c, hc⟩ := orbit_scalar S s' m (fun x hx _ _ ↦ hsl x hx) (fun x hx _ _ ↦ hsr x hx)
          ((unitRay_eq_iff _ _).1 he.symm)
        exact ⟨c, 0, by rw [← hmv, hc]; simp⟩
      · have hyb : y = bb := congrArg BGRSRayCategory.as h
        subst hyb
        rw [eqToHom_refl, Category.id_comp] at he
        obtain ⟨d, hd⟩ := orbit_scalar S t' m htl (fun x hx _ _ ↦ htr x hx)
          ((unitRay_eq_iff _ _).1 he.symm)
        exact ⟨0, d, by rw [← hmv, hd]; simp⟩
    choose c d hcd using key
    refine ⟨∑ v, c (objOf S v), ∑ v, d (objOf S v), ?_⟩
    rw [decomp_right S b, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← hcd, ev_objOf]
  have hfac_B : ∀ j ∈ Ring.jacobson B, ∃ b'' : B, j * ev S bb = b'' * t'.1 := by
    intro j hj
    have key : ∀ v : ι, ∃ b' : B, S.e v * j * ev S bb = b' * t'.1 := by
      intro v
      let n : bb ⟶ objOf S v := homOf S bb (objOf S v) j
      have hnv : n.1 = S.e v * j * ev S bb := by rw [homOf_val, ev_objOf]
      by_cases hn0 : n.1 = 0
      · exact ⟨0, by rw [← hnv, hn0, zero_mul]⟩
      have hnJ : n.1 ∈ Ring.jacobson B := by
        rw [homOf_val]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hj)
      obtain ⟨μ', hμ'⟩ := hfac (LargeIndecomposable.rayOf n) (not_isIso_rayOf S n hnJ)
      set μ : i ⟶ objOf S v := Quotient.out μ'
      have hμ : LargeIndecomposable.rayOf μ = μ' := unitRay_out μ'
      rw [← hμ, rayOf_comp] at hμ'
      by_cases hsp : IsBGRSSpecialZero t' μ
      · rw [bgrsRayRepresentativeProduct_eq_zero_of_special hsp] at hμ'
        exact absurd (congrArg Subtype.val ((rayOf_eq_zero_iff n).1 hμ')) hn0
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp] at hμ'
      obtain ⟨a, b, hab⟩ := (unitRay_eq_iff _ _).1 hμ'
      have hn : n = a.inv ≫ (t' ≫ μ) ≫ b.inv := by rw [hab]; simp
      obtain ⟨c, hc⟩ := corner_scalar S a.inv
      have e1 : t'.1 * a.inv.1 = algebraMap k B c * t'.1 := by
        have := htr _ hc
        rw [mul_sub, sub_eq_zero, ← mul_assoc, ← Algebra.commutes, mul_assoc, val_right] at this
        exact this
      refine ⟨b.inv.1 * μ.1 * algebraMap k B c, ?_⟩
      rw [← hnv, hn, comp_val, comp_val, comp_val, mul_assoc b.inv.1, mul_assoc μ.1, e1]
      simp only [mul_assoc]
    choose b' hb' using key
    refine ⟨∑ v, b' v, ?_⟩
    rw [decomp_left S (j * ev S bb), Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [← hb' v, mul_assoc]
  -- the opposite algebra
  have hB' := isMinimalRepInfinite_mop k hB
  obtain ⟨N, hN⟩ := jacobson_listProd (R := B)
  refine not_minimal_of_tiny (k := k) (B := Bᵐᵒᵖ) hB' (e := op (ev S i)) (e' := op (ev S z))
    (s := op s'.1) (t := op t'.1) (eb := op (ev S bb))
    (R := {x : Bᵐᵒᵖ | x.unop ∈ Ring.jacobson B}) (by rw [← MulOpposite.op_mul, ev_idem])
    (by rw [← MulOpposite.op_mul, ev_idem]) (MulOpposite.op_ne_zero_iff _ |>.2 hs0')
    (by rw [← MulOpposite.op_mul, val_left]) (by rw [← MulOpposite.op_mul, val_right]) (by rw [← MulOpposite.op_mul, val_left])
    (by rw [← MulOpposite.op_mul, val_right]) ⟨N, fun l hl hlR ↦ ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · apply MulOpposite.unop_injective
    rw [MulOpposite.unop_list_prod, MulOpposite.unop_zero]
    apply hN
    · simp [hl]
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hlR y hy
  · intro j hj
    rw [← MulOpposite.op_unop j, ← MulOpposite.op_mul, htr _ hj, MulOpposite.op_zero]
  · intro c hc
    have hc' : c.unop * ev S z = c.unop := by
      have := congrArg unop hc; rwa [MulOpposite.unop_mul, MulOpposite.unop_op] at this
    rw [← MulOpposite.op_unop c, ← MulOpposite.op_mul]
    have e1 : t'.1 * c.unop = t'.1 * (ev S bb * c.unop * ev S z) := by
      rw [mul_assoc, hc', ← mul_assoc, val_right]
    rw [e1, htr _ (S.corner_offdiag _ _ hvzb.symm _), MulOpposite.op_zero]
  · intro b hb hbJ
    have hb' : ev S i * b.unop = b.unop := by
      have := congrArg unop hb; rwa [MulOpposite.unop_mul, MulOpposite.unop_op] at this
    obtain ⟨c, d, hcd⟩ := hsocL_B b.unop hb' (fun j hj ↦ by
      obtain ⟨d, hd⟩ := hbJ (op j) (by simpa using hj)
      refine ⟨d, ?_⟩
      have := congrArg unop hd
      rwa [MulOpposite.unop_mul, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        ← Algebra.commutes] at this)
    refine ⟨c, d, ?_⟩
    rw [← MulOpposite.op_unop b, hcd]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_add, MulOpposite.unop_mul,
      MulOpposite.algebraMap_apply]
    rw [← Algebra.commutes c, ← Algebra.commutes d]
  · intro c hc hcJ
    have hc' : c.unop * ev S z = c.unop := by
      have := congrArg unop hc; rwa [MulOpposite.unop_mul, MulOpposite.unop_op] at this
    obtain ⟨a, ha⟩ := hsocR_B c.unop hc' (fun j hj ↦ by
      have := congrArg unop (hcJ (op j) (by simpa using hj))
      rwa [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] at this)
    refine ⟨a, ?_⟩
    rw [← MulOpposite.op_unop c, ha]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul, MulOpposite.algebraMap_apply]
    rw [← Algebra.commutes a]
  · intro j hj
    obtain ⟨b'', hb''⟩ := hfac_B j.unop hj
    refine ⟨op b'', ?_⟩
    rw [← MulOpposite.op_unop j, ← MulOpposite.op_mul, ← MulOpposite.op_mul, hb'']
  · intro b
    obtain ⟨l, h1, h2⟩ := local_e S (S.toIdempotents.projectiveVertex bb) b.unop
    refine ⟨l, ?_, ?_⟩
    · change (op (ev S bb) * b - algebraMap k Bᵐᵒᵖ l * op (ev S bb)).unop ∈ Ring.jacobson B
      simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply]
      rw [← Algebra.commutes l]
      exact h2
    · change (b * op (ev S bb) - algebraMap k Bᵐᵒᵖ l * op (ev S bb)).unop ∈ Ring.jacobson B
      simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply]
      rw [← Algebra.commutes l]
      exact h1

/-- **`NoTiny` for the opposite of the small ray category** of a minimal
representation-infinite algebra. -/
theorem noTiny_small_op (hB : IsMinimalRepInfinite B) [LocallySmall.{0} S.toIdempotents.RayCategory] :
    NoTiny (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := fun s t h ↦
  S.not_tinyAtDual hB _ _ (RaySmall.tinyAtDual_of_small (tinyAtDual_of_op h))

end SplitBasicData

end LargeIndecomposable
