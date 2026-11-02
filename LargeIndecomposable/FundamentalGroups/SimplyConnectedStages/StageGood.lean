module

public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.StageSC
public import LargeIndecomposable.RayCategories.Quotients.NestQuot
public import LargeIndecomposable.RayCategories.Basic.LoopFree
public import LargeIndecomposable.Coverings.UniversalCover.LocalSC
public import LargeIndecomposable.Coverings.UniversalCover.CoverCountable
public import LargeIndecomposable.Coverings.UniversalCover.CoverChain
public import LargeIndecomposable.Crowns.Basic.CrownReduction

/-!
# Good stages

A stage `Y_K` is *good* when it is cycle-free, interval-finite and simply connected (`Good`).
If `P` is loop-free, the lift of `u` at a point `⟨b, w⟩` with `w ∉ K` survives in `Y_K`
(`uT_not_mem`): a factorization through a killed lift at another point `⟨b, w'⟩` would need a
nonzero endomorphism of `b` of class `w⁻¹ w' ≠ 1`. The lifts of the `uᵢ` survive in every stage
(`usT_not_mem`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {x₀ : P} {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i}

attribute [local instance] isRayCategory_of_finiteRayCategory

namespace Stage

variable (D : RedData α)

lemma killed_mono {K K' : Set (vtx x₀ ⟶ vtx b)} (h : K' ⊆ K) {x y : RayVert (Cover x₀)}
    (e : x ⟶ y) (he : killed (α := α) K' e) : killed (α := α) K e := by
  obtain ⟨w, hw, hx, hm⟩ := he
  exact ⟨w, h hw, hx, hm⟩

lemma arrSetIdeal_mono {K K' : Set (vtx x₀ ⟶ vtx b)} (h : K' ⊆ K) {X Y : Cover x₀} (f : X ⟶ Y)
    (hf : (arrSetIdeal (killed (x₀ := x₀) (α := α) K')).mem f) :
    (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem f := by
  rcases hf with hf | ⟨x, y, e, hS, a, c, hf⟩
  · exact Or.inl hf
  · exact Or.inr ⟨x, y, e, killed_mono h e hS, a, c, hf⟩

lemma val_uT (w : vtx x₀ ⟶ vtx b) : Cover.val (pathVal (uT D w)) = pathVal D.u := by
  rw [Cover.pathVal_projPath, projPath_uT]

lemma val_usT (w : vtx x₀ ⟶ vtx b) (i : ι) :
    Cover.val (pathVal (usT D w i)) = pathVal (D.us i) := by
  rw [Cover.pathVal_projPath, eq_of_heq (projPath_usT D w i)]

lemma aT_comp_usT (w : vtx x₀ ⟶ vtx b) (i : ι) :
    (aT D w i).1 ≫ pathVal (usT D w i) = pathVal (uT D w) := by
  apply Cover.val_injective
  rw [Cover.val_comp, val_usT, val_uT]
  change (D.a i).1 ≫ _ = _
  rw [D.a_val, D.hcomp]

/-- The lifts of `uᵢ` survive in every stage. -/
lemma usT_not_mem (K : Set (vtx x₀ ⟶ vtx b)) (w : vtx x₀ ⟶ vtx b) (i : ι) :
    ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem (pathVal (usT D w i)) := by
  rintro (h | ⟨x, y, e, ⟨w', -, -, hm⟩, a, c, h⟩)
  · apply D.hus i
    rw [← val_usT D w i, h]
    exact (arrowIdeal α).zero_mem _ _
  · apply D.hus i
    rw [← val_usT D w i, h, Cover.val_comp, Cover.val_comp]
    exact (arrowIdeal α).precomp _ ((arrowIdeal α).postcomp _ hm)

/-- **In a loop-free category the lift of `u` survives** at points outside `K`. -/
lemma uT_not_mem (hLF : LoopFree P) {K : Set (vtx x₀ ⟶ vtx b)} {w : vtx x₀ ⟶ vtx b}
    (hw : w ∉ K) : ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem (pathVal (uT D w)) := by
  have h0 : pathVal (uT D w) ≠ 0 := fun h ↦ D.hu0 (by rw [← val_uT D w, h]; rfl)
  rintro (h | ⟨x, y, e, ⟨w', hw', hx, -⟩, a, c, h⟩)
  · exact h0 h
  · subst hx
    have ha : a ≠ 0 := fun ha ↦ h0 (by rw [h, ha, zero_comp])
    have hu := u_eq a ha
    have hl := hLF b (Cover.val a) (RayCat.val_ne_zero ha)
    change w' = w ≫ cls (Cover.val a) _ at hu
    rw [hl, Category.comp_id] at hu
    exact hw (hu ▸ hw')

/-- The lifts of the `aᵢ` at points of `K` lie in the ideal of `Y_K`, hence so does `ũ`. -/
lemma uT_mem {K : Set (vtx x₀ ⟶ vtx b)} {w : vtx x₀ ⟶ vtx b} (hw : w ∈ K) (i : ι) :
    (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem (pathVal (uT D w)) := by
  rw [← aT_comp_usT D w i]
  exact Or.inr ⟨_, _, aT D w i, (aT_killed_iff K D w i).2 hw, 𝟙 _, pathVal (usT D w i),
    (Category.id_comp _).symm⟩

/-- A stage is good: cycle-free, interval-finite and simply connected. -/
def Good (K : Set (vtx x₀ ⟶ vtx b)) : Prop :=
  (∀ (x : RayVert (Y (x₀ := x₀) (α := α) K)) (p : Quiver.Path x x), p.length = 0) ∧
    (∀ a a' : Y (x₀ := x₀) (α := α) K, (interval a a').Finite) ∧
      ∀ c : ArrowWeight (Y (x₀ := x₀) (α := α) K), IsCocycle c → IsCoboundary c

lemma avoids_uT' (K : Set (vtx x₀ ⟶ vtx b)) (w : vtx x₀ ⟶ vtx b) :
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) (uT D w) :=
  avoidsI_of_proj K _ (by rw [projPath_uT]; exact D.hu)

lemma avoids_usT' (K : Set (vtx x₀ ⟶ vtx b)) (w : vtx x₀ ⟶ vtx b) (i : ι) :
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) (usT D w i) :=
  avoidsI_of_proj K _ (by rw [eq_of_heq (projPath_usT D w i)]; exact D.avoids_us i)

instance (K : Set (vtx x₀ ⟶ vtx b)) : Countable (Y (x₀ := x₀) (α := α) K) :=
  Function.Injective.countable (f := fun q : Y (x₀ := x₀) (α := α) K ↦ q.as)
    fun q q' h ↦ by cases q; cases q'; cases h; rfl

section Step

variable (hα : ∀ i, ¬IsIso (α i))

include hα in
/-- A new arrow of `Y_{K ∖ {w₀}}` is the lift of some `aᵢ` at `⟨b, w₀⟩`. -/
lemma new_data {K : Set (vtx x₀ ⟶ vtx b)} {w₀ : vtx x₀ ⟶ vtx b}
    {x y : RayVert (Y (x₀ := x₀) (α := α) (K \ {w₀}))} (e : x ⟶ y)
    (he : IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) (isProper (K \ {w₀})) e) :
    ∃ i : ι, x = RayVert.mk (⟨pt w₀⟩ : Y (x₀ := x₀) (α := α) (K \ {w₀})) ∧
      y = RayVert.mk (⟨⟨d i, w₀ ≫ cls (D.a i).1 (D.a i).2.1⟩⟩ :
        Y (x₀ := x₀) (α := α) (K \ {w₀})) ∧
      HEq (liftArrQ (isProper (K \ {w₀})) e) (aT D w₀ i) := by
  have hk : killed (α := α) K (liftArrQ (isProper (K \ {w₀})) e) := mem_of_irreducible _ _ he
  obtain ⟨w, hw, i, hx, hy, hh⟩ := eq_aT_of_killed (hα := hα) D K _ hk
  have hw' : w = w₀ := by
    by_contra hne
    apply liftArrQ_not_mem (isProper (K \ {w₀})) e
    obtain ⟨w'', hw'', hx', hm⟩ := hk
    have h1 : w'' = w := eq_of_heq (Cover.mk.inj (hx'.symm.trans hx)).2
    refine Or.inr ⟨_, _, liftArrQ (isProper (K \ {w₀})) e,
      ⟨w'', ⟨hw'', fun h2 ↦ hne (h1 ▸ h2)⟩, hx', hm⟩, 𝟙 _, 𝟙 _, by simp⟩
  subst hw'
  refine ⟨i, ?_, ?_, hh⟩
  · obtain ⟨xa⟩ := x
    change xa = pt w at hx
    subst hx
    rfl
  · obtain ⟨ya⟩ := y
    change ya = _ at hy
    subst hy
    rfl

include D hα in
/-- **One more point: a good stage stays good when the lifts at one point are restored.** -/
theorem good_step (hLF : LoopFree P) (hL : LeftCancel P) (hR : RightCancel P)
    (hCB : ChainBounded P) {K : Set (vtx x₀ ⟶ vtx b)} {w₀ : vtx x₀ ⟶ vtx b} (hw₀ : w₀ ∈ K)
    (hK : Good (α := α) K) : Good (α := α) (K \ {w₀}) := by
  have hI : (arrSetIdeal (killed (x₀ := x₀) (α := α) (K \ {w₀}))).IsProper := isProper _
  have hJ : (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).IsProper := isProper _
  have hIJ : ∀ {X Y : Cover x₀} (f : X ⟶ Y),
      (arrSetIdeal (killed (x₀ := x₀) (α := α) (K \ {w₀}))).mem f →
        (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem f :=
    fun f h ↦ arrSetIdeal_mono Set.diff_subset f h
  -- simple connectivity of the old stage, locally
  have hLB : LeftCancel (Y (x₀ := x₀) (α := α) K) := leftCancel_quotient _ (leftCancel_cover hL)
  have hRB : RightCancel (Y (x₀ := x₀) (α := α) K) := rightCancel_quotient _ (rightCancel_cover hR)
  have hCBB : ChainBounded (Y (x₀ := x₀) (α := α) K) := chainBounded_quotI (chainBounded_cover hCB)
  have hscB : ∀ S : Set (Y (x₀ := x₀) (α := α) K), S.Finite → ConvexR S →
      ∀ c : ArrowWeight (Y (x₀ := x₀) (α := α) K), IsCocycleOn S c → IsCoboundaryOn S c :=
    fun S hS hSc c hc ↦ isCoboundaryOn_of_global hLB hRB hCBB hK.2.1 (fun x p ↦ hK.1 x p) hK.2.2
      hS hSc c hc
  -- the data at a new arrow
  have hrel0 : ∀ {y : RayVert (Y (x₀ := x₀) (α := α) (K \ {w₀}))}
      (e : RayVert.mk (⟨pt w₀⟩ : Y (x₀ := x₀) (α := α) (K \ {w₀})) ⟶ y),
      IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) hI e →
      ∃ (z : RayVert (Y (x₀ := x₀) (α := α) (K \ {w₀}))) (ue : Quiver.Path y z)
        (u : Quiver.Path (RayVert.mk (⟨pt w₀⟩ : Y (x₀ := x₀) (α := α) (K \ {w₀}))) z),
        OldPath (IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) hI) ue ∧
        OldPath (IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) hI) u ∧
        e.1 ≫ pathVal ue = pathVal u ∧ pathVal u ≠ 0 ∧
        ∀ zz : Quiver.Path y (RayVert.mk (⟨pt w₀⟩ : Y (x₀ := x₀) (α := α) (K \ {w₀}))),
          OldPath (IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) hI) zz → False := by
    intro y e he
    obtain ⟨i, -, hy, hh⟩ := new_data D hα e he
    obtain ⟨ya⟩ := y
    have hy' := congrArg CategoryTheory.Quotient.as hy
    change ya = _ at hy'
    subst hy'
    have hl : liftArrQ hI e = aT D w₀ i := eq_of_heq hh
    refine ⟨_, toQI hI (usT D w₀ i) (avoidsI_of_avoidsJ hIJ _ (avoids_usT' D K w₀ i)),
      toQI hI (uT D w₀) (avoidsI_of_avoidsJ hIJ _ (avoids_uT' D K w₀)),
      oldPath_toQI hI hIJ _ (avoids_usT' D K w₀ i), oldPath_toQI hI hIJ _ (avoids_uT' D K w₀),
      ?_, ?_, fun zz hzz ↦ ?_⟩
    · erw [pathVal_toQI, pathVal_toQI]
      have h1 : e.1 = (qF (I := arrSetIdeal (killed (x₀ := x₀) (α := α) (K \ {w₀})))).map
          (liftArrQ hI e).1 := (Quot.out_eq e.1).symm
      rw [h1, hl, ← Functor.map_comp, aT_comp_usT]
    · erw [pathVal_toQI]
      exact ((arrSetIdeal _).functor_map_ne_zero_iff _).2
        (uT_not_mem D hLF fun h ↦ h.2 rfl)
    · have hpar := pathVal_eq_of_parallel (A := Y (x₀ := x₀) (α := α) K) (fun x p ↦ hK.1 x p)
        hK.2.1 hscB _ (⟨⟨d i, w₀ ≫ cls (D.a i).1 (D.a i).2.1⟩⟩ : Y (x₀ := x₀) (α := α) K)
        (⟨uEnd D w₀⟩ : Y (x₀ := x₀) (α := α) K) rfl
        ((toB hI hJ zz hzz).comp (toQI hJ (uT D w₀) (avoids_uT' D K w₀)))
        (toQI hJ (usT D w₀ i) (avoids_usT' D K w₀ i))
      erw [pathVal_comp, pathVal_toQI, pathVal_toQI,
        ((arrSetIdeal _).functor_map_eq_zero_iff _).2 (uT_mem D hw₀ i), comp_zero] at hpar
      have h5 := pathVal_toQI hJ (usT D w₀ i) (avoids_usT' D K w₀ i)
      exact ((arrSetIdeal _).functor_map_ne_zero_iff _).2 (usT_not_mem D K w₀ i)
        (h5.symm.trans hpar.symm)
  have hsrc : ∀ {x y : RayVert (Y (x₀ := x₀) (α := α) (K \ {w₀}))} (e : x ⟶ y),
      IsNewA (J := arrSetIdeal (killed (x₀ := x₀) (α := α) K)) hI e →
        x = RayVert.mk (⟨pt w₀⟩ : Y (x₀ := x₀) (α := α) (K \ {w₀})) :=
    fun e he ↦ (new_data D hα e he).choose_spec.1
  have hcfA : ∀ (x : RayVert (Y (x₀ := x₀) (α := α) (K \ {w₀}))) (p : Quiver.Path x x),
      p.length = 0 :=
    cycleFree_of_step hsrc (oldCycle_trivial hI hJ hK.1) fun e he ↦ by
      obtain ⟨z, ue, u, -, -, h1, h2, h3⟩ := hrel0 e he
      exact ⟨z, u, ue, h1, h2, fun zz hzz ↦ (h3 zz hzz).elim⟩
  refine ⟨hcfA, intervalFinite_of_step hsrc hcfA (oldInterval_finite hI hJ hK.2.1),
    isCoboundary_of_nested hI hJ hIJ hK.2.2 fun {x y} e he ↦ ?_⟩
  obtain rfl := hsrc e he
  obtain ⟨z, ue, u, h1, h2, h3, h4, -⟩ := hrel0 e he
  exact ⟨z, ue, u, h1, h2, h3, h4⟩

end Step

end Stage

end LargeIndecomposable.RayCat
