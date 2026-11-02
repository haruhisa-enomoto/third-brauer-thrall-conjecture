module

public import LargeIndecomposable.MildContours.Basic.ExcBridge
public import LargeIndecomposable.MultiplicativeBases.Twisted.ExceptionalContourTwist
public import LargeIndecomposable.MildContours.Basic.ExcUnique
public import LargeIndecomposable.MildContours.Basic.CoreAssembly
public import LargeIndecomposable.BongartzTheorem.Reduction.ConnectBridge

/-!
# The proportionality step without exceptions

`scalarProportionality`: for a minimal representation-infinite distributive algebra there is a
zero-detecting lift for which every non-interlaced contour is deep or has proportional
values. Contours are deep or exceptional (`deep_or_exc`); an exceptional dumb-bell is
unique and is made to commute by twisting its loops (`db_lift`); the `Q₂'` contours are
made to commute one point at a time by twisting `β` or `a` (`q2_lift`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u

namespace RayCat

/-- Connectedness passes to the opposite category. -/
lemma ArrowConn.op {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]
    [Fintype Q] [IsFiniteRayCategory Q] (h : ArrowConn Q) :
    letI := isRayCategory_of_finiteRayCategory (C := Qᵒᵖ); ArrowConn Qᵒᵖ := by
  letI := isRayCategory_of_finiteRayCategory (C := Qᵒᵖ)
  intro V hout hin
  rcases h {X : Q | Opposite.op X ∈ V}
      (fun e he ha ↦ hin e.op ((isIrreducible_op e).2 he) ha)
      (fun e he hb ↦ hout e.op ((isIrreducible_op e).2 he) hb) with h' | h'
  · exact Or.inl fun X hX ↦ h' X.unop hX
  · exact Or.inr fun X ↦ h' X.unop

end RayCat

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

/-- **The dumb-bell lift**: an exceptional dumb-bell contour commutes after twisting its
loops. -/
theorem db_lift (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isFiniteRayCategory hd
    letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
    ∀ (L₀ : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory)), ExceptionalContourCommutation.ZD S.toIdempotents L₀ →
      ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
        DBExcPair (toP p) (toP q) →
        ∃ L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory), ExceptionalContourCommutation.ZD S.toIdempotents L ∧
          L.pathMap p = L.pathMap q := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  intro L₀ hz₀ i j p q hpq h
  obtain ⟨χ, μ, α, N, hχ, hμ, hα, hv, hw, -, -, hLx, hRy⟩ := h
  have hp : p = (Quiver.Path.nil.cons (fromArr μ)).cons (fromArr χ) := by
    rw [← fromP_toP p, hv]; rfl
  have hq : q = (Quiver.Path.nil.cons (fromArr α)).cons (fromArr μ) := by
    rw [← fromP_toP q, hw]; rfl
  subst hp hq
  have hji : j ≠ i := fun h ↦ N.hxy (by
    exact congrArg (fun z : RayVertex S.toIdempotents.RayCategory ↦ (⟨z.obj⟩ : RaySmall.{0} _)) h)
  obtain ⟨L, hz, he⟩ := ExceptionalContourCommutation.db_twist S.toIdempotents L₀ hz₀ hji (fromArr χ) (fromArr μ) (fromArr α) hpq
    (loopGen_transfer (fromArr χ) (by
      rw [reversedArr_fromArr]; exact fun f hf ↦ by rw [← hχ]; exact N.hρx f hf))
    (loopGen_transfer (fromArr α) (by
      rw [reversedArr_fromArr]; exact fun f hf ↦ by rw [← hα]; exact N.hρ f hf))
    (fun e he n ↦ kill_tgt_transfer (fromArr χ) (fromArr χ) (by
      rw [reversedArr_fromArr]; exact hLx) e he n)
    (fun e he n ↦ kill_src_transfer (fromArr α) (fromArr α) (by
      rw [reversedArr_fromArr]; exact hRy) e he n)
  exact ⟨L, hz, he⟩

/-- **The `Q₂'` lift**: a `Q₂'` contour commutes after twisting `β` (or `a`); the values of
the `Q₂'` contours at other points do not change. -/
theorem q2_lift (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isFiniteRayCategory hd
    letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
    ∀ (L₀ : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory)), ExceptionalContourCommutation.ZD S.toIdempotents L₀ →
      ∀ {i : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i i},
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
        Q2Pair (toP p) (toP q) →
        ∃ L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory), ExceptionalContourCommutation.ZD S.toIdempotents L ∧
          L.pathMap p = L.pathMap q ∧
          ∀ {i'' : RayVertex S.toIdempotents.RayCategory} {p'' q'' : Quiver.Path i'' i''}, i'' ≠ i →
            (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p'' q'' →
            Q2Pair (toP p'') (toP q'') →
            L.pathMap p'' = L₀.pathMap p'' ∧ L.pathMap q'' = L₀.pathMap q'' := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro L₀ hz₀ i p q hpq hQ
  have pIsA_of_isA : ∀ {X Y X' Y' : RayVert (RaySmall.{0} S.toIdempotents.RayCategory)} (T : X ⟶ Y)
      (e : X' ⟶ Y'), TwistLift.IsA (fromArr T) (fromArr e) → PIsA T e := by
    intro X Y X' Y' T e h
    obtain ⟨h1, h2, h3⟩ := h
    have hY : Y' = Y := by
      have := congrArg (fun z : RayVertex S.toIdempotents.RayCategory ↦ (⟨z.obj⟩ : RaySmall.{0} _)) h1
      exact this
    have hX : X' = X := by
      have := congrArg (fun z : RayVertex S.toIdempotents.RayCategory ↦ (⟨z.obj⟩ : RaySmall.{0} _)) h2
      exact this
    subst hX hY
    refine ⟨rfl, rfl, heq_of_eq ?_⟩
    have := congrArg reversedArr (eq_of_heq h3)
    rwa [reversedArr_fromArr, reversedArr_fromArr] at this
  obtain ⟨ρ, t, a, β, ht, hv, hw, hLG, h3, hst⟩ := hQ
  have hp : p = (Quiver.Path.nil.cons (fromArr ρ)).cons (fromArr ρ) := by
    rw [← fromP_toP p, hv]; rfl
  have hq : q = (Quiver.Path.nil.cons (fromArr β)).cons (fromArr a) := by
    rw [← fromP_toP q, hw]; rfl
  subst hp hq
  have hiT : i ≠ (⟨t.out.as⟩ : RayVertex S.toIdempotents.RayCategory) := fun h ↦ ht (by
    have := congrArg (fun z : RayVertex S.toIdempotents.RayCategory ↦ (⟨z.obj⟩ : RaySmall.{0} _)) h
    exact this.symm)
  have hEC := loopGen_transfer (fromArr ρ) (by rw [reversedArr_fromArr]; exact hLG)
  -- the values of a `Q₂'` contour at another point are unchanged when the twisted arrow `T`
  -- is not one of its arrows
  have other : ∀ {X Y : RayVert (RaySmall.{0} S.toIdempotents.RayCategory)} (T : X ⟶ Y)
      (L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory)),
      (∀ {i' j' : RayVertex S.toIdempotents.RayCategory} (e : i' ⟶ j'),
        ¬TwistLift.IsA (fromArr T) e → L.representative e = L₀.representative e) →
      (∀ {x' t' : RayVert (RaySmall.{0} S.toIdempotents.RayCategory)} (ρ' : x' ⟶ x') (a' : x' ⟶ t')
        (β' : t' ⟶ x'), x' ≠ RayVert.mk (⟨i.obj⟩ : RaySmall.{0} S.toIdempotents.RayCategory) →
        a'.1 ≫ β'.1 = ρ'.1 ≫ ρ'.1 →
        ρ'.1 ≫ ρ'.1 ≠ 0 → (¬PIsA T ρ' ∧ ¬PIsA T a' ∧ ¬PIsA T β')) →
      ∀ {i'' : RayVertex S.toIdempotents.RayCategory} {p'' q'' : Quiver.Path i'' i''},
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p'' q'' →
        Q2Pair (toP p'') (toP q'') →
        (RayVert.mk (⟨i''.obj⟩ : RaySmall.{0} S.toIdempotents.RayCategory) : RayVert _) ≠
          RayVert.mk (⟨i.obj⟩ : RaySmall.{0} S.toIdempotents.RayCategory) →
        L.pathMap p'' = L₀.pathMap p'' ∧ L.pathMap q'' = L₀.pathMap q'' := by
    intro X Y T L hag hap i'' p'' q'' hpq'' hQ'' hX
    obtain ⟨ρ'', t'', a'', β'', -, hv'', hw'', -, h3'', -⟩ := hQ''
    have hval'' : a''.1 ≫ β''.1 = ρ''.1 ≫ ρ''.1 := by
      have := congrArg (RaySmall.sh (X := (⟨i''.obj⟩ : RaySmall.{0} _)) (Y := ⟨i''.obj⟩)) hpq''.2
      rw [← pathVal_toP, ← pathVal_toP, hv'', hw''] at this
      change (𝟙 _ ≫ ρ''.1) ≫ ρ''.1 = (𝟙 _ ≫ a''.1) ≫ β''.1 at this
      simpa using this.symm
    have h0'' : ρ''.1 ≫ ρ''.1 ≠ 0 := fun h ↦ h3'' (by rw [← Category.assoc, h, zero_comp])
    obtain ⟨n1, n2, n3⟩ := hap ρ'' a'' β'' hX hval'' h0''
    have hp'' : p'' = (Quiver.Path.nil.cons (fromArr ρ'')).cons (fromArr ρ'') := by
      rw [← fromP_toP p'', hv'']; rfl
    have hq'' : q'' = (Quiver.Path.nil.cons (fromArr β'')).cons (fromArr a'') := by
      rw [← fromP_toP q'', hw'']; rfl
    subst hp'' hq''
    have e1 := hag (fromArr ρ'') (fun h ↦ n1 (pIsA_of_isA T ρ'' h))
    have e2 := hag (fromArr a'') (fun h ↦ n2 (pIsA_of_isA T a'' h))
    have e3 := hag (fromArr β'') (fun h ↦ n3 (pIsA_of_isA T β'' h))
    simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id]
    exact ⟨by rw [e1], by rw [e2, e3]⟩
  have hxne : ∀ {i'' : RayVertex S.toIdempotents.RayCategory}, i'' ≠ i →
      (RayVert.mk ⟨i''.obj⟩ : RayVert (RaySmall.{0} S.toIdempotents.RayCategory)) ≠ RayVert.mk ⟨i.obj⟩ :=
    fun hne h ↦ hne (by
      have := congrArg (fun z : RaySmall.{0} S.toIdempotents.RayCategory ↦
        (⟨z.as⟩ : RayVertex S.toIdempotents.RayCategory)) h
      exact this)
  rcases hst with hsrc | htgt
  · obtain ⟨L, hz, he, hag⟩ := ExceptionalContourCommutation.q2_twist_src S.toIdempotents L₀ hz₀ hiT (fromArr ρ) (fromArr a)
      (fromArr β) hpq hEC (fun e he n ↦ kill_src_transfer (fromArr β) (fromArr ρ) (by
        rw [reversedArr_fromArr, reversedArr_fromArr]; exact hsrc) e he n)
    exact ⟨L, hz, he, fun hne hpq'' hQ'' ↦ other β L hag (fun ρ' a' β' hX hval' h0' ↦
      q2_apart_src ρ β hsrc ht ρ' a' β' hX hval' h0') hpq'' hQ'' (hxne hne)⟩
  · obtain ⟨L, hz, he, hag⟩ := ExceptionalContourCommutation.q2_twist_tgt S.toIdempotents L₀ hz₀ hiT (fromArr ρ) (fromArr a)
      (fromArr β) hpq hEC (fun e he n ↦ kill_tgt_transfer (fromArr a) (fromArr ρ) (by
        rw [reversedArr_fromArr, reversedArr_fromArr]; exact htgt) e he n)
    exact ⟨L, hz, he, fun hne hpq'' hQ'' ↦ other a L hag (fun ρ' a' β' hX hval' h0' ↦
      q2_apart_tgt ρ a htgt ht ρ' a' β' hX hval' h0') hpq'' hQ'' (hxne hne)⟩

/-- **All `Q₂'` contours at once**: twisting one point at a time. -/
theorem q2_all (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isFiniteRayCategory hd
    letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
    letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
    MildHyp k (RaySmall.{0} S.toIdempotents.RayCategory) →
    ∀ (L₀ : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory)), ExceptionalContourCommutation.ZD S.toIdempotents L₀ →
      ∃ L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory), ExceptionalContourCommutation.ZD S.toIdempotents L ∧
        ∀ {i : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i i},
          (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
          Q2Pair (toP p) (toP q) → L.pathMap p = L.pathMap q := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  classical
  intro hM L₀ hz₀
  haveI : Finite (RayVertex S.toIdempotents.RayCategory) := Finite.of_equiv _ rayVertexEquiv.symm
  letI : Fintype (RayVertex S.toIdempotents.RayCategory) := Fintype.ofFinite _
  -- a `Q₂'` contour as a P-contour
  have contour : ∀ {i : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i i},
      (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
      ¬(properWhiskerInterlacementRelation
        (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
      pathVal (toP p) = pathVal (toP q) ∧ pathVal (toP p) ≠ 0 ∧ ¬Interlaced (toP p) (toP q) := by
    intro i p q hpq hni
    refine ⟨by rw [pathVal_toP, pathVal_toP, hpq.2], ?_, not_interlaced_toP hpq.1 hni⟩
    rw [pathVal_toP]; exact fun h ↦ hpq.1 ((RaySmall.sh_eq_zero_iff _).1 h)
  suffices H : ∀ F : Finset (RayVertex S.toIdempotents.RayCategory),
      ∃ L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory), ExceptionalContourCommutation.ZD S.toIdempotents L ∧
        ∀ {i : RayVertex S.toIdempotents.RayCategory}, i ∈ F → ∀ {p q : Quiver.Path i i},
          (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
          Q2Pair (toP p) (toP q) → L.pathMap p = L.pathMap q by
    obtain ⟨L, hz, hL⟩ := H Finset.univ
    exact ⟨L, hz, fun hpq hni hQ ↦ hL (Finset.mem_univ _) hpq hni hQ⟩
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨L₀, hz₀, fun hi ↦ absurd hi (Finset.notMem_empty _)⟩
  | insert x F hxF ih =>
    obtain ⟨L, hz, hL⟩ := ih
    by_cases hex : ∃ (p q : Quiver.Path x x),
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q ∧
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q ∧
        Q2Pair (toP p) (toP q)
    · obtain ⟨p₀, q₀, hpq₀, hni₀, hQ₀⟩ := hex
      obtain ⟨L', hz', he', hother⟩ := S.q2_lift hd L hz hpq₀ hQ₀
      refine ⟨L', hz', fun {i} hi {p q} hpq hni hQ ↦ ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hiF
      · obtain ⟨hv₀, h0₀, hn₀⟩ := contour hpq₀ hni₀
        obtain ⟨hv, -, -⟩ := contour hpq hni
        obtain ⟨h1, h2⟩ := q2_same hM hQ₀ hv₀ h0₀ hn₀ hQ hv
        have e1 : p = p₀ := by rw [← fromP_toP p, h1, fromP_toP]
        have e2 : q = q₀ := by rw [← fromP_toP q, h2, fromP_toP]
        rw [e1, e2, he']
      · have hix : i ≠ x := fun h ↦ hxF (h ▸ hiF)
        obtain ⟨h1, h2⟩ := hother hix hpq hQ
        rw [h1, h2, hL hiF hpq hni hQ]
    · refine ⟨L, hz, fun {i} hi {p q} hpq hni hQ ↦ ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hiF
      · exact (hex ⟨p, q, hpq, hni, hQ⟩).elim
      · exact hL hiF hpq hni hQ

end SplitBasicData

/-- **The proportionality step** ([mild] Theorem 3 with the exceptional contours made to
commute): for a minimal representation-infinite distributive algebra there is a
zero-detecting lift for which every non-interlaced contour is deep or has proportional
values. -/
theorem scalarProportionality : ScalarProportionality.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ)
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := Classical.decEq _
  letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ)
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ := Classical.decEq _
  have hM := S.mildHyp hB hd
  have hMo := hM.op
  have hE := S.endCyclic
  have hNPI : NoProjInj (RaySmall.{0} S.toIdempotents.RayCategory) := S.noProjInj_small hB
  have hNT : NoTiny (RaySmall.{0} S.toIdempotents.RayCategory) := S.noTiny_small hB
  have hNTo : NoTiny (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := S.noTiny_small_op hB
  have hNS : NoSplit (RaySmall.{0} S.toIdempotents.RayCategory) := S.noSplit_small hB
  have hOS : OneSidedCyclic (RaySmall.{0} S.toIdempotents.RayCategory) :=
    RaySmall.oneSidedCyclic (ray_oneSided S.toIdempotents)
  have hconn : ArrowConn (RaySmall.{0} S.toIdempotents.RayCategory) := fun V hout hin ↦
    S.isolated_trivial_small hB V
      ⟨fun i hi j hj f ↦ by
        by_contra hf; exact hj (mem_of_out V hout _ f le_rfl hf hi),
       fun i hi j hj f ↦ by
        by_contra hf; exact hi (mem_of_in V hin _ f le_rfl hf hj)⟩
  have hcore : CoreExcHyp (RaySmall.{0} S.toIdempotents.RayCategory) := fun C ω' hρ ↦
    coreExc hM hMo hE hOS hNPI hNS hNT hNTo hconn C ω' hρ
  have hcoreo : CoreExcHyp (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := fun C ω' hρ ↦
    coreExc (P := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ) (k := k) hMo hMo.op hE.op hOS.op hNPI.op
      hNS.op hNTo hNT.op_op hconn.op C ω' hρ
  have hfinI : Finite (TwoSidedIdeal B) := finite_twoSidedIdeal_of_isDistribIdeals k hd
  have hfinIop : Finite (TwoSidedIdeal Bᵐᵒᵖ) := finite_twoSidedIdeal_mop
  letI : HasBGRSDistributiveHomStructure k S.toIdempotents.op.ProjectiveCategory :=
    SplitBasicIdempotents.ProjectiveCategory.bgrsDistributiveHomStructureOfComparable
      S.toIdempotents.op fun U V hU hV ↦
        SplitBasicIdempotents.ProjectiveCategory.finiteIdeal_homSubbimodule_comparable
          S.toIdempotents.op U V hU hV
  obtain ⟨L₀, hz₀⟩ := CriticalFigure16Quotient.exists_zeroDetectingNormalizedLift S.toIdempotents
    (mildAlg_of_minimal hB) (mildAlg_mop_of_minimal hB)
  -- a lift on which every exceptional contour commutes
  obtain ⟨L, hz, hexc⟩ : ∃ L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory),
      ExceptionalContourCommutation.ZD S.toIdempotents L ∧ ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
        ExcPair (toP p) (toP q) → L.pathMap p = L.pathMap q := by
    by_cases hdb : ∃ (i j : RayVertex S.toIdempotents.RayCategory) (p q : Quiver.Path i j),
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q ∧
        DBExcPair (toP p) (toP q)
    · obtain ⟨i₀, j₀, p₀, q₀, hpq₀, hdb₀⟩ := hdb
      obtain ⟨L, hz, he⟩ := S.db_lift hd L₀ hz₀ hpq₀ hdb₀
      refine ⟨L, hz, fun {i j} {p q} hpq hni hE' ↦ ?_⟩
      obtain ⟨hx, hy, h⟩ := db_unique hdb₀ hE'
      have hj : j = j₀ := congrArg (fun z : RaySmall.{0} S.toIdempotents.RayCategory ↦
        (⟨z.as⟩ : RayVertex S.toIdempotents.RayCategory)) hx
      have hi : i = i₀ := congrArg (fun z : RaySmall.{0} S.toIdempotents.RayCategory ↦
        (⟨z.as⟩ : RayVertex S.toIdempotents.RayCategory)) hy
      subst hj hi
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : p = p₀ := by rw [← fromP_toP p, eq_of_heq h1, fromP_toP]
        have e2 : q = q₀ := by rw [← fromP_toP q, eq_of_heq h2, fromP_toP]
        rw [e1, e2, he]
      · have e1 : p = q₀ := by rw [← fromP_toP p, eq_of_heq h1, fromP_toP]
        have e2 : q = p₀ := by rw [← fromP_toP q, eq_of_heq h2, fromP_toP]
        rw [e1, e2, he]
    · obtain ⟨L, hz, hL⟩ := S.q2_all hd hM L₀ hz₀
      refine ⟨L, hz, fun {i j} {p q} hpq hni hE' ↦ ?_⟩
      rcases hE' with h | h | ⟨hji, h | h⟩
      · exact (hdb ⟨i, j, p, q, hpq, h⟩).elim
      · exact (hdb ⟨i, j, q, p, (rayPathContourRelation (C := S.toIdempotents.RayCategory)).symm' hpq,
          h⟩).elim
      · have hij : i = j := congrArg (fun z : RaySmall.{0} S.toIdempotents.RayCategory ↦
          (⟨z.as⟩ : RayVertex S.toIdempotents.RayCategory)) hji
        subst hij
        exact hL hpq hni h
      · have hij : i = j := congrArg (fun z : RaySmall.{0} S.toIdempotents.RayCategory ↦
          (⟨z.as⟩ : RayVertex S.toIdempotents.RayCategory)) hji
        subst hij
        exact (hL ((rayPathContourRelation (C := S.toIdempotents.RayCategory)).symm' hpq)
          (fun h' ↦ hni (Relation.EqvGen.symm _ _ h')) h).symm
  refine ⟨L, hz, fun {i j} {p q} hpq hni ↦ ?_⟩
  have h0 : pathVal (toP p) ≠ 0 := by
    rw [pathVal_toP]; exact fun h ↦ hpq.1 ((RaySmall.sh_eq_zero_iff _).1 h)
  rcases MildContour.deep_or_exc (k := k) hM hMo hE hcore hcoreo (toP p) (toP q)
      (by rw [pathVal_toP, pathVal_toP, hpq.2]) h0 (not_interlaced_toP hpq.1 hni) with
    ⟨hy, hx⟩ | hE'
  · left
    refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · have hi := S.not_isIso_unitRay_of_mem_jacobson a ha
      have := hx (RaySmall.sh (unitRay a.asHom)) (fun h ↦ hi ((RaySmall.isIso_sh_iff _).1 h))
      rw [pathVal_toP, ← RaySmall.sh_comp, RaySmall.sh_eq_zero_iff] at this
      exact this
    · have hi := S.not_isIso_unitRay_of_mem_jacobson b hb
      have := hy (RaySmall.sh (unitRay b.asHom)) (fun h ↦ hi ((RaySmall.isIso_sh_iff _).1 h))
      rw [pathVal_toP, ← RaySmall.sh_comp, RaySmall.sh_eq_zero_iff] at this
      exact this
  · right
    refine ⟨fun h ↦ hpq.1 ((hz p).1 h), 1, ?_⟩
    change L.pathMap p = ((1 : kˣ) : k) • L.pathMap q
    rw [hexc hpq hni hE']
    simp

end LargeIndecomposable
