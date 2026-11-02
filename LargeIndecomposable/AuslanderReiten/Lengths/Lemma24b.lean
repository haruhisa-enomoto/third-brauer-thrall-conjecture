module

public import LargeIndecomposable.AuslanderReiten.Lengths.Lemma24bPre

/-!
# Bongartz's Lemma 2.4 (b)

For a convex set `T'` and a module `V` over the quotient algebra `A' = A / ⟨e_v : v ∉ T'⟩`:
`IrrIn V` says that every irreducible map of `A`-modules into `V` starts at a module living on
`T'`; `IrrOut V` says that every irreducible map out of `V` ends at such a module.

`irrIn_step`: if `T'` is closed under successors and every proper predecessor of `V` has `IrrOut`,
then `V` has `IrrIn`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {T' : Set D.ι}

/-- Irreducible maps into `V` start at modules living on `T'`. -/
def IrrIn (T' : Set D.ι) (V : FDMod k (D.QAlg T')) : Prop :=
  ∀ X : FDMod k A, IndNT X → ∀ f : X ⟶ resFD (D.qmap T') V, IsIrr f → LivesOn T' X

/-- Irreducible maps out of `V` end at modules living on `T'`. -/
def IrrOut (T' : Set D.ι) (V : FDMod k (D.QAlg T')) : Prop :=
  ∀ Y : FDMod k A, IndNT Y → ∀ f : resFD (D.qmap T') V ⟶ Y, IsIrr f → LivesOn T' Y

lemma irrOut_iso {V V' : FDMod k (D.QAlg T')} (h : IsoM V V') (hV' : IrrOut T' V') :
    IrrOut T' V := by
  intro Y hY f hf
  obtain ⟨g, hg⟩ := h.symm.res (φ := D.qmap T')
  exact hV' Y hY (g ≫ f) (hf.iso_comp g hg)

/-- A decomposition of a nonzero module has a summand. -/
lemma Decomp.nonempty_of_nontrivial {k' A'' : Type u} [Field k'] [Ring A''] [Algebra k' A'']
    {E : FDMod k' A''} (d : Decomp E) [Nontrivial E] : Nonempty d.ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  apply he
  have := LinearMap.congr_fun d.sum_id e
  simp only [LinearMap.sum_apply, Finset.univ_eq_empty, Finset.sum_empty,
    LinearMap.zero_apply, LinearMap.id_apply] at this
  exact this.symm

omit [FiniteDimensional k A] in
/-- Indecomposability transfers along isomorphisms. -/
lemma indNT_of_iso {k' A'' : Type u} [Field k'] [Ring A''] [Algebra k' A'']
    {X Y : FDMod k' A''} (h : IsoM X Y) (hX : IndNT X) : IndNT Y := by
  obtain ⟨g, hg⟩ := h
  let e := LinearEquiv.ofBijective (FDMod.lin g) hg
  refine ⟨fun U V hUV ↦ ?_, ?_⟩
  · have hc : IsCompl (U.comap (FDMod.lin g)) (V.comap (FDMod.lin g)) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hx'
        have := Submodule.disjoint_def.1 hUV.disjoint _ hx hx'
        exact hg.1 (by rw [this, map_zero])
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have hx : FDMod.lin g x ∈ U ⊔ V := hUV.codisjoint.eq_top ▸ Submodule.mem_top
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hx
        have h1 : x = e.symm u + e.symm v := by
          apply hg.1
          change FDMod.lin g x = e (e.symm u + e.symm v)
          rw [map_add, e.apply_symm_apply, e.apply_symm_apply, huv]
        rw [h1]
        refine Submodule.add_mem_sup ?_ ?_
        · change e (e.symm u) ∈ U; rwa [e.apply_symm_apply]
        · change e (e.symm v) ∈ V; rwa [e.apply_symm_apply]
    have hbot : ∀ W : Submodule A'' Y, W.comap (FDMod.lin g) = ⊥ → W = ⊥ := by
      intro W hW
      rw [eq_bot_iff]
      intro y hy
      have : e.symm y ∈ W.comap (FDMod.lin g) := by
        change e (e.symm y) ∈ W; rwa [e.apply_symm_apply]
      rw [hW, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← e.apply_symm_apply y, this, map_zero]
    rcases hX.1 _ _ hc with h | h
    · exact Or.inl (hbot U h)
    · exact Or.inr (hbot V h)
  · haveI := hX.2
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    exact ⟨⟨e x, 0, fun h ↦ hx (e.injective (by rw [h, map_zero]))⟩⟩

variable (hT : D.ConvexSet T')

include hT in
/-- **Lemma 2.4 (b), maps into `V`.** -/
theorem irrIn_step (hsucc : ∀ z, z ∈ T' → LivesOn T' (projE (k := k) (D.idem z)))
    {V : FDMod k (D.QAlg T')} (hV : IndNT V)
    (hOut : ∀ m W, 0 < m → PredN V m W → IrrOut T' W) : IrrIn T' V := by
  classical
  have hφ := D.qmap_surjective T'
  intro X hX f hf
  haveI := hV.2
  haveI : IsLocalRing (Module.End (D.QAlg T') V) := hV.1.isLocalRing (k := k)
  by_cases hp : IsFreeSummand (D.QAlg T') V
  · obtain ⟨z, hz, hiso⟩ := (D.quot hT).iso_proj_of_freeSummand hV hp
    have hiso2 : IsoM (resFD (D.qmap T') V) (projE (k := k) (D.idem z)) :=
      (hiso.res (φ := D.qmap T')).trans (isoM_res_proj hT z (hsucc z hz)).symm
    obtain ⟨g, hg⟩ := hiso2
    obtain ⟨v, -, r, hr⟩ := (hf.comp_iso g hg).factor_rightAS (D.isRightAS_radP z (hT.1 hz))
    have hvinj : Function.Injective (FDMod.lin v) := fun a b h ↦ by
      have h1 := LinearMap.congr_fun (congrArg FDMod.lin hr) a
      have h2 := LinearMap.congr_fun (congrArg FDMod.lin hr) b
      change FDMod.lin r (FDMod.lin v a) = a at h1
      change FDMod.lin r (FDMod.lin v b) = b at h2
      rw [← h1, ← h2, h]
    exact livesOn_of_inj v hvinj (livesOn_of_inj (D.radInc z) Subtype.val_injective (hsucc z hz))
  · obtain ⟨E', g', hg', hgs, hmin, hleft, hKind, hKnt⟩ := exists_arSeq V hp
    let K' : FDMod k (D.QAlg T') := FDMod.ofSub (LinearMap.ker (FDMod.lin g'))
    let f' : K' ⟶ E' := (FDMod.ofLin ((LinearMap.ker (FDMod.lin g')).subtype))
    have hf'inj : Function.Injective (FDMod.lin f') := Subtype.val_injective
    have hex' : LinearMap.range (FDMod.lin f') = LinearMap.ker (FDMod.lin g') :=
      Submodule.range_subtype _
    have hK : IndNT K' := ⟨hKind, hKnt⟩
    -- `K'` is a proper predecessor of `V`
    obtain ⟨d'⟩ := FDMod.exists_decomp E'
    haveI : Nontrivial E' := by
      obtain ⟨vv, hvv⟩ := exists_ne (0 : V)
      obtain ⟨e, rfl⟩ := hgs vv
      exact ⟨⟨e, 0, fun h ↦ hvv (by rw [h, map_zero])⟩⟩
    obtain ⟨i⟩ := DirData.Decomp.nonempty_of_nontrivial d'
    have hi : IndNT (d'.obj i) := ⟨d'.indec i, d'.nt i⟩
    obtain ⟨j1, a1, ha1⟩ := (isIrr_summand hg' hmin hV d' i).iso_chosenMin hi hV
    let W1 := (chosenMin V hV).d.obj j1
    have hW1 : PredN V 1 W1 := PredN.step (PredN.zero hV) hV j1
    have hleftmin := leftMinimal_of_arSeq hleft hf'inj hg' hgs hex' hmin
    have hirr2 := (isIrr_summandL hleft hleftmin hK d' i).comp_iso a1 ha1
    obtain ⟨j2, hj2⟩ := hirr2.iso_chosenMin hK hW1.indNT
    have hW2 : PredN V 2 _ := PredN.step hW1 hW1.indNT j2
    have hOutK : IrrOut T' K' := irrOut_iso hj2 (hOut 2 _ (by norm_num) hW2)
    -- the `A`-Auslander–Reiten sequence starting at `res K'`
    let rf' := resHom (D.qmap T') f'
    have hrinj : Function.Injective (FDMod.lin rf') := res_injective hf'inj
    have hrns : ¬∃ r, rf' ≫ r = 𝟙 _ := fun h ↦ hleft.1 ((splitMono_res_iff hφ f').1 h)
    have hKA : IndNT (resFD (D.qmap T') K') := (indNT_res_iff hφ K').2 hK
    haveI : Nontrivial (resFD (D.qmap T') K') := hKA.2
    haveI : IsLocalRing (Module.End A (resFD (D.qmap T') K')) := hKA.1.isLocalRing (k := k)
    obtain ⟨E'', f'', hf''L, hf''inj, hf''min, hg''R, hC⟩ :=
      exists_arSeqL (resFD (D.qmap T') K') (resFD (D.qmap T') E') rf' hrinj hrns
    obtain ⟨d''⟩ := FDMod.exists_decomp E''
    have hE'' : LivesOn T' E'' := livesOn_of_decomp d'' fun j ↦
      hOutK _ ⟨d''.indec j, d''.nt j⟩ _ (isIrr_summandL hf''L hf''min hKA d'' j)
    have hrL : IsLeftAS rf' := isLeftAS_res hT hleft hf''L hE''
    have hVA : IndNT (resFD (D.qmap T') V) := (indNT_res_iff hφ V).2 hV
    haveI : Nontrivial (resFD (D.qmap T') V) := hVA.2
    haveI : IsLocalRing (Module.End A (resFD (D.qmap T') V)) := hVA.1.isLocalRing (k := k)
    haveI : Nontrivial (FDMod.ofQuot E'' (LinearMap.range (FDMod.lin f''))) := hC.2
    haveI : IsLocalRing (Module.End A (FDMod.ofQuot E'' (LinearMap.range (FDMod.lin f'')))) :=
      hC.1.isLocalRing (k := k)
    obtain ⟨a, ha⟩ := coker_iso_of_leftAS (g := (show E'' ⟶ FDMod.ofQuot E''
        (LinearMap.range (FDMod.lin f'')) from (FDMod.ofLin ((LinearMap.range (FDMod.lin f'')).mkQ))))
      hf''L hf''inj (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm
      hrL hrinj (res_surjective hgs) (res_exact hex')
    obtain ⟨v, -, r, hr⟩ := hf.factor_rightAS (isRightAS_comp_iso hg''R a ha)
    have hvinj : Function.Injective (FDMod.lin v) := fun a b h ↦ by
      have h1 := LinearMap.congr_fun (congrArg FDMod.lin hr) a
      have h2 := LinearMap.congr_fun (congrArg FDMod.lin hr) b
      change FDMod.lin r (FDMod.lin v a) = a at h1
      change FDMod.lin r (FDMod.lin v b) = b at h2
      rw [← h1, ← h2, h]
    exact livesOn_of_inj v hvinj hE''

/-- **Lemma 2.4 (b), maps out of `V`.** -/
theorem irrOut_step (sd : ∀ z, Decomp (D.RadP z)) (hsd : ∀ z, z ∈ D.T → D.SepDecomp z (sd z))
    {x : D.ι} (i0 : (sd x).ι) {V : FDMod k (D.QAlg (Bset x (sd x) i0))} (hV : IndNT V)
    (hIn : IrrIn (Bset x (sd x) i0) V)
    (hOut : ∀ m W, 0 < m → PredN V m W → IrrOut (Bset x (sd x) i0) W)
    (hR : ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0)) :
    IrrOut (Bset x (sd x) i0) V := by
  classical
  have hB : D.ConvexSet (Bset x (sd x) i0) := Bset_convex x (sd x) i0
  have hφ := D.qmap_surjective (Bset x (sd x) i0)
  have hVA : IndNT (resFD (D.qmap (Bset x (sd x) i0)) V) := (indNT_res_iff hφ V).2 hV
  intro Y hY f hf
  haveI := hY.2
  haveI : IsLocalRing (Module.End A Y) := hY.1.isLocalRing (k := k)
  by_cases hp : IsFreeSummand A Y
  · obtain ⟨y, hy, g, hg⟩ := D.iso_proj_of_freeSummand hY hp
    have hsupp : D.Supp (resFD (D.qmap (Bset x (sd x) i0)) V) ⊆ (Bset x (sd x) i0) := (livesOn_iff_supp _ _).1 (livesOn_res V)
    rcases lemma24a sd hsd i0 hVA hsupp hy (hf.comp_iso g hg) with hyB | ⟨-, hiso⟩
    · exact livesOn_iso (IsoM.symm (⟨g, hg⟩ : IsoM Y _)) (livesOn_proj x (sd x) i0 hyB)
    · exact absurd hiso hR
  · obtain ⟨E, g, hg, hgs, hmin, hleft, hKind, hKnt⟩ := exists_arSeq Y hp
    let K : FDMod k A := FDMod.ofSub (LinearMap.ker (FDMod.lin g))
    let fK : K ⟶ E := (FDMod.ofLin ((LinearMap.ker (FDMod.lin g)).subtype))
    have hfKinj : Function.Injective (FDMod.lin fK) := Subtype.val_injective
    have hexK : LinearMap.range (FDMod.lin fK) = LinearMap.ker (FDMod.lin g) :=
      Submodule.range_subtype _
    have hK : IndNT K := ⟨hKind, hKnt⟩
    obtain ⟨d⟩ := FDMod.exists_decomp E
    obtain ⟨v, -, r, hr⟩ := hf.factor_rightAS hg
    obtain ⟨j, hj⟩ := iso_summand_of_splitMono hVA d v r hr
    obtain ⟨b, hb⟩ := hj.symm
    have hleftmin := leftMinimal_of_arSeq hleft hfKinj hg hgs hexK hmin
    have hirr := (isIrr_summandL hleft hleftmin hK d j).comp_iso b hb
    have hKl : LivesOn (Bset x (sd x) i0) K := hIn K hK _ hirr
    -- `K` is the restriction of a predecessor of `V`
    let K3 := descendQ K hKl
    have hK3iso : IsoM K (resFD (D.qmap (Bset x (sd x) i0)) K3) := isoM_descend' K hKl
    have hK3 : IndNT K3 := (indNT_res_iff hφ K3).1 (indNT_of_iso hK3iso hK)
    have hirr3 : IsIrr (unresHom hφ (descIsoQ K hKl ≫ (fK ≫ d.proj j) ≫ b)) :=
      IsIrr.unres hφ (hirr.iso_comp (descIsoQ K hKl) Function.bijective_id)
    obtain ⟨j1, hj1⟩ := hirr3.iso_chosenMin hK3 hV
    have hW1 : PredN V 1 ((chosenMin V hV).d.obj j1) := PredN.step (PredN.zero hV) hV j1
    have hOutW := hOut 1 _ one_pos hW1
    -- the `A`-Auslander–Reiten sequence starting at `res W`
    obtain ⟨c, hc⟩ : IsoM (resFD (D.qmap (Bset x (sd x) i0)) ((chosenMin V hV).d.obj j1)) K :=
      (hj1.res (φ := D.qmap (Bset x (sd x) i0))).symm.trans hK3iso.symm
    let W := resFD (D.qmap (Bset x (sd x) i0)) ((chosenMin V hV).d.obj j1)
    have hWA : IndNT W := (indNT_res_iff hφ _).2 hW1.indNT
    haveI : Nontrivial W := hWA.2
    haveI : IsLocalRing (Module.End A W) := hWA.1.isLocalRing (k := k)
    have hι : Function.Injective (FDMod.lin (c ≫ fK)) := hfKinj.comp hc.1
    have hιns : ¬∃ r : E ⟶ W, (c ≫ fK) ≫ r = 𝟙 W := by
      rintro ⟨r', hr'⟩
      refine hleft.1 ⟨r' ≫ c, (FDMod.hom_ext (LinearMap.ext fun kk ↦ ?_))⟩
      obtain ⟨w, rfl⟩ := hc.2 kk
      have := LinearMap.congr_fun (congrArg FDMod.lin hr') w
      change FDMod.lin r' (FDMod.lin fK (FDMod.lin c w)) = w at this
      change FDMod.lin c (FDMod.lin r' (FDMod.lin fK (FDMod.lin c w))) = FDMod.lin c w
      rw [this]
    obtain ⟨E2, f2, hf2L, hf2inj, hf2min, hg2R, hC2⟩ := exists_arSeqL W E (c ≫ fK) hι hιns
    obtain ⟨d2⟩ := FDMod.exists_decomp E2
    have hE2 : LivesOn (Bset x (sd x) i0) E2 := livesOn_of_decomp d2 fun j' ↦
      hOutW _ ⟨d2.indec j', d2.nt j'⟩ _ (isIrr_summandL hf2L hf2min hWA d2 j')
    have hC2l : LivesOn (Bset x (sd x) i0) (FDMod.ofQuot E2 (LinearMap.range (FDMod.lin f2))) :=
      livesOn_of_surj (show E2 ⟶ FDMod.ofQuot E2 (LinearMap.range (FDMod.lin f2)) from
        (FDMod.ofLin ((LinearMap.range (FDMod.lin f2)).mkQ))) (Submodule.mkQ_surjective _) hE2
    haveI : Nontrivial (FDMod.ofQuot E2 (LinearMap.range (FDMod.lin f2))) := hC2.2
    haveI : IsLocalRing (Module.End A (FDMod.ofQuot E2 (LinearMap.range (FDMod.lin f2)))) :=
      hC2.1.isLocalRing (k := k)
    have hexι : LinearMap.range (FDMod.lin (c ≫ fK)) = LinearMap.ker (FDMod.lin g) := by
      rw [← hexK]
      ext e
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨kk, rfl⟩
        obtain ⟨w, rfl⟩ := hc.2 kk
        exact ⟨w, rfl⟩
    have hiso := coker_iso_of_leftAS (g := (show E2 ⟶ FDMod.ofQuot E2
        (LinearMap.range (FDMod.lin f2)) from (FDMod.ofLin ((LinearMap.range (FDMod.lin f2)).mkQ))))
      hf2L hf2inj (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm
      (isLeftAS_iso_comp hleft c hc) hι hgs hexι
    exact livesOn_iso hiso hC2l

/-- **Bongartz's Lemma 2.4 (b).** Let `C` be a preprojective component over the quotient for
`B = Bᵢ(x)`, and `U₀ ∈ C` such that no proper predecessor of `U₀` restricts to `Rᵢ(x)`. Then for
every predecessor `V` of `U₀`, irreducible maps of `A`-modules into `V` start in `B`, and if `V`
does not restrict to `Rᵢ(x)`, irreducible maps out of `V` end in `B`. -/
theorem lemma24b (sd : ∀ z, Decomp (D.RadP z)) (hsd : ∀ z, z ∈ D.T → D.SepDecomp z (sd z))
    {x : D.ι} (i0 : (sd x).ι) {𝒞 : FDMod k (D.QAlg (Bset x (sd x) i0)) → Prop}
    (h𝒞 : PreprojComp 𝒞) {U₀ : FDMod k (D.QAlg (Bset x (sd x) i0))} (hU₀ : 𝒞 U₀)
    (habove : ∀ m V, 0 < m → PredN U₀ m V →
      ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0)) :
    ∀ n V, PredN U₀ n V → IrrIn (Bset x (sd x) i0) V ∧
      (¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0) →
        IrrOut (Bset x (sd x) i0) V) := by
  have hB := Bset_convex x (sd x) i0
  have hsucc : ∀ z, z ∈ Bset x (sd x) i0 →
      LivesOn (Bset x (sd x) i0) (projE (k := k) (D.idem z)) := fun z hz ↦
    livesOn_proj x (sd x) i0 hz
  have key := h𝒞.induction (fun V ↦ ∀ n, PredN U₀ n V → IrrIn (Bset x (sd x) i0) V ∧
      (¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0) →
        IrrOut (Bset x (sd x) i0) V)) (fun V hV ih n hn ↦ by
    have hVi := h𝒞.indNT V hV
    have hOut : ∀ m W, 0 < m → PredN V m W → IrrOut (Bset x (sd x) i0) W := fun m W hm hW ↦
      (ih m W hm hW (n + m) (hn.trans hW)).2 (habove (n + m) W (by omega) (hn.trans hW))
    have hIn := irrIn_step hB hsucc hVi hOut
    exact ⟨hIn, fun hR ↦ irrOut_step sd hsd i0 hVi hIn hOut hR⟩)
  exact fun n V hV ↦ key V (h𝒞.mem_of_predN hU₀ hV) n hV

end DirData

end LargeIndecomposable.AR
