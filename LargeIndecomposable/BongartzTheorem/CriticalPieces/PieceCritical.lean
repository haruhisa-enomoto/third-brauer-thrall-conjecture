module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.ExtCocycle
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalForm
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalConnected
public import LargeIndecomposable.DirectedAlgebras.Preprojective.CriticalQuotLine
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverLocalSCResidue
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullStage
public import LargeIndecomposable.Coverings.Pieces.PieceSepCover
/-!
# Critical pieces carry point–brick data

For a critical piece: all indecomposable projectives lie in the preprojective component
(`goodProj_piece`), because the points whose projective lies in it form an arrow-closed, hence
convex, set containing the support of the component. Then `AR.DirData.exists_pointBrick` gives
point–brick data on a minimal quotient. They inflate to the piece (`pointBrick'_critical`). This
proves `PointBrickData`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR.PreprojComp

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
include h𝒞

lemma mem_of_pred {X : FDMod k A} (hX : 𝒞 X) : ∀ {n : ℕ} {Y : FDMod k A}, PredN X n Y → 𝒞 Y := by
  intro n Y h
  induction h with
  | zero _ => exact hX
  | step _ _ i ih => exact h𝒞.pred_chosen _ ih i

/-- **Predecessor closure.** -/
lemma mem_of_hom {X N : FDMod k A} (hX : 𝒞 X) (hN : IsIndecMod A N) (f : N ⟶ X)
    (hf : FDMod.lin f ≠ 0) : 𝒞 N := by
  by_cases hb : Function.Bijective (FDMod.lin f)
  · exact h𝒞.iso X N hX ⟨invOf f hb, (LinearEquiv.ofBijective (FDMod.lin f) hb).symm.bijective⟩
  · obtain ⟨b, hb'⟩ := h𝒞.finPred X hX
    obtain ⟨m, -, Y, hY, hiso⟩ := iso_predN_of_hom hb' (PredN.zero (h𝒞.indNT X hX)) N hN f hf hb
    exact h𝒞.iso Y N (h𝒞.mem_of_pred hX hY) hiso.symm

/-- **Members of a preprojective component are good.** -/
lemma good {X : FDMod k A} (hX : 𝒞 X) : Good X := by
  refine ⟨h𝒞.indNT X hX, h𝒞.finIso X hX, fun n Y hY m Z hm hZ ↦ ?_⟩
  exact h𝒞.noCycle Y (h𝒞.mem_of_pred hX hY) m Z hm hZ

/-- A nonzero morphism `s → t` puts `P_t` before `P_s`. -/
lemma proj_succ (D : DirData k A) (s t : D.ι) (a : A) (ha : D.e t * a * D.e s ≠ 0)
    (hs : 𝒞 (projE (k := k) (D.idem s))) (hind : IsIndecMod A (projE (k := k) (D.idem t))) :
    𝒞 (projE (k := k) (D.idem t)) := by
  have hvr : (D.e t * a * D.e s) * D.e s = D.e t * a * D.e s := by
    rw [mul_assoc, D.e_mul_e]
  refine h𝒞.mem_of_hom hs hind (show _ ⟶ _ from (FDMod.ofLin (DirData.rmul t _ hvr))) fun h0 ↦ ha ?_
  have h1 := LinearMap.congr_fun h0 (DirData.genP (k := k) (D := D) t)
  have h2 := congrArg Subtype.val h1
  change D.e t * (D.e t * a * D.e s) = 0 at h2
  rwa [← mul_assoc, ← mul_assoc, D.e_mul_e] at h2

end LargeIndecomposable.AR.PreprojComp

namespace LargeIndecomposable.AR.DirData

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {D : DirData k A}

/-- On a module concentrated at `x`, the algebra acts through the character at `x`. -/
lemma smul_eq_chi {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {x : D.ι} (hx : x ∈ D.T) (h : ∀ m : M, D.e x • m = m) (a : A) (m : M) :
    a • m = D.chi x hx a • m := by
  classical
  have hy : ∀ y, y ≠ x → ∀ z : M, D.e y • z = 0 := fun y hy z ↦ by
    rw [← h z, ← mul_smul, D.orth y x hy, zero_smul]
  have h1 : a • m = ∑ y, D.e y • (a • m) := by
    rw [← Finset.sum_smul, D.sum, one_smul]
  rw [h1, Finset.sum_eq_single x (fun y _ hne ↦ hy y hne _) (by simp)]
  have h2 : D.e x • (a • m) = (D.e x * a * D.e x) • m := by
    rw [mul_smul, mul_smul, h m]
  rw [h2, D.chi_spec x hx, smul_assoc, h m]

end LargeIndecomposable.AR.DirData

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- Arrow-closed parts of convex sets, in the forward direction, are convex. -/
theorem convex_of_succ {C T : Set (Cover x₀)} (hC : Convex C) (hTC : T ⊆ C)
    (hcl : ∀ a b (f : a ⟶ b), IsIrreducible f → a ∈ C → b ∈ C → a ∈ T → b ∈ T) :
    Convex T := by
  intro a b c ha hc hab hbc
  induction hab with
  | refl => exact ha
  | step f hf hrest ih =>
    rename_i a' a'' b'
    have ha''C : a'' ∈ C :=
      hC a' a'' c (hTC ha) (hTC hc) (Reach.step f hf (Reach.refl _)) (reach_trans' hrest hbc)
    exact ih (hcl _ _ f hf (hTC ha) ha''C ha) hbc

lemma convex_ptsOf_succ {C : Finset (Cover x₀)} (hC : Convex (C : Set (Cover x₀)))
    (R : Set (pieceQuiver C).V)
    (hR : ∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ R → (pieceQuiver C).tgt α ∈ R) :
    Convex ((ptsOf R : Finset (Cover x₀)) : Set (Cover x₀)) :=
  convex_of_succ hC (fun c hc ↦ ptsOf_subset R hc) fun a b f hf ha hb h ↦
    (mem_ptsOf (⟨b, hb⟩ : (pieceQuiver C).V)).2
      (hR ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨f, hf⟩⟩ ((mem_ptsOf (⟨a, ha⟩ : (pieceQuiver C).V)).1 h))

/-- The corners of a piece have dimension at most one. -/
lemma cartan_piece_le_one (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A),
    l ≠ [] → ¬PathFrom i l i) (hpar : ParEq S) (x y : (pieceQuiver S).V) :
    AR.cartan (pieceDirData (k := k) hacyc) y x ≤ 1 := by
  classical
  let D := pieceDirData (k := k) hacyc
  by_cases hxy : y = x
  · subst hxy
    exact (AR.cartan_diag D (i := y) (Set.mem_univ _)).le
  let b : PieceAlg k S := pbvec x y
  have hsub : pmk (k := k) '' cornerSet k x y ⊆ {b} := by
    rintro _ ⟨r, (⟨h, rfl⟩ | ⟨l, hl, hp, rfl⟩), rfl⟩
    · exact absurd h.symm hxy
    · exact pmk_word_eq_bvec hpar hp
  let ξ : AR.eSub (AR.projE (k := k) (D.idem x)) (D.e y) →ₗ[k] PieceAlg k S :=
    { toFun := fun m ↦ ((m : AR.projE (k := k) (D.idem x)) : PieceAlg k S)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hξ : Function.Injective ξ := fun a b h ↦ Subtype.ext (Subtype.ext h)
  have hr : LinearMap.range ξ ≤ Submodule.span k {b} := by
    rintro _ ⟨m, rfl⟩
    have h1 := Submodule.span_mono hsub (corner_piece (k := k) ((m : AR.projE (k := k) (D.idem x)) :
      PieceAlg k S) x y)
    have h2 : pev (k := k) y * ((m : AR.projE (k := k) (D.idem x)) : PieceAlg k S) * pev x =
        ξ m := by
      have h3 : ((m : AR.projE (k := k) (D.idem x)) : PieceAlg k S) * pev x = _ :=
        (m : AR.projE (k := k) (D.idem x)).2
      rw [mul_assoc, h3]
      exact congrArg Subtype.val (show D.e y • (m : AR.projE (k := k) (D.idem x)) = m from m.2)
    rwa [h2] at h1
  have h1 : finrank k (AR.eSub (AR.projE (k := k) (D.idem x)) (D.e y)) ≤ 1 := by
    rw [← LinearMap.finrank_range_of_inj hξ]
    refine (Submodule.finrank_mono hr).trans ?_
    refine finrank_le_one (⟨b, Submodule.mem_span_singleton_self b⟩ : Submodule.span k {b})
      fun w ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 w.2
    exact ⟨c, Subtype.ext hc⟩
  change ((finrank k (AR.eSub (AR.projE (k := k) (D.idem x)) (D.e y)) : ℕ) : ℤ) ≤ 1
  exact_mod_cast h1

section Critical

variable [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
  (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
  (hlsc : CoverLocalSC x₀) (hrep : ¬PieceRepFin k S)
  (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < S.card →
    PieceRepFin k C')
include hS hne hacycCov hint hlsc hrep hmin

/-- **All indecomposable projectives of a critical piece are good.** -/
theorem goodProj_piece (x : (pieceQuiver S).V) :
    AR.Good (AR.projE (k := k) ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).idem x)) := by
  classical
  have hconnS := connected_of_critical (k := k) hS hrep hmin
  obtain ⟨𝒞, h𝒞⟩ := piece_preprojComp (k := k) hS hne hacycCov hint hlsc
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  let D := pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)
  have hunb := unbounded_of_not_pieceRepFin hS hne hacycCov hint hlsc hconnS hrep
  have hunb𝒞 := AR.PreprojComp.unbounded D.e D.idem D.sum
    (fun x ↦ D.projIndNT x (Set.mem_univ x))
    (fun T hT hcl ↦ hconnS T hT fun α ↦
      ⟨fun h ↦ hcl _ _ h (Or.inr (D.arrNe _ _ (parr_arrow hpar α))),
        fun h ↦ hcl _ _ h (Or.inl (D.arrNe _ _ (parr_arrow hpar α)))⟩) h𝒞 hunb
  let R : Set (pieceQuiver S).V := {x | 𝒞 (AR.projE (k := k) (D.idem x))}
  have hind : ∀ y, AR.IsIndecMod (PieceAlg k S) (AR.projE (k := k) (D.idem y)) := fun y ↦
    (D.projIndNT y (Set.mem_univ y)).1
  -- `R` is closed under arrows
  have hsucc : ∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ R → (pieceQuiver S).tgt α ∈ R := by
    intro α hα
    obtain ⟨a, ha⟩ := D.arrNe _ _ (parr_arrow hpar α)
    exact h𝒞.proj_succ D _ _ a ha hα (hind _)
  by_contra hno
  by_cases hall : ∀ y, y ∈ R
  · exact hno (h𝒞.good (hall x))
  push Not at hall
  obtain ⟨u, hu⟩ := hall
  have hlt : (ptsOf R).card < S.card := by
    refine Finset.card_lt_card ⟨ptsOf_subset R, fun h ↦ hu ?_⟩
    exact (mem_ptsOf u).1 (h (show S from u).2)
  obtain ⟨n, Y, hY⟩ := hmin _ (convex_ptsOf_succ hS R hsucc) hlt
  obtain ⟨M, hM, hMb⟩ := hunb𝒞 (Finset.univ.sup fun j ↦ finrank k (pickRep R (Y j)).Tot)
  have hMi := h𝒞.indNT M hM
  have hsupp : SuppIn (ptsOf R) (repOf M) := by
    intro s hs
    refine ⟨fun a b ↦ ?_⟩
    have hsR : s ∉ R := fun h ↦ hs ((mem_ptsOf s).2 h)
    have h0 : ∀ m : (repOf M).obj s, m = 0 := by
      intro m
      by_contra hm
      apply hsR
      have h1 : pev (k := k) s • val M m ≠ 0 := by
        rw [ev_smul_val]
        exact fun h ↦ hm (val_injective M h)
      obtain ⟨f, hf⟩ := AR.exists_proj_hom_ne' D h1
      exact h𝒞.mem_of_hom hM (hind s) f hf
    rw [h0 a, h0 b]
  have hX := respectsCover_repOf M
  obtain ⟨j, ⟨φ⟩⟩ := hY _ inferInstance (respectsCover_resP (ptsOf_subset R) (repOf M) hX)
    (isIndec_resP (ptsOf_subset R) hsupp (isIndec_repOf M hMi))
  obtain ⟨ψ⟩ := iso_pickRep R (Y j) (fun i ↦ inferInstance) hsupp φ
  have h1 : finrank k M = finrank k (pickRep R (Y j)).Tot := by
    rw [← (totEquiv M).finrank_eq, (totEquivOfIso ψ).finrank_eq]
  have h2 := Finset.le_sup (f := fun j ↦ finrank k (pickRep R (Y j)).Tot) (Finset.mem_univ j)
  omega

/-- **A critical piece has unbounded indecomposables on the trivial quotient.** -/
theorem unb_piece :
    (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).Unb Set.univ := by
  intro b
  have hconnS := connected_of_critical (k := k) hS hrep hmin
  obtain ⟨N, hN, hb⟩ := unbounded_of_not_pieceRepFin hS hne hacycCov hint hlsc hconnS hrep b
  have hl : AR.DirData.LivesOn (D := pieceDirData (k := k) (piece_acyclic (S := S) hacycCov))
      Set.univ N := fun v hv ↦ absurd (Set.mem_univ v) hv
  refine ⟨AR.DirData.descendQ N hl, ?_, hb⟩
  exact (AR.indNT_res_iff (AR.DirData.qmap_surjective _ _) _).1
    (AR.DirData.indNT_of_iso (AR.DirData.isoM_descend' N hl) hN)

end Critical

/-- **Extension classes of modules give data on the piece.** -/
theorem two_le_relSub_mod {Km Pm Xm Ym : AR.FDMod k (PieceAlg k S)}
    (f : Km →ₗ[PieceAlg k S] Pm) (g : Pm →ₗ[PieceAlg k S] Xm)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) {X Y : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) (hY : RespectsCover Y) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)]
    (eX : PieceMod X hX ≃ₗ[PieceAlg k S] Xm) (eY : PieceMod Y hY ≃ₗ[PieceAlg k S] Ym)
    (hd : finrank k (LinearMap.range (AR.precomp (A := PieceAlg k S) k (Y := Ym) f)) + 2 ≤
      finrank k (Km →ₗ[PieceAlg k S] Ym)) :
    2 ≤ finrank k (relSub X Y) := by
  classical
  let Kr := repOf Km
  let Pr := repOf Pm
  have hK : RespectsCover Kr := respectsCover_repOf Km
  have hP : RespectsCover Pr := respectsCover_repOf Pm
  let eK : PieceMod Kr hK ≃ₗ[PieceAlg k S] Km := repOfEquivA Km
  let eP : PieceMod Pr hP ≃ₗ[PieceAlg k S] Pm := repOfEquivA Pm
  let sK : PieceMod Kr hK →ₗ[PieceAlg k S] PieceMod Pr hP := eP.symm.toLinearMap ∘ₗ f ∘ₗ eK.toLinearMap
  let sP : PieceMod Pr hP →ₗ[PieceAlg k S] PieceMod X hX := eX.symm.toLinearMap ∘ₗ g ∘ₗ eP.toLinearMap
  let ι : Kr ⟶ Pr := homOfLin sK
  let π : Pr ⟶ X := homOfLin sP
  have hιt : ∀ x, ι.tot x = sK x := homOfLin_tot sK
  have hπt : ∀ x, π.tot x = sP x := homOfLin_tot sP
  have hE : Ext.VExact ι π := by
    refine vExact_of_tot ι π ?_ ?_ ?_
    · intro a b hab
      rw [hιt, hιt] at hab
      exact eK.injective (hf (eP.symm.injective hab))
    · intro y
      obtain ⟨p, hp⟩ := hg (eX y)
      refine ⟨eP.symm p, (hπt _).trans ?_⟩
      change eX.symm (g (eP (eP.symm p))) = y
      rw [LinearEquiv.apply_symm_apply, hp]
      exact eX.symm_apply_apply y
    · intro p
      constructor
      · intro hp
        rw [hπt] at hp
        have h1 : g (eP p) = 0 := by
          have h2 : eX.symm (g (eP p)) = 0 := hp
          have h3 := congrArg eX h2
          rw [LinearEquiv.apply_symm_apply, map_zero] at h3
          exact h3
        have h4 : eP p ∈ LinearMap.range f := by
          rw [hex]
          exact h1
        obtain ⟨c, hc⟩ := h4
        refine ⟨eK.symm c, (hιt _).trans ?_⟩
        change eP.symm (f (eK (eK.symm c))) = p
        rw [LinearEquiv.apply_symm_apply, hc]
        exact eP.symm_apply_apply p
      · rintro ⟨x, rfl⟩
        refine (hπt _).trans ((congrArg sP (hιt x)).trans ?_)
        change eX.symm (g (eP (eP.symm (f (eK x))))) = 0
        rw [LinearEquiv.apply_symm_apply, AR.mem_ker_of_range hex, map_zero]
  let sE : (Km →ₗ[PieceAlg k S] Ym) → (PieceMod Kr hK →ₗ[PieceAlg k S] PieceMod Y hY) := fun e ↦
    eY.symm.toLinearMap ∘ₗ e ∘ₗ eK.toLinearMap
  let Φ : (Km →ₗ[PieceAlg k S] Ym) → (Kr ⟶ Y) := fun e ↦ homOfLin (sE e)
  let Φi : ∀ i, (Km →ₗ[PieceAlg k S] Ym) →ₗ[k] (Kr.obj i →ₗ[k] Y.obj i) := fun i ↦
    { toFun := fun e ↦
        { toFun := fun x ↦ (show Y.Tot from sE e (show Kr.Tot from Pi.single i x)) i
          map_add' := fun a b ↦ by
            have h0 : (Pi.single i (a + b) : Kr.Tot) = Pi.single i a + Pi.single i b :=
              map_add (LinearMap.single k (fun j ↦ Kr.obj j) i) a b
            rw [h0]
            exact congrFun (map_add (sE e) (show Kr.Tot from Pi.single i a)
              (show Kr.Tot from Pi.single i b)) i
          map_smul' := fun c a ↦ by
            have h0 : (Pi.single i (c • a) : Kr.Tot) = c • Pi.single i a :=
              map_smul (LinearMap.single k (fun j ↦ Kr.obj j) i) c a
            rw [h0]
            exact congrFun (LinearMap.map_smul_of_tower (sE e) c
              (show Kr.Tot from Pi.single i a)) i }
      map_add' := fun a b ↦ LinearMap.ext fun x ↦
        congrFun (map_add eY.symm (a (eK (show Kr.Tot from Pi.single i x)))
          (b (eK (show Kr.Tot from Pi.single i x)))) i
      map_smul' := fun c a ↦ LinearMap.ext fun x ↦
        congrFun (LinearMap.map_smul_of_tower eY.symm.toLinearMap c
          (a (eK (show Kr.Tot from Pi.single i x)))) i }
  have hΦ : ∀ e i, ((Φ e).app i).hom = Φi i e := fun e i ↦ LinearMap.ext fun x ↦ rfl
  haveI : FiniteDimensional k (Km →ₗ[PieceAlg k S] Ym) :=
    AR.finiteDimensional_hom (k := k) (A := PieceAlg k S) (L := Km) (M := Ym)
  refine two_le_relSub hX hP hE Φ Φi hΦ (LinearMap.range (AR.precomp (A := PieceAlg k S) k (Y := Ym) f)) ?_ hd
  rintro e ⟨ψ, hψ⟩
  let ψA : PieceMod Pr hP →ₗ[PieceAlg k S] PieceMod Y hY :=
    { toFun := ψ.tot
      map_add' := map_add ψ.tot
      map_smul' := fun a x ↦ LinearMap.congr_fun (tot_comp_pieceAct hP hY ψ a) x }
  let ψB : Pm →ₗ[PieceAlg k S] Ym := eY.toLinearMap ∘ₗ ψA ∘ₗ eP.symm.toLinearMap
  refine ⟨ψB, LinearMap.ext fun c ↦ ?_⟩
  let x : PieceMod Kr hK := eK.symm c
  have h1 : ι.tot x = eP.symm (f c) := by
    refine (hιt _).trans ?_
    change eP.symm (f (eK (eK.symm c))) = _
    rw [LinearEquiv.apply_symm_apply]
  have h2 : ψ.tot (ι.tot x) = (Φ e).tot x := by
    rw [← hψ, Rep.Hom.tot_comp]
    rfl
  have h3 : (Φ e).tot x = eY.symm (e c) := by
    refine (homOfLin_tot (sE e) x).trans ?_
    change eY.symm (e (eK (eK.symm c))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [h1] at h2
  change eY (ψ.tot (eP.symm (f c))) = e c
  rw [h2, h3, LinearEquiv.apply_symm_apply]

/-- **The point representation is the one-dimensional module at the point.** -/
theorem exists_point_equiv (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A),
    l ≠ [] → ¬PathFrom i l i) (x : (pieceQuiver S).V) (Sm : AR.FDMod k (PieceAlg k S))
    (hx : ∀ m : Sm, pev (k := k) x • m = m) (h1 : finrank k Sm = 1) :
    Nonempty (PieceMod (Rep.pointRep (k := k) x) (respectsCover_pointRep x) ≃ₗ[PieceAlg k S] Sm) := by
  classical
  let D := pieceDirData (k := k) hacyc
  let Y := Rep.pointRep (k := k) x
  have hY : RespectsCover Y := respectsCover_pointRep x
  obtain ⟨s₀, hs₀, hs⟩ := finrank_eq_one_iff'.1 h1
  have hn : (0 : ℕ) < @ite ℕ (x = x) ((pieceQuiver S).decV x x) 1 0 := by simp
  let i₀ : Fin (@ite ℕ (x = x) ((pieceQuiver S).decV x x) 1 0) := ⟨0, hn⟩
  let cd : Y.Tot →ₗ[k] k :=
    { toFun := fun y ↦ (show Fin (@ite ℕ (x = x) ((pieceQuiver S).decV x x) 1 0) → k from y x) i₀
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hcd : ∀ y : Y.Tot, cd y = 0 → y = 0 := by
    intro y hy
    funext i
    by_cases hi : i = x
    · subst hi
      refine funext fun j ↦ ?_
      have hj : j = i₀ := by
        apply Fin.ext
        have := j.2
        simp at this
        change j.1 = 0
        omega
      rw [hj]
      exact hy
    · refine funext fun j ↦ ?_
      have := j.2
      simp [hi] at this
  have hall : ∀ y : PieceMod Y hY, D.e x • y = y := by
    intro y
    change (show Y.Tot →ₗ[k] Y.Tot from pieceAct Y hY (pev x)) (show Y.Tot from y) = y
    rw [pieceAct_pev]
    funext i
    rw [Rep.idm_apply]
    by_cases hi : i = x
    · subst hi
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi]
      refine funext fun j ↦ ?_
      have := j.2
      simp [hi] at this
  let L : PieceMod Y hY →ₗ[PieceAlg k S] Sm :=
    { toFun := fun y ↦ cd y • s₀
      map_add' := fun a b ↦ by
        have h : cd (show Y.Tot from a + b) = cd (show Y.Tot from a) + cd (show Y.Tot from b) :=
          map_add cd (show Y.Tot from a) (show Y.Tot from b)
        change cd (show Y.Tot from a + b) • s₀ =
          cd (show Y.Tot from a) • s₀ + cd (show Y.Tot from b) • s₀
        rw [h, add_smul]
      map_smul' := fun a y ↦ by
        have hsm := AR.DirData.smul_eq_chi (D := D) (x := x) (Set.mem_univ x) hall a y
        have e2 := AR.DirData.smul_eq_chi (D := D) (x := x) (Set.mem_univ x) hx a s₀
        have e1 : cd (show Y.Tot from a • y) =
            D.chi x (Set.mem_univ x) a * cd (show Y.Tot from y) := by
          rw [show (show Y.Tot from a • y) = D.chi x (Set.mem_univ x) a • (show Y.Tot from y) from hsm]
          exact map_smul cd _ _
        change cd (show Y.Tot from a • y) • s₀ = a • (cd (show Y.Tot from y) • s₀)
        have e3 : a • (cd (show Y.Tot from y) • s₀) = cd (show Y.Tot from y) • (a • s₀) :=
          map_smul (actK Sm a) (cd (show Y.Tot from y)) s₀
        rw [e1, e3, e2, mul_smul, smul_comm] }
  refine ⟨LinearEquiv.ofBijective L ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_, fun w ↦ ?_⟩⟩
  · have h2 : cd y • s₀ = 0 := hy
    exact hcd y ((smul_eq_zero.1 h2).resolve_right hs₀)
  · obtain ⟨c, hc⟩ := hs w
    let y : Y.Tot := Pi.single x (fun _ ↦ c)
    refine ⟨y, ?_⟩
    have h3 : cd y = c := by
      change (show Fin (@ite ℕ (x = x) ((pieceQuiver S).decV x x) 1 0) → k from y x) i₀ = c
      have h4 : y x = fun _ ↦ c := Pi.single_eq_same (M := fun i ↦ Y.obj i) x _
      rw [h4]
    change cd y • s₀ = w
    rw [h3, hc]

/-- **Point–brick data over the piece algebra living on `T'` give point–brick data on the
piece living on `T'`.** -/
theorem pointBrickAt_of_in [IsAlgClosed k] (hacyc : ∀ (i : (pieceQuiver S).V)
    (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i) {T' : Set (pieceQuiver S).V}
    (h : (pieceDirData (k := k) hacyc).PointBrickAIn T') :
    ∃ (x : (pieceQuiver S).V) (Vr : Rep k (pieceQuiver S)), PointBrickAt (k := k) x Vr ∧
      x ∈ T' ∧ ∀ i, Nontrivial (Vr.obj i) → i ∈ T' := by
  classical
  let D := pieceDirData (k := k) hacyc
  obtain ⟨x, hxT, V, hV0, Sm, K, Pm, f, hb, hnt, hVk, hSx, hS1, hf, hext⟩ := h
  refine ⟨x, repOf V, ?_, hxT, fun i hi ↦ ?_⟩
  swap
  · by_contra hiT
    obtain ⟨a, b, hab⟩ := hi
    apply hab
    apply val_injective V
    rw [← ev_smul_val V a, ← ev_smul_val V b]
    exact (hV0 i hiT _).trans (hV0 i hiT _).symm
  let Vr := repOf V
  have hVc : RespectsCover Vr := respectsCover_repOf V
  let eV : PieceMod Vr hVc ≃ₗ[PieceAlg k S] V := repOfEquivA V
  have finV : ∀ i, FiniteDimensional k (Vr.obj i) := fun i ↦ inferInstance
  have hVx : Subsingleton (Vr.obj x) := by
    refine ⟨fun a b ↦ ?_⟩
    have h0 : ∀ m : Vr.obj x, m = 0 := fun m ↦ by
      apply val_injective V
      rw [← ev_smul_val V m]
      exact hVk _
    rw [h0 a, h0 b]
  have brickV : ∀ φ : Vr ⟶ Vr, ∃ c : k, ∀ i, (φ.app i).hom = c • LinearMap.id := by
    intro φ
    let φA : PieceMod Vr hVc →ₗ[PieceAlg k S] PieceMod Vr hVc :=
      { toFun := φ.tot
        map_add' := map_add φ.tot
        map_smul' := fun a x ↦ LinearMap.congr_fun (tot_comp_pieceAct hVc hVc φ a) x }
    let φM : V →ₗ[PieceAlg k S] V := eV.toLinearMap ∘ₗ φA ∘ₗ eV.symm.toLinearMap
    obtain ⟨c, hc⟩ := hb (show V ⟶ V from (AR.FDMod.ofLin φM))
    refine ⟨c, fun i ↦ LinearMap.ext fun v ↦ ?_⟩
    have h1 : ∀ y : PieceMod Vr hVc, φ.tot y = c • y := fun y ↦ by
      apply eV.injective
      have h2 := LinearMap.congr_fun hc (eV y)
      change eV (φ.tot (eV.symm (eV y))) = c • eV y at h2
      rw [LinearEquiv.symm_apply_apply] at h2
      rw [h2]
      exact (LinearMap.map_smul_of_tower eV.toLinearMap c y).symm
    have h3 := congrFun (h1 (show Vr.Tot from Pi.single i v)) i
    rw [Rep.Hom.tot_apply, Pi.single_eq_same] at h3
    refine h3.trans ?_
    change c • (Pi.single i v : Vr.Tot) i = _
    rw [Pi.single_eq_same]
    rfl
  have hV : ∃ i, Nontrivial (Vr.obj i) :=
    (isIndec_repOf V ⟨AR.isIndecMod_of_brick hb, hnt⟩).1
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨eS⟩ := exists_point_equiv hacyc x Sm hSx hS1
  rcases hext with ⟨g, hg, hex, hd⟩ | ⟨g, hg, hex, hd⟩
  · exact pointBrickAt_of_rel x Vr finV hVx brickV hV hVc
      (two_le_relSub_mod f g hf hg hex hVc (respectsCover_pointRep x) eV eS hd)
  · exact pointBrickAt_of_rel_source x Vr finV hVx brickV hV hVc
      (two_le_relSub_mod f g hf hg hex (respectsCover_pointRep x) hVc eS eV hd)


section Final

variable [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
  (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
  (hlsc : CoverLocalSC x₀) (hrep : ¬PieceRepFin k S)
  (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < S.card →
    PieceRepFin k C')
include hS hne hacycCov hint hlsc hrep hmin

/-- **Critical pieces carry point–brick data.** -/
theorem pointBrick'_critical : PointBrick' (k := k) S := by
  classical
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  obtain ⟨T', hT', h⟩ := AR.DirData.exists_pointBrick (D := D) (fun _ ↦ Set.mem_univ _)
      (fun x y ↦ cartan_piece_le_one hacyc hpar x y)
      (goodProj_piece hS hne hacycCov hint hlsc hrep hmin)
      (unb_piece hS hne hacycCov hint hlsc hrep hmin)
  obtain ⟨x, Vr, h, -⟩ := pointBrickAt_of_in hacyc (AR.DirData.pointBrickAIn_of_quot hT' h)
  exact ⟨x, Vr, h⟩

end Final

lemma nonempty_of_not_repFin (hrep : ¬PieceRepFin k S) : S.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  refine hrep ⟨0, Fin.elim0, fun X _ _ hind ↦ ?_⟩
  obtain ⟨⟨s, -⟩, -⟩ := hind
  exact absurd (show (∅ : Finset (Cover x₀)) from s).2 (by simp)

/-- **`PointBrickData` holds.** No tilting, tubes or classification tables are used. -/
theorem pointBrickData : PointBrickData.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf C hC hrep hmin
  exact ⟨C, hC, pointBrick'_critical hC (nonempty_of_not_repFin hrep)
    (coverIsAcyclic k B ι S hB hd x₀)
    (intervalFinite_of_hull (intervalFiniteCover k B ι S hB hd e x₀ htf))
    (coverLocallySimplyConnected k B ι S hB hd x₀) hrep hmin⟩

end LargeIndecomposable.RayCat
