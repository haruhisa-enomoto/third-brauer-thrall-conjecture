module

public import LargeIndecomposable.BongartzTheorem.Reduction.CoverDichotomy
public import LargeIndecomposable.Coverings.GradedModules.GradedCount
public import LargeIndecomposable.RayCategories.Basic.Balls

/-!
# Gabriel's covering theorem for pieces of the cover

If every finite set of objects of the universal cover lies in a finite convex piece
(interval-finiteness), every finite convex piece is representation-finite, the fundamental
group is torsion-free, and the graded-indecomposable `k(P)`-modules have supports of bounded
size, then `k(P)` is representation-finite (`repFin_of_bounded_support`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}
variable {k : Type u} [Field k]

/-- Path operators are conjugated by isomorphisms of representations. -/
lemma pathTot_iso {D : FinQuiver} {X Y : Rep k D} (φ : X ≅ Y) :
    ∀ le : List D.A, Y.pathTot le = φ.hom.tot ∘ₗ X.pathTot le ∘ₗ φ.inv.tot
  | [] => by
    simp only [Rep.pathTot, LinearMap.id_comp]
    rw [← Rep.Hom.tot_comp, φ.inv_hom_id, Rep.Hom.tot_id]
  | e :: le => by
    simp only [Rep.pathTot]
    rw [pathTot_iso φ le]
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 2
    have h1 := LinearMap.congr_fun (Rep.Hom.tot_comp_arrOp φ.inv e) x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h1
    rw [h1]

/-- `RespectsCover` passes along isomorphisms. -/
lemma respectsCover_of_iso {S : Finset (Cover x₀)} {X Y : Rep k (pieceQuiver S)} (φ : X ≅ Y)
    (hX : RespectsCover X) : RespectsCover Y := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rw [pathTot_iso φ, hX.1 le i j h h0]; simp
  · rw [pathTot_iso φ, pathTot_iso φ, hX.2 le le' i j h h' he]

/-- Finite dimension passes along isomorphisms. -/
lemma finiteDimensional_of_iso {D : FinQuiver} {X Y : Rep k D} (φ : X ≅ Y)
    [∀ i, FiniteDimensional k (X.obj i)] (i : D.V) : FiniteDimensional k (Y.obj i) :=
  LinearEquiv.finiteDimensional
    { toFun := (φ.hom.app i).hom
      invFun := (φ.inv.app i).hom
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun x ↦ by
        have := congrArg (fun f ↦ (Rep.Hom.app f i).hom x) φ.hom_inv_id
        simp only [Rep.comp_app, Rep.id_app, ModuleCat.hom_comp, ModuleCat.hom_id,
          LinearMap.comp_apply, LinearMap.id_apply] at this
        exact this
      right_inv := fun y ↦ by
        have := congrArg (fun f ↦ (Rep.Hom.app f i).hom y) φ.inv_hom_id
        simp only [Rep.comp_app, Rep.id_app, ModuleCat.hom_comp, ModuleCat.hom_id,
          LinearMap.comp_apply, LinearMap.id_apply] at this
        exact this }

variable (x₀) in
/-- Every finite set of objects of the cover lies in a finite convex piece. -/
def HullFinite : Prop :=
  ∀ T : Finset (Cover x₀), ∃ S : Finset (Cover x₀), T ⊆ S ∧ Convex (S : Set (Cover x₀))

variable {ℓ : ∀ y : P, vtx x₀ ⟶ vtx y}

lemma mem_suppSet_of_W {M : Type u} [AddCommGroup M] [Module (Linearization P k) M]
    [Module k M] [IsScalarTower k (Linearization P k) M] {μ : GrMod (rayGrAlg ℓ k) M}
    {a : Cover x₀} (ha : W ℓ k μ a ≠ ⊥) : a ∈ suppSet ℓ k μ := by
  by_contra h
  apply ha
  rw [eq_bot_iff]
  intro w hw
  have h1 := projW_of_mem ℓ k μ (a := a) hw
  rw [if_pos rfl, projW_eq_zero_of_not_mem ℓ k μ h] at h1
  exact (Submodule.mem_bot k).2 h1.symm

lemma W_shift {M : Type u} [AddCommGroup M] [Module (Linearization P k) M]
    [Module k M] [IsScalarTower k (Linearization P k) M] (μ : GrMod (rayGrAlg ℓ k) M)
    (a : Cover x₀) : W ℓ k (μ.shift (gOf ℓ a)) (cov ℓ a.y 1) = W ℓ k μ a := by
  ext m
  change (morElt k (𝟙 a.y) • m = m ∧ μ.Mem (gOf ℓ (cov ℓ a.y 1) * gOf ℓ a) m) ↔
    (morElt k (𝟙 a.y) • m = m ∧ μ.Mem (gOf ℓ a) m)
  rw [gOf_cov, one_mul]

variable (k ℓ) in
/-- The support of a graded module, as a finite set. -/
def suppF {M : Type u} [AddCommGroup M] [Module (Linearization P k) M]
    [Module k M] [IsScalarTower k (Linearization P k) M] (μ : GrMod (rayGrAlg ℓ k) M) :
    Finset (Cover x₀) :=
  (suppSet ℓ k μ).filter fun a ↦ W ℓ k μ a ≠ ⊥

/-- **Consequence of Gabriel's covering theorem.** Interval-finiteness, representation-finite convex pieces, a
torsion-free fundamental group and graded-indecomposables of bounded support make `k(P)`
representation-finite. -/
theorem repFin_of_bounded_support (htf : TorsionFree (Pi1 x₀)) (hIF : HullFinite x₀)
    (hpiece : ∀ S : Finset (Cover x₀), Convex (S : Set (Cover x₀)) → PieceRepFin k S)
    (n : ℕ) (hbd : ∀ (M : FDMod k (Linearization P k)) (μ : GrMod (rayGrAlg ℓ k) M),
      IsGrIndec μ → Nontrivial M → (suppF k ℓ μ).card ≤ n) :
    ∃ (r : ℕ) (Y : Fin r → FDMod k (Linearization P k)), ∀ N : FDMod k (Linearization P k),
      IsIndecMod (Linearization P k) N → Nontrivial N →
        ∃ j, ∃ f : Y j →ₗ[Linearization P k] N, Function.Bijective f := by
  classical
  -- the finite family of connected supports through the fundamental domain
  let F : Finset (Cover x₀) := Finset.univ.image fun y ↦ cov ℓ y 1
  have h𝒯 : (⋃ f ∈ F, {S : Finset (Cover x₀) | f ∈ S ∧ S.card ≤ n ∧ IsConnSet S}).Finite :=
    F.finite_toSet.biUnion fun f _ ↦ finite_connSets f n
  let 𝒯 := h𝒯.toFinset
  -- hulls and their representation lists
  choose hull hsub hconv using hIF
  choose r Yr hYr using fun T : Finset (Cover x₀) ↦ hpiece (hull T) (hconv T)
  let zeroObj : FDMod k (Linearization P k) := FDMod.ofSub (P := DAobj k (Linearization P k)) ⊥
  let obj : (Σ T : 𝒯, Fin (r T.1)) → FDMod k (Linearization P k) := fun p ↦
    if h : RespectsCover (Yr p.1.1 p.2) ∧ ∀ i, FiniteDimensional k ((Yr p.1.1 p.2).obj i) then
      haveI := h.2
      pdMod (hconv p.1.1) (Yr p.1.1 p.2) h.1
    else zeroObj
  let e := Fintype.equivFin (Σ T : 𝒯, Fin (r T.1))
  -- every graded-indecomposable is one of the listed push-downs
  have hcover : ∀ X : FDMod k (Linearization P k), GrInd (rayGrAlg ℓ k) X →
      ∃ j, ∃ f : obj (e.symm j) →ₗ[Linearization P k] X, Function.Bijective f := by
    intro X hX
    obtain ⟨γ, hγ, hXnt⟩ := hX
    -- a point of the support
    obtain ⟨a, ha⟩ : ∃ a, W ℓ k γ a ≠ ⊥ := by
      by_contra hall
      push Not at hall
      obtain ⟨m, hm⟩ := exists_ne (0 : X)
      apply hm
      rw [← sum_projW ℓ k γ m]
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      have := projW_mem ℓ k γ a m
      rw [hall a] at this
      exact (Submodule.mem_bot k).1 this
    -- shift so that the point lies over the fundamental domain
    set γ' := γ.shift (gOf ℓ a)
    have hγ' : IsGrIndec γ' := hγ.shift _
    have ha' : W ℓ k γ' (cov ℓ a.y 1) ≠ ⊥ := by rw [W_shift]; exact ha
    set T := suppF k ℓ γ'
    have haT : cov ℓ a.y 1 ∈ T := Finset.mem_filter.2 ⟨mem_suppSet_of_W ha', ha'⟩
    have hTconn : IsConnSet T := by
      intro U hU
      rcases suppC_connected k hγ' U (fun b c hb hc hbc ↦ hU b c hb
        (Finset.mem_filter.2 ⟨mem_suppSet_of_W hc, hc⟩) hbc) with h | h
      · exact Or.inl fun b hb ↦ h b (Finset.mem_filter.1 hb).2
      · exact Or.inr fun b hb ↦ h b (Finset.mem_filter.1 hb).2
    have hT𝒯 : T ∈ 𝒯 := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image.2 ⟨a.y, Finset.mem_univ _, rfl⟩))
        ⟨haT, hbd X γ' hγ' hXnt, hTconn⟩
    -- the piece representation
    set S := hull T
    have hS : ∀ b, W ℓ k γ' b ≠ ⊥ → b ∈ S := fun b hb ↦
      hsub T (Finset.mem_filter.2 ⟨mem_suppSet_of_W hb, hb⟩)
    haveI : ∀ i, FiniteDimensional k ((grRep ℓ k γ' S).obj i) := fun i ↦
      inferInstanceAs (FiniteDimensional k (W ℓ k γ' _))
    have hind : (grRep ℓ k γ' S).IsIndec := by
      refine ⟨⟨⟨cov ℓ a.y 1, hS _ ha'⟩, ?_⟩, fun φ hφ ↦ grRep_idem k hS hγ' φ hφ⟩
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha'
      exact ⟨⟨⟨w, hw⟩, 0, fun h ↦ hw0 (congrArg Subtype.val h)⟩⟩
    obtain ⟨jT, ⟨φ⟩⟩ := hYr T (grRep ℓ k γ' S) (fun i ↦ inferInstance) respectsCover_grRep hind
    have hY : RespectsCover (Yr T jT) := respectsCover_of_iso φ respectsCover_grRep
    haveI hYf : ∀ i, FiniteDimensional k ((Yr T jT).obj i) := finiteDimensional_of_iso φ
    obtain ⟨g, hg⟩ := exists_bijective_pdMod k hS (hconv T) (Yr T jT) hY φ
    refine ⟨e ⟨⟨T, hT𝒯⟩, jT⟩, ?_⟩
    have hobj : obj (e.symm (e ⟨⟨T, hT𝒯⟩, jT⟩)) = pdMod (hconv T) (Yr T jT) hY := by
      rw [Equiv.symm_apply_apply]
      simp only [obj, dif_pos (show RespectsCover (Yr T jT) ∧ _ from ⟨hY, hYf⟩)]
    rw [hobj]
    let geq := LinearEquiv.ofBijective g hg
    exact ⟨geq.symm.toLinearMap, geq.symm.bijective⟩

  exact ⟨Fintype.card (Σ T : 𝒯, Fin (r T.1)), fun j ↦ obj (e.symm j), fun N hN hNnt ↦
    gabriel_density (Γ := rayGrAlg ℓ k) htf (rayGrRadHyp k ℓ) (fun j ↦ obj (e.symm j)) hcover N hN⟩

end LargeIndecomposable.RayCat

namespace LargeIndecomposable.AR

open CategoryTheory

universe w

/-- **From `FDMod` lists to representation-finiteness.** -/
theorem isRepresentationFinite_of_fdList {k A : Type w} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] {r : ℕ} (Y : Fin r → FDMod k A)
    (hY : ∀ N : FDMod k A, IsIndecMod A N → Nontrivial N →
      ∃ j, ∃ f : Y j →ₗ[A] N, Function.Bijective f) :
    Statement.IsRepresentationFinite A := by
  refine ⟨r, fun j ↦ ModuleCat.of A (Y j), fun M _ _ _ hM ↦ ?_⟩
  letI : Module k M := Module.compHom M (algebraMap k A)
  haveI : IsScalarTower k A M := ⟨fun c a m ↦ by
    change (c • a) • m = algebraMap k A c • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : FiniteDimensional k M := Module.Finite.trans A M
  let N : FDMod k A := FDMod.mk M
  obtain ⟨j, f, hf⟩ := hY N hM.2 hM.1
  exact ⟨j, ⟨(LinearEquiv.ofBijective f hf).symm⟩⟩

end LargeIndecomposable.AR
