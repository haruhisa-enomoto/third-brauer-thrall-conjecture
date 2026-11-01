module

public import LargeIndecomposable.Coverings.GradedModules.GradedPieceTot

/-!
# The push-down of `grRep` is the graded module

`totToM` intertwines the push-down action of the path algebra with the action of `k(P)`
through `linPres` (`totToM_pdAct`). For a convex piece `S` containing all cover objects
carrying `M`, it is an isomorphism of `k(P)`-modules from the push-down `pdMod` of `grRep`
onto `M` (`pdModEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}
variable (k : Type u) [Field k]

lemma linPres_vertex (q : P) : linPres P k (vertex k (quiver P) q) = morElt k (𝟙 q) := by
  rw [morElt, dif_neg (IsRayCategory.id_ne_zero q), rayElt, dif_pos (IsIso.id q)]

lemma linPres_arrow (c : (quiver P).A) : linPres P k (arrow k (quiver P) c) = arrElt k c := by
  obtain ⟨x, y, f, hf⟩ := c
  have h : PathFrom (D := quiver P) x [⟨x, y, f, hf⟩] y := ⟨rfl, rfl⟩
  have hpm : pathMor [⟨x, y, f, hf⟩] x y h = f := by
    change eqToHom rfl ≫ f ≫ eqToHom rfl = f
    simp
  have h0 : pathMor [⟨x, y, f, hf⟩] x y h ≠ 0 := fun h' ↦ hf.1 (hpm ▸ h')
  have := linPres_word k ⟨x, y, f, hf⟩ [] x y h h0
  rw [show word k (quiver P) [⟨x, y, f, hf⟩] = arrow k (quiver P) ⟨x, y, f, hf⟩ by
    simp [word]] at this
  rw [this]
  change _ = morElt k f
  rw [morElt, dif_neg hf.1]
  congr 1
  exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext hpm))))

variable {ℓ : ∀ y : P, vtx x₀ ⟶ vtx y}
variable {M : Type u} [AddCommGroup M] [Module (Linearization P k) M] [Module k M]
  [IsScalarTower k (Linearization P k) M] {μ : GrMod (rayGrAlg ℓ k) M} {S : Finset (Cover x₀)}

/-- **`totToM` intertwines the path algebra actions.** -/
lemma totToM_pdAct (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (z : (quiver P).PathAlgebra k)
    (x : (grRep ℓ k μ S).Tot) :
    totToM ℓ k μ S ((grRep ℓ k μ S).pdAct (pieceProj S) z x) =
      linPres P k z • totToM ℓ k μ S x := by
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective k (FinQuiver.PathRel k (quiver P)) z
  induction w using FreeAlgebra.induction generalizing x with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    rw [AlgHom.commutes, algebraMap_smul]
  | grade1 g =>
    rcases g with q | c
    · have h1 := Rep.pdAct_vertex (pieceProj S) (grRep ℓ k μ S) q
      change totToM ℓ k μ S ((grRep ℓ k μ S).pdAct (pieceProj S) (vertex k (quiver P) q) x) =
        linPres P k (vertex k (quiver P) q) • _
      rw [h1, linPres_vertex, totToM_pdVert]
    · have h1 := Rep.pdAct_arrow (pieceProj S) (grRep ℓ k μ S) c
      change totToM ℓ k μ S ((grRep ℓ k μ S).pdAct (pieceProj S) (arrow k (quiver P) c) x) =
        linPres P k (arrow k (quiver P) c) • _
      rw [h1, linPres_arrow, totToM_pdArr hS]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, ha, hb, map_mul, mul_smul]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, ha, hb, map_add, add_smul]

/-- `mToTot` intertwines the actions too. -/
lemma mToTot_smul (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (z : (quiver P).PathAlgebra k) (m : M) :
    mToTot ℓ k μ S (linPres P k z • m) =
      (grRep ℓ k μ S).pdAct (pieceProj S) z (mToTot ℓ k μ S m) := by
  have := totToM_pdAct k hS z (mToTot ℓ k μ S m)
  rw [totToM_mToTot ℓ k μ S hS] at this
  rw [← this, mToTot_totToM]

/-- The endomorphism of `M` induced by an endomorphism of `grRep`. -/
def endM (e : grRep ℓ k μ S ⟶ grRep ℓ k μ S) : M →ₗ[k] M :=
  totToM ℓ k μ S ∘ₗ e.tot ∘ₗ mToTot ℓ k μ S

lemma endM_smul (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (e : grRep ℓ k μ S ⟶ grRep ℓ k μ S)
    (b : Linearization P k) (m : M) : endM k e (b • m) = b • endM k e m := by
  obtain ⟨z, rfl⟩ := linPres_surjective P k b
  simp only [endM, LinearMap.coe_comp, Function.comp_apply]
  rw [mToTot_smul k hS]
  have hc := Rep.commute_pdAct (pieceProj S) (grRep ℓ k μ S) e.tot
    (Rep.Hom.isPdHom_tot _ e).1 (Rep.Hom.isPdHom_tot _ e).2 z
  rw [← LinearMap.comp_apply (e.tot), hc, LinearMap.comp_apply, totToM_pdAct k hS]

/-- `endM` as a `k(P)`-linear map. -/
def endMA (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (e : grRep ℓ k μ S ⟶ grRep ℓ k μ S) :
    M →ₗ[Linearization P k] M where
  toFun := endM k e
  map_add' := map_add _
  map_smul' b m := endM_smul k hS e b m

lemma endM_homog (e : grRep ℓ k μ S ⟶ grRep ℓ k μ S) {g : Pi1 x₀} {m : M}
    (hm : μ.Mem g m) : μ.Mem g (endM k e m) := by
  simp only [endM, LinearMap.coe_comp, Function.comp_apply]
  change μ.Mem g (∑ a, toM ((e.app a).hom (mToTot ℓ k μ S m a)))
  refine μ.mem_sum _ _ fun a _ ↦ ?_
  by_cases ha : gOf ℓ (pt S a) = g
  · subst ha
    exact (show W ℓ k μ (pt S a) from (e.app a).hom (mToTot ℓ k μ S m a)).2.2
  · have h0 : mToTot ℓ k μ S m a = 0 := by
      apply toM_injective
      change morElt k (𝟙 (pt S a).y) • μ.proj (gOf ℓ (pt S a)) m = 0
      rw [μ.proj_of_mem hm ha, smul_zero]
    rw [h0, map_zero]
    exact μ.mem_zero g

/-- **Graded-indecomposable modules give indecomposable piece representations**: an
idempotent endomorphism of `grRep` is `0` or the identity. -/
theorem grRep_idem (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (hind : IsGrIndec μ)
    (e : grRep ℓ k μ S ⟶ grRep ℓ k μ S) (he : e ≫ e = e) :
    (∀ i, e.app i = 0) ∨ e = 𝟙 _ := by
  set ε := endMA k hS e
  have hεε : ε ∘ₗ ε = ε := by
    ext m
    change endM k e (endM k e m) = endM k e m
    simp only [endM, LinearMap.coe_comp, Function.comp_apply, mToTot_totToM]
    rw [← LinearMap.comp_apply e.tot, ← Rep.Hom.tot_comp, he]
  have hhom : IsHomog μ μ 1 ε := fun g m hm ↦ by rw [mul_one]; exact endM_homog k e hm
  have hεm : ∀ m, ε (ε m) = ε m := fun m ↦ LinearMap.congr_fun hεε m
  have hcompl : IsCompl (LinearMap.range ε) (LinearMap.ker ε) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro m ⟨⟨n, rfl⟩, hm⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hεm] at hm
      rw [Submodule.mem_bot, hm]
    · rw [codisjoint_iff, eq_top_iff]
      intro m _
      rw [show m = ε m + (m - ε m) by abel]
      refine Submodule.add_mem_sup (LinearMap.mem_range_self _ _) ?_
      rw [LinearMap.mem_ker, map_sub, hεm, sub_self]
  have htot : ∀ x, e.tot x = mToTot ℓ k μ S (ε (totToM ℓ k μ S x)) := fun x ↦ by
    change _ = mToTot ℓ k μ S (totToM ℓ k μ S (e.tot (mToTot ℓ k μ S (totToM ℓ k μ S x))))
    rw [mToTot_totToM, mToTot_totToM]
  rcases hind _ _ (isGrSub_range hhom) (isGrSub_ker hhom) hcompl with h | h
  · left
    intro i
    ext w
    have := htot (Pi.single i w)
    have h0 : ε (totToM ℓ k μ S (Pi.single i w)) = 0 := by
      have : ε (totToM ℓ k μ S (Pi.single i w)) ∈ LinearMap.range ε := LinearMap.mem_range_self _ _
      rw [h] at this; exact (Submodule.mem_bot _).1 this
    rw [h0, map_zero] at this
    have := congrFun this i
    rw [Rep.Hom.tot_apply, Pi.single_eq_same] at this
    exact this
  · right
    have hid : ∀ m, ε m = m := by
      intro m
      have hm : ε (m - ε m) = 0 := by
        rw [map_sub, hεm, sub_self]
      have : m - ε m ∈ LinearMap.ker ε := hm
      rw [h] at this
      exact (sub_eq_zero.1 ((Submodule.mem_bot _).1 this)).symm
    apply Rep.hom_ext
    intro i
    ext w
    have := htot (Pi.single i w)
    rw [hid, mToTot_totToM] at this
    have := congrFun this i
    rw [Rep.Hom.tot_apply, Pi.single_eq_same] at this
    rw [this]
    rfl

end LargeIndecomposable.RayCat
