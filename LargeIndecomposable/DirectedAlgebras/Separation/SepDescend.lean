module

public import LargeIndecomposable.DirectedAlgebras.Separation.SepCases

/-!
# Radicals over a convex quotient

If `P(z)` lives on a convex `T'`, the radical of the quotient projective at `z` restricts to
`rad P(z)` (`isoM_res_radP`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {T' : Set D.ι} (hT : D.ConvexSet T')

/-- **The quotient radical at `z` restricts to `rad P(z)`.** -/
theorem isoM_res_radP (z : D.ι) (hzT : z ∈ T') (hz : LivesOn T' (projE (k := k) (D.idem z))) :
    IsoM (D.RadP z) (resFD (D.qmap T') ((D.quot hT).RadP z)) := by
  let P := projE (k := k) (D.idem z)
  let ez : P := ⟨D.e z, e_mem (D.idem z)⟩
  let D' := D.quot hT
  have hez : D.qmap T' (D.e z) ≠ 0 := D'.ne z hzT
  let Φ : D.RadP z ⟶ resFD (D.qmap T') (D'.RadP z) :=
    FDMod.ofLin
    { toFun r := ofX (⟨⟨D.qmap T' ((r : P) : A), by
          change D.qmap T' ((r : P) : A) * D.qmap T' (D.e z) = D.qmap T' ((r : P) : A)
          rw [← map_mul, show ((r : P) : A) * D.e z = (r : P) from (r : P).2]⟩, by
          change D.qmap T' (D.e z) * D.qmap T' ((r : P) : A) = 0
          rw [← map_mul, show D.e z * ((r : P) : A) = 0 from r.2, map_zero]⟩ : D'.radP z)
      map_add' a b := by
        apply toX_injective; apply Subtype.ext; apply Subtype.ext
        change D.qmap T' (((a : P) : A) + ((b : P) : A)) = _
        rw [map_add]; rfl
      map_smul' c a := by
        apply toX_injective; apply Subtype.ext; apply Subtype.ext
        change D.qmap T' (c * ((a : P) : A)) = _
        rw [map_mul]; rfl }
  let val : resFD (D.qmap T') (D'.RadP z) → D.QAlg T' := fun b ↦
    (((toX b : D'.radP z) : projE (k := k) (D'.idem z)) : D.QAlg T')
  have hval_rad : ∀ b, D.qmap T' (D.e z) * val b = 0 := fun b ↦ (toX b).2
  have hval_l : ∀ b, val b * D.qmap T' (D.e z) = val b := fun b ↦
    ((toX b : D'.radP z) : projE (k := k) (D'.idem z)).2
  have hmemΨ : ∀ b, actQ P hz (val b) ez ∈ D.radP z := by
    intro b
    obtain ⟨a, ha⟩ := D.qmap_surjective T' (val b)
    change D.e z * ((actQ P hz (val b) ez : P) : A) = 0
    rw [← ha, actQ_qmap]
    change D.e z * (a * D.e z) = 0
    have h1 : D.qmap T' (D.e z * a * D.e z) = 0 := by
      rw [map_mul, map_mul, ha, mul_assoc, hval_l, hval_rad]
    rw [D.chi_spec z (hT.1 hzT), map_smul] at h1
    have h2 : D.chi z (hT.1 hzT) a = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hez
    rw [← mul_assoc, D.chi_spec z (hT.1 hzT), h2, zero_smul]
  let Ψ : resFD (D.qmap T') (D'.RadP z) ⟶ D.RadP z :=
    FDMod.ofLin
    { toFun b := ⟨actQ P hz (val b) ez, hmemΨ b⟩
      map_add' a b := by
        apply Subtype.ext
        change actQ P hz (val (a + b)) ez = actQ P hz (val a) ez + actQ P hz (val b) ez
        rw [show val (a + b) = val a + val b from rfl, map_add]; rfl
      map_smul' c b := by
        apply Subtype.ext
        change actQ P hz (D.qmap T' c * val b) ez = c • actQ P hz (val b) ez
        rw [map_mul, Module.End.mul_apply, actQ_qmap] }
  have hΨΦ : ∀ r : D.RadP z, FDMod.lin Ψ (FDMod.lin Φ r) = r := fun r ↦ by
    apply Subtype.ext
    change actQ P hz (D.qmap T' ((r : P) : A)) ez = (r : P)
    rw [actQ_qmap]
    apply Subtype.ext
    exact (r : P).2
  refine ⟨Φ, fun a b h ↦ by rw [← hΨΦ a, ← hΨΦ b, h], fun b ↦ ⟨FDMod.lin Ψ b, ?_⟩⟩
  apply toX_injective; apply Subtype.ext; apply Subtype.ext
  obtain ⟨a, ha⟩ := D.qmap_surjective T' (val b)
  change D.qmap T' ((actQ P hz (val b) ez : P) : A) = val b
  rw [← ha, actQ_qmap]
  change D.qmap T' (a * D.e z) = _
  rw [map_mul, ha, hval_l]

/-- **A decomposition into summands living on `T'` descends along an isomorphism.** -/
def decompDescend {X : FDMod k (D.QAlg T')} {M : FDMod k A} (g : M ⟶ resFD (D.qmap T') X)
    (hg : Function.Bijective (FDMod.lin g)) (d : Decomp M) (hd : ∀ i, LivesOn T' (d.obj i)) :
    Decomp X where
  ι := d.ι
  obj i := descendQ (d.obj i) (hd i)
  indec i := ((indNT_res_iff (D.qmap_surjective T') _).1
    (indNT_of_iso (isoM_descend' _ (hd i)) ⟨d.indec i, d.nt i⟩)).1
  nt i := ((indNT_res_iff (D.qmap_surjective T') _).1
    (indNT_of_iso (isoM_descend' _ (hd i)) ⟨d.indec i, d.nt i⟩)).2
  inc i := unresHom (D.qmap_surjective T') (descIsoQ _ (hd i) ≫ d.inc i ≫ g)
  proj i := unresHom (D.qmap_surjective T') (invOf g hg ≫ d.proj i ≫ descIsoQInv _ (hd i))
  sum_id := by
    apply LinearMap.ext; intro x
    rw [LinearMap.sum_apply]
    change ∑ i, FDMod.lin g (FDMod.lin (d.inc i) (FDMod.lin (d.proj i)
      (FDMod.lin (invOf g hg) (ofX x)))) = x
    rw [← map_sum]
    have := LinearMap.congr_fun d.sum_id (FDMod.lin (invOf g hg) (ofX x))
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.id_apply] at this
    rw [this]
    exact LinearMap.congr_fun (congrArg FDMod.lin ((invOf_comp g hg))) (ofX x)
  retr i := by
    apply LinearMap.ext; intro x
    change FDMod.lin (d.proj i) (FDMod.lin (invOf g hg) (FDMod.lin g
      (FDMod.lin (d.inc i) x))) = x
    rw [show FDMod.lin (invOf g hg) (FDMod.lin g (FDMod.lin (d.inc i) x)) =
      FDMod.lin (d.inc i) x from LinearMap.congr_fun (congrArg FDMod.lin (comp_invOf g hg)) _]
    exact LinearMap.congr_fun (d.retr i) x
  orth i j h := by
    apply LinearMap.ext; intro x
    change FDMod.lin (d.proj j) (FDMod.lin (invOf g hg) (FDMod.lin g
      (FDMod.lin (d.inc i) x))) = 0
    rw [show FDMod.lin (invOf g hg) (FDMod.lin g (FDMod.lin (d.inc i) x)) =
      FDMod.lin (d.inc i) x from LinearMap.congr_fun (congrArg FDMod.lin (comp_invOf g hg)) _]
    exact LinearMap.congr_fun (d.orth i j h) x

lemma quot_supp (Y : FDMod k (D.QAlg T')) :
    (D.quot hT).Supp Y = D.Supp (resFD (D.qmap T') Y) := rfl

lemma quot_qset_sub {z : D.ι} (hz : z ∈ T') : (D.quot hT).QSet z ⊆ D.QSet z := by
  rintro y ⟨hy, hny⟩
  exact ⟨hT.1 hy, fun h ↦ hny (D.restrict_path hT hy hz h)⟩

lemma quot_conn {z u v : D.ι} (hz : z ∈ T')
    (h : (D.quot hT).Conn ((D.quot hT).QSet z) u v) : D.Conn (D.QSet z) u v :=
  rtg_mono (fun _ _ h ↦ ⟨quot_qset_sub hT hz h.1, quot_qset_sub hT hz h.2.1,
    h.2.2.imp (fun h ↦ h.1) (fun h ↦ h.1)⟩) h

/-- **Separating decompositions descend.** -/
theorem sepDecomp_descend {z : D.ι} (hz : z ∈ T') {d : Decomp (D.RadP z)}
    (hsd : D.SepDecomp z d) (hd : ∀ i, LivesOn T' (d.obj i))
    (g : D.RadP z ⟶ resFD (D.qmap T') ((D.quot hT).RadP z))
    (hg : Function.Bijective (FDMod.lin g)) :
    (D.quot hT).SepDecomp z (decompDescend g hg d hd) := by
  intro i j hij u v hu hv hc
  rw [quot_supp] at hu hv
  exact hsd i j hij u v (supp_iso (isoM_descend _ (hd i)) hu) (supp_iso (isoM_descend _ (hd j)) hv)
    (quot_conn hT hz hc)

end DirData

end LargeIndecomposable.AR
