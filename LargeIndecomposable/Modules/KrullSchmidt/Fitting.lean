module

public import LargeIndecomposable.AuslanderReiten.Lengths.Auslander

/-!
# Fitting's lemma; decomposition into indecomposables; right almost split families

* `IsIndecMod.isLocalRing`: a nonzero indecomposable finite-dimensional module has a local
  endomorphism ring (Fitting's lemma).
* `FDMod.exists_decomp`: every object is a finite direct sum of nonzero indecomposables.
* `FDMod.exists_rasFam`: every nonzero indecomposable object has a right almost split
  family whose sources are nonzero indecomposables.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Fitting's lemma.** -/
theorem IsIndecMod.isLocalRing {M : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] [Nontrivial M] (hM : IsIndecMod A M) :
    IsLocalRing (Module.End A M) := by
  haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
  haveI : IsArtinian A M := isArtinian_of_tower k inferInstance
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and
    (Filter.eventually_ge_atTop 1)).exists
  rcases hM _ _ hn with h | h
  · left
    have hinj : Function.Injective (f ^ n) := LinearMap.ker_eq_bot.1 h
    have hfinj : Function.Injective f := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      intro x y hxy
      apply hinj
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hxy]
    rw [Module.End.isUnit_iff]
    exact ⟨hfinj, (LinearMap.injective_iff_surjective (f := f.restrictScalars k)).1 hfinj⟩
  · right
    apply IsNilpotent.isUnit_one_sub
    refine ⟨n, LinearMap.ext fun x ↦ ?_⟩
    have : (f ^ n) x ∈ LinearMap.range (f ^ n) := LinearMap.mem_range_self _ x
    rw [h] at this
    simpa using this

/-- A direct sum decomposition of an object into nonzero indecomposables. -/
structure Decomp (E : FDMod k A) where
  ι : Type u
  [fin : Fintype ι]
  obj : ι → FDMod k A
  indec : ∀ i, IsIndecMod A (obj i)
  nt : ∀ i, Nontrivial (obj i)
  inc : ∀ i, obj i ⟶ E
  proj : ∀ i, E ⟶ obj i
  sum_id : ∑ i, FDMod.lin (inc i) ∘ₗ FDMod.lin (proj i) = LinearMap.id
  retr : ∀ i, FDMod.lin (proj i) ∘ₗ FDMod.lin (inc i) = LinearMap.id
  orth : ∀ i j, i ≠ j → FDMod.lin (proj j) ∘ₗ FDMod.lin (inc i) = 0

attribute [instance] Decomp.fin

/-- Decompositions of two complementary submodules give one of the whole module. -/
def Decomp.ofCompl {E : FDMod k A} (U V : Submodule A E) (hUV : IsCompl U V)
    (dU : Decomp (FDMod.ofSub U)) (dV : Decomp (FDMod.ofSub V)) : Decomp E where
  ι := dU.ι ⊕ dV.ι
  obj := Sum.elim dU.obj dV.obj
  indec i := match i with
    | .inl i => dU.indec i
    | .inr i => dV.indec i
  nt i := match i with
    | .inl i => dU.nt i
    | .inr i => dV.nt i
  inc i := match i with
    | .inl i => show dU.obj i →ₗ[A] E from U.subtype ∘ₗ FDMod.lin (dU.inc i)
    | .inr i => show dV.obj i →ₗ[A] E from V.subtype ∘ₗ FDMod.lin (dV.inc i)
  proj i := match i with
    | .inl i => show E →ₗ[A] dU.obj i from
        FDMod.lin (dU.proj i) ∘ₗ Submodule.projectionOnto U V hUV
    | .inr i => show E →ₗ[A] dV.obj i from
        FDMod.lin (dV.proj i) ∘ₗ Submodule.projectionOnto V U hUV.symm
  sum_id := by
    rw [Fintype.sum_sum_type]
    ext x
    have hU := LinearMap.congr_fun dU.sum_id (Submodule.projectionOnto U V hUV x)
    have hV := LinearMap.congr_fun dV.sum_id (Submodule.projectionOnto V U hUV.symm x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at hU hV
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.id_coe, id_eq]
    change ∑ i, (U.subtype (FDMod.lin (dU.inc i) (FDMod.lin (dU.proj i)
        (Submodule.projectionOnto U V hUV x)))) +
      ∑ i, (V.subtype (FDMod.lin (dV.inc i) (FDMod.lin (dV.proj i)
        (Submodule.projectionOnto V U hUV.symm x)))) = x
    calc _ = U.subtype (∑ i, FDMod.lin (dU.inc i) (FDMod.lin (dU.proj i)
            (Submodule.projectionOnto U V hUV x))) +
          V.subtype (∑ i, FDMod.lin (dV.inc i) (FDMod.lin (dV.proj i)
            (Submodule.projectionOnto V U hUV.symm x))) := by simp only [map_sum]
      _ = x := by
        rw [hU, hV]
        exact Submodule.projection_add_projection_eq_self hUV x
  retr i := match i with
    | .inl i => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dU.proj i) (Submodule.projectionOnto U V hUV
          (U.subtype (FDMod.lin (dU.inc i) x))) = x
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left]
        exact LinearMap.congr_fun (dU.retr i) x
    | .inr i => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dV.proj i) (Submodule.projectionOnto V U hUV.symm
          (V.subtype (FDMod.lin (dV.inc i) x))) = x
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left]
        exact LinearMap.congr_fun (dV.retr i) x
  orth i j hij := match i, j with
    | .inl i, .inl j => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dU.proj j) (Submodule.projectionOnto U V hUV
          (U.subtype (FDMod.lin (dU.inc i) x))) = 0
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left]
        exact LinearMap.congr_fun (dU.orth i j fun h ↦ hij (h ▸ rfl)) x
    | .inr i, .inr j => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dV.proj j) (Submodule.projectionOnto V U hUV.symm
          (V.subtype (FDMod.lin (dV.inc i) x))) = 0
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left]
        exact LinearMap.congr_fun (dV.orth i j fun h ↦ hij (h ▸ rfl)) x
    | .inl i, .inr j => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dV.proj j) (Submodule.projectionOnto V U hUV.symm
          (U.subtype (FDMod.lin (dU.inc i) x))) = 0
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_right hUV.symm, map_zero]
    | .inr i, .inl j => by
        apply LinearMap.ext; intro x
        change FDMod.lin (dU.proj j) (Submodule.projectionOnto U V hUV
          (V.subtype (FDMod.lin (dV.inc i) x))) = 0
        rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_right hUV, map_zero]

/-- **Every object decomposes into nonzero indecomposables.** -/
theorem FDMod.exists_decomp : ∀ E : FDMod k A, Nonempty (Decomp E) := by
  classical
  suffices H : ∀ n, ∀ E : FDMod k A, finrank k E = n → Nonempty (Decomp E) from
    fun E ↦ H _ E rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hn
  by_cases htriv : Subsingleton E
  · refine ⟨Decomp.mk PEmpty.{u + 1} (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
      (fun i ↦ i.elim) (fun i ↦ i.elim) ?_ (fun i ↦ i.elim) (fun i ↦ i.elim)⟩
    ext x; exact Subsingleton.elim _ _
  rw [not_subsingleton_iff_nontrivial] at htriv
  by_cases hind : IsIndecMod A E
  · exact ⟨Decomp.mk PUnit.{u + 1} (fun _ ↦ E) (fun _ ↦ hind) (fun _ ↦ htriv) (fun _ ↦ 𝟙 E)
      (fun _ ↦ 𝟙 E) (by simp) (fun _ ↦ rfl) (fun i j h ↦ absurd (Subsingleton.elim i j) h)⟩
  simp only [IsIndecMod, not_forall] at hind
  obtain ⟨U, V, hUV, hne⟩ := hind
  push Not at hne
  have hlt : ∀ (W W' : Submodule A E), IsCompl W W' → W' ≠ ⊥ →
      finrank k (FDMod.ofSub W) < n := by
    intro W W' hc hW'
    rw [← hn]
    have h1 := Submodule.finrank_add_eq_of_isCompl (K := k) (U := W.restrictScalars k)
      (W := W'.restrictScalars k) (by
        constructor
        · rw [disjoint_iff, ← Submodule.restrictScalars_inf, hc.inf_eq_bot,
            Submodule.restrictScalars_bot]
        · rw [codisjoint_iff, ← Submodule.restrictScalars_sup, hc.sup_eq_top,
            Submodule.restrictScalars_top])
    have h2 : 0 < finrank k (W'.restrictScalars k) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
      exact ⟨⟨x, hx⟩, fun h ↦ hx0 (congrArg Subtype.val h)⟩
    change finrank k (W.restrictScalars k) < _
    omega
  obtain ⟨dU⟩ := ih _ (hlt U V hUV hne.2) _ rfl
  obtain ⟨dV⟩ := ih _ (hlt V U hUV.symm hne.1) _ rfl
  exact ⟨Decomp.ofCompl U V hUV dU dV⟩

/-- **Right almost split families into nonzero indecomposables**, with nonzero
indecomposable sources. -/
theorem FDMod.exists_rasFam [FiniteDimensional k A] (Z : FDMod k A) (hZ : IsIndecMod A Z)
    [Nontrivial Z] :
    Nonempty (RASFam (fun X : FDMod k A ↦ IsIndecMod A X ∧ Nontrivial X) Z) := by
  classical
  haveI := hZ.isLocalRing (k := k)
  obtain ⟨E, g, hg1, hg2⟩ := FDMod.exists_rightAS Z
  obtain ⟨d⟩ := FDMod.exists_decomp E
  refine ⟨RASFam.mk d.ι d.obj (fun i ↦ ⟨d.indec i, d.nt i⟩) (fun i ↦ d.inc i ≫ g) ?_ ?_⟩
  · rintro ⟨h, hh⟩
    apply hg1
    refine ⟨show Z →ₗ[A] E from ∑ i, FDMod.lin (d.inc i) ∘ₗ FDMod.lin (h i), ?_⟩
    show FDMod.lin g ∘ₗ (∑ i, FDMod.lin (d.inc i) ∘ₗ FDMod.lin (h i)) = LinearMap.id
    rw [← hh]
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum,
      FDMod.lin_comp]
  · intro W v hv
    obtain ⟨t, ht⟩ := hg2 W v fun ⟨s, hs⟩ ↦ hv ⟨s, hs⟩
    refine ⟨fun i ↦ t ≫ d.proj i, ?_⟩
    have hid := d.sum_id
    rw [← ht]
    ext x
    have := LinearMap.congr_fun hid (FDMod.lin t x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    simp only [FDMod.lin_comp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [← map_sum (FDMod.lin g), this]

end LargeIndecomposable.AR
