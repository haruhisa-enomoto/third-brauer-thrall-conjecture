module

public import LargeIndecomposable.DirectedAlgebras.Directing.ResProj

/-!
# Preliminaries for Bongartz's Lemma 2.4 (b)

Left almost split maps under isomorphisms; modules whose decomposition summands live on `T'` live
on `T'`; restriction preserves isomorphism and exactness; and a left almost split map over the
quotient restricts to a left almost split map over `A` as soon as some left almost split map over
`A` with the same source lands in modules living on `T'` (`isLeftAS_res`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Left almost split maps precomposed with isomorphisms.** -/
lemma isLeftAS_iso_comp {X' X E : FDMod k A} {f : X ⟶ E} (hf : IsLeftAS f) (h : X' ⟶ X)
    (hh : Function.Bijective (FDMod.lin h)) : IsLeftAS (h ≫ f) := by
  refine ⟨fun ⟨r, hr⟩ ↦ hf.1 ⟨r ≫ h, ?_⟩, fun W u hu ↦ ?_⟩
  · apply FDMod.hom_ext; apply LinearMap.ext; intro x
    obtain ⟨x', rfl⟩ := hh.2 x
    change FDMod.lin h (FDMod.lin r (FDMod.lin f (FDMod.lin h x'))) = FDMod.lin h x'
    rw [show FDMod.lin r (FDMod.lin f (FDMod.lin h x')) = x' from LinearMap.congr_fun (congrArg FDMod.lin hr) x']
  · have hu' : ¬∃ r : W ⟶ X, (invOf h hh ≫ u) ≫ r = 𝟙 X := by
      rintro ⟨r, hr⟩
      refine hu ⟨r ≫ invOf h hh, (FDMod.hom_ext (LinearMap.ext fun x' ↦ ?_))⟩
      have := LinearMap.congr_fun (congrArg FDMod.lin (hr)) (FDMod.lin h x')
      change FDMod.lin r (FDMod.lin u (FDMod.lin (invOf h hh) (FDMod.lin h x'))) = _ at this
      rw [show FDMod.lin (invOf h hh) (FDMod.lin h x') = x' from
        LinearMap.congr_fun (congrArg FDMod.lin (comp_invOf h hh)) x'] at this
      change FDMod.lin (invOf h hh) (FDMod.lin r (FDMod.lin u x')) = x'
      rw [this]
      exact LinearMap.congr_fun (congrArg FDMod.lin ((comp_invOf h hh))) x'
    obtain ⟨t, ht⟩ := hf.2 W (invOf h hh ≫ u) hu'
    refine ⟨t, (FDMod.hom_ext (LinearMap.ext fun x' ↦ ?_))⟩
    have := LinearMap.congr_fun (congrArg FDMod.lin (ht)) (FDMod.lin h x')
    change FDMod.lin t (FDMod.lin f (FDMod.lin h x')) =
      FDMod.lin u (FDMod.lin (invOf h hh) (FDMod.lin h x')) at this
    rw [show FDMod.lin (invOf h hh) (FDMod.lin h x') = x' from
      LinearMap.congr_fun (congrArg FDMod.lin (comp_invOf h hh)) x'] at this
    exact this

lemma IsoM.res {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'} {X Y : FDMod k A'}
    (h : IsoM X Y) : IsoM (resFD φ X) (resFD φ Y) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨resHom φ g, hg⟩

lemma IsoM.unres {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'}
    (hφ : Function.Surjective φ) {X Y : FDMod k A'} (h : IsoM (resFD φ X) (resFD φ Y)) :
    IsoM X Y := by
  obtain ⟨g, hg⟩ := h
  exact ⟨unresHom hφ g, hg⟩

section ResExact

variable {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'}

lemma res_injective {X Y : FDMod k A'} {f : X ⟶ Y} (hf : Function.Injective (FDMod.lin f)) :
    Function.Injective (FDMod.lin (resHom φ f)) := hf

lemma res_surjective {X Y : FDMod k A'} {f : X ⟶ Y} (hf : Function.Surjective (FDMod.lin f)) :
    Function.Surjective (FDMod.lin (resHom φ f)) := hf

lemma res_exact {X Y Z : FDMod k A'} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g)) :
    LinearMap.range (FDMod.lin (resHom φ f)) = LinearMap.ker (FDMod.lin (resHom φ g)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have : FDMod.lin f (toX x) ∈ LinearMap.ker (FDMod.lin g) := hex ▸ LinearMap.mem_range_self _ _
    exact this
  · intro hy
    have hy' : toX y ∈ LinearMap.range (FDMod.lin f) := hex ▸ hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨ofX x, hx⟩

end ResExact

variable [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {T' : Set D.ι}

/-- **A module whose summands live on `T'` lives on `T'`.** -/
lemma livesOn_of_decomp {E : FDMod k A} (d : Decomp E) (h : ∀ i, LivesOn T' (d.obj i)) :
    LivesOn T' E := by
  intro v hv e
  have hsum : e = ∑ i, FDMod.lin (d.inc i) (FDMod.lin (d.proj i) e) := by
    simpa using (LinearMap.congr_fun d.sum_id e).symm
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← map_smul, h i v hv, map_zero]

variable (hT : D.ConvexSet T')

include hT in
/-- **Relative factorization through a left almost split map of the quotient.** -/
lemma leftAS_res_factor {K E : FDMod k (D.QAlg T')} {f : K ⟶ E} (hf : IsLeftAS f)
    (W : FDMod k A) (hW : LivesOn T' W) (u : resFD (D.qmap T') K ⟶ W)
    (hu : ¬∃ r : W ⟶ resFD (D.qmap T') K, u ≫ r = 𝟙 _) :
    ∃ t : resFD (D.qmap T') E ⟶ W, resHom (D.qmap T') f ≫ t = u := by
  have hφ := D.qmap_surjective T'
  let u' : K ⟶ descendQ W hW := unresHom hφ (u ≫ descIsoQInv W hW)
  have hu' : ¬∃ r : descendQ W hW ⟶ K, u' ≫ r = 𝟙 K := by
    rintro ⟨r, hr⟩
    exact hu ⟨descIsoQInv W hW ≫ resHom (D.qmap T') r, (FDMod.hom_ext (LinearMap.ext fun x ↦
      LinearMap.congr_fun (congrArg FDMod.lin (hr)) (toX x)))⟩
  obtain ⟨t', ht'⟩ := hf.2 _ u' hu'
  exact ⟨resHom (D.qmap T') t' ≫ descIsoQ W hW, (FDMod.hom_ext (LinearMap.ext fun x ↦
    LinearMap.congr_fun (congrArg FDMod.lin (ht')) (toX x)))⟩

include hT in
/-- **Restricted left almost split maps are left almost split** when some left almost split map
over `A` with the same source lands in modules living on `T'`. -/
theorem isLeftAS_res {K E : FDMod k (D.QAlg T')} {f : K ⟶ E} (hf : IsLeftAS f)
    {E'' : FDMod k A} {f'' : resFD (D.qmap T') K ⟶ E''} (hf'' : IsLeftAS f'')
    (hE'' : LivesOn T' E'') : IsLeftAS (resHom (D.qmap T') f) := by
  have hφ := D.qmap_surjective T'
  refine ⟨fun h ↦ hf.1 ((splitMono_res_iff hφ f).1 h), fun W u hu ↦ ?_⟩
  obtain ⟨t, ht⟩ := hf''.2 W u hu
  obtain ⟨s, hs⟩ := leftAS_res_factor hT hf E'' hE'' f'' hf''.1
  exact ⟨s ≫ t, by rw [← Category.assoc, hs, ht]⟩

end DirData

end LargeIndecomposable.AR
