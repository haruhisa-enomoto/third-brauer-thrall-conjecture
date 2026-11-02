module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.PreprojInd

/-!
# Uniqueness of Auslander–Reiten sequences

Right almost split maps stay right almost split after an isomorphism of the target
(`isRightAS_comp_iso`). Two exact sequences `0 → K → E → Z → 0` and `0 → K → E' → Z' → 0` with
injective left almost split first maps and local `End Z`, `End Z'` have isomorphic end terms
(`coker_iso_of_leftAS`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Right almost split maps compose with isomorphisms of the target.** -/
lemma isRightAS_comp_iso {E Z Z' : FDMod k A} {g : E ⟶ Z} (hg : IsRightAS g) (a : Z ⟶ Z')
    (ha : Function.Bijective (FDMod.lin a)) : IsRightAS (g ≫ a) := by
  let ai := invOf a ha
  have hai : ∀ z', FDMod.lin a (FDMod.lin ai z') = z' := fun z' ↦
    LinearMap.congr_fun (congrArg FDMod.lin (invOf_comp a ha)) z'
  have hia : ∀ z, FDMod.lin ai (FDMod.lin a z) = z := fun z ↦
    LinearMap.congr_fun (congrArg FDMod.lin (comp_invOf a ha)) z
  refine ⟨fun ⟨s, hs⟩ ↦ hg.1 ⟨a ≫ s, (FDMod.hom_ext (LinearMap.ext fun z ↦ ?_))⟩, fun W u hu ↦ ?_⟩
  · apply ha.1
    exact LinearMap.congr_fun (congrArg FDMod.lin hs) (FDMod.lin a z)
  · have hu' : ¬∃ s : Z ⟶ W, s ≫ (u ≫ ai) = 𝟙 Z := by
      rintro ⟨s, hs⟩
      refine hu ⟨ai ≫ s, (FDMod.hom_ext (LinearMap.ext fun z' ↦ ?_))⟩
      have := LinearMap.congr_fun (congrArg FDMod.lin hs) (FDMod.lin ai z')
      change FDMod.lin ai (FDMod.lin u (FDMod.lin s (FDMod.lin ai z'))) = FDMod.lin ai z' at this
      have h2 := congrArg (FDMod.lin a) this
      rw [hai, hai] at h2
      exact h2
    obtain ⟨v, hv⟩ := hg.2 W (u ≫ ai) hu'
    refine ⟨v, (FDMod.hom_ext (LinearMap.ext fun w ↦ ?_))⟩
    have := LinearMap.congr_fun (congrArg FDMod.lin hv) w
    change FDMod.lin g (FDMod.lin v w) = FDMod.lin ai (FDMod.lin u w) at this
    change FDMod.lin a (FDMod.lin g (FDMod.lin v w)) = FDMod.lin u w
    rw [this, hai]

/-- The map induced on cokernels. -/
def indMap {E E' Z Z' : FDMod k A} (g : E ⟶ Z) (hg : Function.Surjective (FDMod.lin g))
    (g' : E' ⟶ Z') (a : E ⟶ E')
    (h : ∀ e, FDMod.lin g e = 0 → FDMod.lin g' (FDMod.lin a e) = 0) : Z ⟶ Z' :=
  (FDMod.ofLin (show Z →ₗ[A] Z' from (LinearMap.ker (FDMod.lin g)).liftQ (FDMod.lin g' ∘ₗ FDMod.lin a)
    (fun e he ↦ h e he) ∘ₗ (LinearMap.quotKerEquivOfSurjective _ hg).symm.toLinearMap))

lemma indMap_spec {E E' Z Z' : FDMod k A} (g : E ⟶ Z) (hg : Function.Surjective (FDMod.lin g))
    (g' : E' ⟶ Z') (a : E ⟶ E')
    (h : ∀ e, FDMod.lin g e = 0 → FDMod.lin g' (FDMod.lin a e) = 0) (e : E) :
    FDMod.lin (indMap g hg g' a h) (FDMod.lin g e) = FDMod.lin g' (FDMod.lin a e) := by
  have hq : (LinearMap.quotKerEquivOfSurjective _ hg).symm (FDMod.lin g e) =
      Submodule.Quotient.mk e := (LinearMap.quotKerEquivOfSurjective _ hg).symm_apply_eq.2 rfl
  change (LinearMap.ker (FDMod.lin g)).liftQ (FDMod.lin g' ∘ₗ FDMod.lin a) (fun e he ↦ h e he)
    ((LinearMap.quotKerEquivOfSurjective _ hg).symm (FDMod.lin g e)) = _
  rw [hq]
  rfl

/-- A surjection whose kernel is the image of a non-split injection does not split. -/
lemma not_splitEpi_of_leftAS {K E Z : FDMod k A} {f : K ⟶ E} (hf : IsLeftAS f)
    (hfinj : Function.Injective (FDMod.lin f)) {g : E ⟶ Z}
    (hg : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g)) :
    ¬∃ s : Z ⟶ E, s ≫ g = 𝟙 Z := by
  rintro ⟨s, hs⟩
  apply hf.1
  have hmem : ∀ e, e - FDMod.lin s (FDMod.lin g e) ∈ LinearMap.range (FDMod.lin f) := fun e ↦ by
    rw [hex, LinearMap.mem_ker, map_sub]
    rw [show FDMod.lin g (FDMod.lin s (FDMod.lin g e)) = FDMod.lin g e from
      LinearMap.congr_fun (congrArg FDMod.lin hs) _, sub_self]
  let ef := LinearEquiv.ofInjective (FDMod.lin f) hfinj
  refine ⟨(FDMod.ofLin (show E →ₗ[A] K from ef.symm.toLinearMap ∘ₗ LinearMap.codRestrict _
    (LinearMap.id - FDMod.lin s ∘ₗ FDMod.lin g) hmem)), (FDMod.hom_ext (LinearMap.ext fun x ↦ ?_))⟩
  change ef.symm ⟨FDMod.lin f x - FDMod.lin s (FDMod.lin g (FDMod.lin f x)), _⟩ = x
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  change FDMod.lin f x - FDMod.lin s (FDMod.lin g (FDMod.lin f x)) = FDMod.lin f x
  have : FDMod.lin g (FDMod.lin f x) = 0 := by
    rw [← LinearMap.mem_ker, ← hex]; exact LinearMap.mem_range_self _ x
  rw [this, map_zero, sub_zero]

/-- The round trip between the end terms of two sequences with left almost split first maps is
an automorphism. -/
lemma roundTrip_bijective {K E E' Z Z' : FDMod k A} {f : K ⟶ E} {g : E ⟶ Z} {f' : K ⟶ E'}
    {g' : E' ⟶ Z'} (hf : IsLeftAS f) (hfi : Function.Injective (FDMod.lin f))
    (hg : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g))
    (hg' : Function.Surjective (FDMod.lin g'))
    (hex' : LinearMap.range (FDMod.lin f') = LinearMap.ker (FDMod.lin g'))
    [IsLocalRing (Module.End A Z)] (a : E ⟶ E') (b : E' ⟶ E) (ha : f ≫ a = f') (hb : f' ≫ b = f)
    (hA : ∀ e, FDMod.lin g e = 0 → FDMod.lin g' (FDMod.lin a e) = 0)
    (hB : ∀ e, FDMod.lin g' e = 0 → FDMod.lin g (FDMod.lin b e) = 0) :
    Function.Bijective (FDMod.lin (indMap g' hg' g b hB) ∘ₗ FDMod.lin (indMap g hg g' a hA)) := by
  set ψ : Module.End A Z := FDMod.lin (indMap g' hg' g b hB) ∘ₗ FDMod.lin (indMap g hg g' a hA)
  have hψ : ∀ e, ψ (FDMod.lin g e) = FDMod.lin g (FDMod.lin b (FDMod.lin a e)) := fun e ↦ by
    change FDMod.lin (indMap g' hg' g b hB) (FDMod.lin (indMap g hg g' a hA) (FDMod.lin g e)) = _
    rw [indMap_spec, indMap_spec]
  have hfab : ∀ k', FDMod.lin b (FDMod.lin a (FDMod.lin f k')) = FDMod.lin f k' := fun k' ↦ by
    have h1 : FDMod.lin a (FDMod.lin f k') = FDMod.lin f' k' := LinearMap.congr_fun (congrArg FDMod.lin ha) k'
    rw [h1]; exact LinearMap.congr_fun (congrArg FDMod.lin hb) k'
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ψ with h | h
  · exact (Module.End.isUnit_iff ψ).1 h
  · exfalso
    let c : E ⟶ E := (FDMod.ofLin (show E →ₗ[A] E from LinearMap.id - FDMod.lin b ∘ₗ FDMod.lin a))
    have hC : ∀ e, FDMod.lin g e = 0 → FDMod.lin (𝟙 E) (FDMod.lin c e) = 0 := fun e he ↦ by
      rw [← LinearMap.mem_ker, ← hex] at he
      obtain ⟨k', rfl⟩ := he
      change FDMod.lin f k' - FDMod.lin b (FDMod.lin a (FDMod.lin f k')) = 0
      rw [hfab, sub_self]
    let hmap := indMap g hg (𝟙 E) c hC
    have hh : ∀ z, (1 - ψ) z = FDMod.lin g (FDMod.lin hmap z) := fun z ↦ by
      obtain ⟨e, rfl⟩ := hg z
      rw [indMap_spec]
      change FDMod.lin g e - ψ (FDMod.lin g e) = FDMod.lin g (e - FDMod.lin b (FDMod.lin a e))
      rw [hψ, map_sub]
    obtain ⟨w, hw1, -⟩ := isUnit_iff_exists.1 h
    refine not_splitEpi_of_leftAS hf hfi hg hex ⟨(FDMod.ofLin (show Z →ₗ[A] E from FDMod.lin hmap ∘ₗ w)),
      (FDMod.hom_ext (LinearMap.ext fun z ↦ ?_))⟩
    change FDMod.lin g (FDMod.lin hmap (w z)) = z
    rw [← hh]
    exact LinearMap.congr_fun hw1 z

/-- **Auslander–Reiten sequences are determined by their left end.** -/
theorem coker_iso_of_leftAS {K E E' Z Z' : FDMod k A} {f : K ⟶ E} {g : E ⟶ Z} {f' : K ⟶ E'}
    {g' : E' ⟶ Z'} (hf : IsLeftAS f) (hfi : Function.Injective (FDMod.lin f))
    (hg : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g))
    (hf' : IsLeftAS f') (hfi' : Function.Injective (FDMod.lin f'))
    (hg' : Function.Surjective (FDMod.lin g'))
    (hex' : LinearMap.range (FDMod.lin f') = LinearMap.ker (FDMod.lin g'))
    [IsLocalRing (Module.End A Z)] [IsLocalRing (Module.End A Z')] : IsoM Z Z' := by
  obtain ⟨a, ha⟩ := hf.2 E' f' hf'.1
  obtain ⟨b, hb⟩ := hf'.2 E f hf.1
  have hA : ∀ e, FDMod.lin g e = 0 → FDMod.lin g' (FDMod.lin a e) = 0 := fun e he ↦ by
    rw [← LinearMap.mem_ker, ← hex] at he
    obtain ⟨k', rfl⟩ := he
    rw [show FDMod.lin a (FDMod.lin f k') = FDMod.lin f' k' from LinearMap.congr_fun (congrArg FDMod.lin ha) k',
      ← LinearMap.mem_ker, ← hex']
    exact LinearMap.mem_range_self _ _
  have hB : ∀ e, FDMod.lin g' e = 0 → FDMod.lin g (FDMod.lin b e) = 0 := fun e he ↦ by
    rw [← LinearMap.mem_ker, ← hex'] at he
    obtain ⟨k', rfl⟩ := he
    rw [show FDMod.lin b (FDMod.lin f' k') = FDMod.lin f k' from LinearMap.congr_fun (congrArg FDMod.lin hb) k',
      ← LinearMap.mem_ker, ← hex]
    exact LinearMap.mem_range_self _ _
  have h1 := roundTrip_bijective hf hfi hg hex hg' hex' a b ha hb hA hB
  have h2 := roundTrip_bijective hf' hfi' hg' hex' hg hex b a hb ha hB hA
  refine ⟨indMap g hg g' a hA, fun x y hxy ↦ h1.1 ?_, fun z ↦ ?_⟩
  · change FDMod.lin (indMap g' hg' g b hB) (FDMod.lin (indMap g hg g' a hA) x) =
      FDMod.lin (indMap g' hg' g b hB) (FDMod.lin (indMap g hg g' a hA) y)
    rw [hxy]
  · obtain ⟨w, hw⟩ := h2.2 z
    exact ⟨_, hw⟩

/-- **In an Auslander–Reiten sequence with right minimal right map, the left map is left
minimal.** -/
theorem leftMinimal_of_arSeq {K E Z : FDMod k A} {f : K ⟶ E} {g : E ⟶ Z} (hf : IsLeftAS f)
    (hfi : Function.Injective (FDMod.lin f)) (hg : IsRightAS g)
    (hgs : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g))
    (hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ))
    [IsLocalRing (Module.End A Z)] [FiniteDimensional k E] :
    ∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ) := by
  intro φ hφ
  have hA : ∀ e, FDMod.lin g e = 0 → FDMod.lin g (FDMod.lin φ e) = 0 := fun e he ↦ by
    rw [← LinearMap.mem_ker, ← hex] at he
    obtain ⟨k', rfl⟩ := he
    rw [show FDMod.lin φ (FDMod.lin f k') = FDMod.lin f k' from LinearMap.congr_fun (congrArg FDMod.lin hφ) k',
      ← LinearMap.mem_ker, ← hex]
    exact LinearMap.mem_range_self _ _
  have hB : ∀ e, FDMod.lin g e = 0 → FDMod.lin g (FDMod.lin (𝟙 E) e) = 0 := fun e he ↦ he
  have hψ := roundTrip_bijective hf hfi hgs hex hgs hex φ (𝟙 E) hφ (Category.comp_id f) hA hB
  let ψ : Z ⟶ Z := (FDMod.ofLin (FDMod.lin (indMap g hgs g (𝟙 E) hB) ∘ₗ FDMod.lin (indMap g hgs g φ hA)))
  have hψg : ∀ e, FDMod.lin ψ (FDMod.lin g e) = FDMod.lin g (FDMod.lin φ e) := fun e ↦ by
    change FDMod.lin (indMap g hgs g (𝟙 E) hB) (FDMod.lin (indMap g hgs g φ hA) (FDMod.lin g e)) = _
    rw [indMap_spec, indMap_spec]
    rfl
  have hg' := isRightAS_comp_iso hg (invOf ψ hψ) (LinearEquiv.ofBijective _ hψ).symm.bijective
  obtain ⟨t, ht⟩ := hg.2 E (g ≫ invOf ψ hψ) hg'.1
  have hφt : (φ ≫ t) ≫ g = g := by
    apply FDMod.hom_ext; apply LinearMap.ext; intro e
    have h1 : FDMod.lin g (FDMod.lin t (FDMod.lin φ e)) =
        FDMod.lin (invOf ψ hψ) (FDMod.lin g (FDMod.lin φ e)) := LinearMap.congr_fun (congrArg FDMod.lin ht) _
    change FDMod.lin g (FDMod.lin t (FDMod.lin φ e)) = FDMod.lin g e
    rw [h1, ← hψg]
    exact LinearMap.congr_fun (congrArg FDMod.lin ((comp_invOf ψ hψ))) _
  have hb := hmin _ hφt
  have hinj : Function.Injective (FDMod.lin φ) := fun x y hxy ↦ hb.1 (by
    change FDMod.lin t (FDMod.lin φ x) = FDMod.lin t (FDMod.lin φ y)
    rw [hxy])
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (FDMod.lin φ).restrictScalars k)).1 hinj⟩

end LargeIndecomposable.AR
