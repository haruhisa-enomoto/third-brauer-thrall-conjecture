module

public import LargeIndecomposable.AuslanderReiten.Lengths.BSet

/-!
# Transfers of irreducible maps

Irreducibility is preserved by composing with isomorphisms (`IsIrr.comp_iso`, `IsIrr.iso_comp`)
and descends along restriction to a quotient algebra (`IsIrr.unres`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The inverse of a bijective morphism. -/
def invOf {X Y : FDMod k A} (g : X ⟶ Y) (hg : Function.Bijective (FDMod.lin g)) : Y ⟶ X :=
  (FDMod.ofLin ((LinearEquiv.ofBijective (FDMod.lin g) hg).symm.toLinearMap))

lemma invOf_comp {X Y : FDMod k A} (g : X ⟶ Y) (hg : Function.Bijective (FDMod.lin g)) :
    invOf g hg ≫ g = 𝟙 Y :=
  (FDMod.hom_ext (LinearMap.ext fun y ↦ (LinearEquiv.ofBijective (FDMod.lin g) hg).apply_symm_apply y))

lemma comp_invOf {X Y : FDMod k A} (g : X ⟶ Y) (hg : Function.Bijective (FDMod.lin g)) :
    g ≫ invOf g hg = 𝟙 X :=
  (FDMod.hom_ext (LinearMap.ext fun x ↦ (LinearEquiv.ofBijective (FDMod.lin g) hg).symm_apply_apply x))

/-- **Irreducibility survives composing with an isomorphism on the target.** -/
lemma IsIrr.comp_iso {X Y Y' : FDMod k A} {f : X ⟶ Y} (hf : IsIrr f) (g : Y ⟶ Y')
    (hg : Function.Bijective (FDMod.lin g)) : IsIrr (f ≫ g) := by
  have h1 := invOf_comp g hg
  have h2 := comp_invOf g hg
  refine ⟨fun ⟨r, hr⟩ ↦ hf.1 ⟨g ≫ r, by rw [← Category.assoc, hr]⟩,
    fun ⟨s, hs⟩ ↦ hf.2.1 ⟨g ≫ s, ?_⟩, fun W a b hab ↦ ?_⟩
  · have : s ≫ f = invOf g hg := by
      rw [← Category.comp_id (s ≫ f), ← h2, ← Category.assoc, Category.assoc s, hs,
        Category.id_comp]
    rw [Category.assoc, this, h2]
  · rcases hf.2.2 W a (b ≫ invOf g hg) (by rw [← Category.assoc, hab, Category.assoc, h2,
      Category.comp_id]) with h | ⟨s, hs⟩
    · exact Or.inl h
    · refine Or.inr ⟨invOf g hg ≫ s, ?_⟩
      have : s ≫ b = g := by
        rw [← Category.comp_id (s ≫ b), ← h1, ← Category.assoc, Category.assoc s, hs,
          Category.id_comp]
      rw [Category.assoc, this, h1]

/-- **Irreducibility survives composing with an isomorphism on the source.** -/
lemma IsIrr.iso_comp {X' X Y : FDMod k A} {f : X ⟶ Y} (hf : IsIrr f) (h : X' ⟶ X)
    (hh : Function.Bijective (FDMod.lin h)) : IsIrr (h ≫ f) := by
  have h1 := invOf_comp h hh
  have h2 := comp_invOf h hh
  refine ⟨fun ⟨r, hr⟩ ↦ hf.1 ⟨r ≫ h, ?_⟩, fun ⟨s, hs⟩ ↦ hf.2.1 ⟨s ≫ h, by
    rw [Category.assoc, hs]⟩, fun W a b hab ↦ ?_⟩
  · have : f ≫ r = invOf h hh := by
      rw [← Category.id_comp (f ≫ r), ← h1, Category.assoc, ← Category.assoc h f, hr,
        Category.comp_id]
    rw [← Category.assoc, this, h1]
  · rcases hf.2.2 W (invOf h hh ≫ a) b (by rw [Category.assoc, hab, ← Category.assoc, h1,
      Category.id_comp]) with ⟨r, hr⟩ | h3
    · refine Or.inl ⟨r ≫ invOf h hh, ?_⟩
      have : a ≫ r = h := by
        rw [← Category.id_comp (a ≫ r), ← h2, Category.assoc, ← Category.assoc _ a, hr,
          Category.comp_id]
      rw [← Category.assoc, this, h2]
    · exact Or.inr h3

/-- **Components of minimal left almost split maps are irreducible.** -/
theorem isIrr_summandL {X E : FDMod k A} {f : X ⟶ E} (hf : IsLeftAS f)
    (hmin : ∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ)) (hX : IndNT X)
    (d : Decomp E) (i : d.ι) : IsIrr (f ≫ d.proj i) := by
  classical
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    simpa using LinearMap.congr_fun d.sum_id x
  have hretr : ∀ j u, FDMod.lin (d.proj j) (FDMod.lin (d.inc j) u) = u := fun j u ↦
    LinearMap.congr_fun (d.retr j) u
  have horth : ∀ j l, j ≠ l → ∀ u, FDMod.lin (d.proj l) (FDMod.lin (d.inc j) u) = 0 :=
    fun j l h u ↦ LinearMap.congr_fun (d.orth j l h) u
  refine ⟨fun ⟨r, hr⟩ ↦ hf.1 ⟨d.proj i ≫ r, by rw [← Category.assoc, hr]⟩,
    fun ⟨s, hs⟩ ↦ ?_, fun W a b hab ↦ ?_⟩
  · have hb := bijective_of_split hX.1 (d.nt i) (f ≫ d.proj i) s
      (LinearMap.ext fun u ↦ LinearMap.congr_fun ((FDMod.comp_eq_id_iff _ _).1 (hs)) u)
    exact hf.1 ⟨d.proj i ≫ invOf _ hb, by rw [← Category.assoc, comp_invOf]⟩
  · by_cases ha : SplitMono a
    · exact Or.inl ha
    right
    obtain ⟨c, hc⟩ := hf.2 W a ha
    have hbc : ∀ x, FDMod.lin b (FDMod.lin c (FDMod.lin f x)) =
        FDMod.lin (d.proj i) (FDMod.lin f x) := fun x ↦ by
      have h1 : FDMod.lin c (FDMod.lin f x) = FDMod.lin a x := LinearMap.congr_fun (congrArg FDMod.lin hc) x
      rw [h1]; exact LinearMap.congr_fun (congrArg FDMod.lin (hab)) x
    let φ : E →ₗ[A] E := FDMod.lin (d.inc i) ∘ₗ FDMod.lin b ∘ₗ FDMod.lin c +
      ∑ j ∈ Finset.univ.erase i, FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
    have hφ : f ≫ (show E ⟶ E from (FDMod.ofLin (φ))) = f := by
      apply FDMod.hom_ext; apply LinearMap.ext; intro x
      change φ (FDMod.lin f x) = FDMod.lin f x
      conv_rhs => rw [← hsum (FDMod.lin f x), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, hbc]
    have hφb := hmin _ hφ
    have hprojφ : ∀ j, j ≠ i → ∀ e, FDMod.lin (d.proj j) (φ e) = FDMod.lin (d.proj j) e := by
      intro j hj e
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, map_add, map_sum, horth i j (Ne.symm hj), zero_add]
      rw [Finset.sum_eq_single j]
      · rw [hretr]
      · intro l _ hl; rw [horth l j hl]
      · intro h; exact absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) h
    have hprojφi : ∀ e, FDMod.lin (d.proj i) (φ e) = FDMod.lin b (FDMod.lin c e) := by
      intro e
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, map_add, map_sum, hretr]
      rw [Finset.sum_eq_zero, add_zero]
      intro l hl; rw [horth l i (Finset.ne_of_mem_erase hl)]
    let τ : d.obj i →ₗ[A] d.obj i := FDMod.lin b ∘ₗ FDMod.lin c ∘ₗ FDMod.lin (d.inc i)
    have hτs : Function.Surjective τ := by
      intro w
      obtain ⟨e, he⟩ := hφb.2 (FDMod.lin (d.inc i) w)
      replace he : φ e = FDMod.lin (d.inc i) w := he
      have hej : ∀ j, j ≠ i → FDMod.lin (d.proj j) e = 0 := fun j hj ↦ by
        rw [← hprojφ j hj, he, horth i j (Ne.symm hj)]
      have he' : e = FDMod.lin (d.inc i) (FDMod.lin (d.proj i) e) := by
        conv_lhs => rw [← hsum e, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        rw [Finset.sum_eq_zero, add_zero]
        intro j hj; rw [hej j (Finset.ne_of_mem_erase hj), map_zero]
      refine ⟨FDMod.lin (d.proj i) e, ?_⟩
      change FDMod.lin b (FDMod.lin c (FDMod.lin (d.inc i) (FDMod.lin (d.proj i) e))) = w
      rw [← he', ← hprojφi, he, hretr]
    have hτb : Function.Bijective τ :=
      ⟨(LinearMap.injective_iff_surjective (f := τ.restrictScalars k)).2 hτs, hτs⟩
    let eτ := LinearEquiv.ofBijective τ hτb
    refine ⟨(FDMod.ofLin (show d.obj i →ₗ[A] W from FDMod.lin c ∘ₗ FDMod.lin (d.inc i) ∘ₗ eτ.symm.toLinearMap)),
      (FDMod.hom_ext (LinearMap.ext fun w ↦ ?_))⟩
    change τ (eτ.symm w) = w
    exact eτ.apply_symm_apply w

section Res

variable {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'} (hφ : Function.Surjective φ)

include hφ in
/-- **Irreducible maps between restrictions are irreducible over the quotient.** -/
lemma IsIrr.unres {X Y : FDMod k A'} {f : X ⟶ Y} (hf : IsIrr (resHom φ f)) : IsIrr f := by
  refine ⟨fun h ↦ hf.1 ((splitMono_res_iff hφ f).2 h), fun ⟨s, hs⟩ ↦ hf.2.1 ⟨resHom φ s,
    (FDMod.hom_ext (LinearMap.ext fun y ↦ LinearMap.congr_fun (congrArg FDMod.lin (hs)) (toX y)))⟩, fun W a b hab ↦ ?_⟩
  rcases hf.2.2 (resFD φ W) (resHom φ a) (resHom φ b) (by rw [← hab]; rfl) with h | ⟨s, hs⟩
  · exact Or.inl ((splitMono_res_iff hφ a).1 h)
  · exact Or.inr ⟨unresHom hφ s, (FDMod.hom_ext (LinearMap.ext fun y ↦ LinearMap.congr_fun (congrArg FDMod.lin (hs)) (ofX y)))⟩

end Res

end LargeIndecomposable.AR
