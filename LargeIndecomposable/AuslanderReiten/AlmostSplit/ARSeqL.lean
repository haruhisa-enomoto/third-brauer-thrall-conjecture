module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.Preproj

/-!
# Auslander–Reiten sequences starting at a module

Left minimal left almost split maps exist (`exists_minimal_leftAS`). If `U` admits a
non-split monomorphism (`U` is not injective), a left almost split map out of `U` is injective
(`injective_of_leftAS`). For an injective left minimal left almost split `f : U → E`, the cokernel
map `E → E / f U` is right almost split (`isRightAS_coker`, by a pullback argument) and its target
is nonzero indecomposable (`isIndecMod_of_rightAS`). This is the sequence
`0 → U → E → τ⁻¹U → 0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `f` corestricted to the range of an endomorphism `φ` with `f φ = f`. -/
lemma isLeftAS_range {U E : FDMod k A} {f : U ⟶ E} (hf : IsLeftAS f) (φ : E ⟶ E)
    (hφ : f ≫ φ = f) :
    IsLeftAS (show U ⟶ FDMod.ofSub (LinearMap.range (FDMod.lin φ)) from
      (FDMod.ofLin (LinearMap.codRestrict _ (FDMod.lin f) fun u ↦ LinearMap.mem_range.2 ⟨FDMod.lin f u,
        (LinearMap.congr_fun (congrArg FDMod.lin hφ) u : FDMod.lin φ (FDMod.lin f u) = FDMod.lin f u)⟩))) := by
  refine ⟨fun ⟨r, hr⟩ ↦ hf.1 ⟨show E ⟶ U from (FDMod.ofLin (FDMod.lin r ∘ₗ
    (LinearMap.codRestrict _ (FDMod.lin φ) fun e ↦ LinearMap.mem_range_self _ e))), ?_⟩,
    fun W u' hu ↦ ?_⟩
  · apply FDMod.hom_ext; apply LinearMap.ext; intro u
    have h1 := LinearMap.congr_fun (congrArg FDMod.lin hr) u
    have hx : FDMod.lin φ (FDMod.lin f u) = FDMod.lin f u := LinearMap.congr_fun (congrArg FDMod.lin hφ) u
    change FDMod.lin r ⟨FDMod.lin φ (FDMod.lin f u), LinearMap.mem_range_self _ _⟩ = u
    have hy : (⟨FDMod.lin φ (FDMod.lin f u), LinearMap.mem_range_self _ _⟩ :
        LinearMap.range (FDMod.lin φ)) = ⟨FDMod.lin f u, LinearMap.mem_range.2 ⟨FDMod.lin f u, hx⟩⟩ :=
      Subtype.ext hx
    rw [hy]
    exact h1
  · obtain ⟨v, hv⟩ := hf.2 W u' hu
    refine ⟨show FDMod.ofSub (LinearMap.range (FDMod.lin φ)) ⟶ W from
      (FDMod.ofLin (FDMod.lin v ∘ₗ (LinearMap.range (FDMod.lin φ)).subtype)), ?_⟩
    rw [← hv]
    rfl

/-- **Minimal left almost split maps exist.** -/
theorem exists_minimal_leftAS [FiniteDimensional k A] (U : FDMod k A)
    [IsLocalRing (Module.End A U)] :
    ∃ (E : FDMod k A) (f : U ⟶ E), IsLeftAS f ∧
      ∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ) := by
  classical
  have hex : ∃ n, ∃ (E : FDMod k A) (f : U ⟶ E), IsLeftAS f ∧ finrank k E = n := by
    obtain ⟨E, f, hf⟩ := FDMod.exists_leftAS U
    exact ⟨_, E, f, hf, rfl⟩
  obtain ⟨E, f, hf, hn⟩ := Nat.find_spec hex
  refine ⟨E, f, hf, fun φ hφ ↦ ?_⟩
  have hR := isLeftAS_range hf φ hφ
  have hle := Nat.find_min' hex ⟨_, _, hR, rfl⟩
  rw [← hn] at hle
  have hsurj : Function.Surjective (FDMod.lin φ) := by
    have hrank : finrank k ((LinearMap.range (FDMod.lin φ)).restrictScalars k) = finrank k E :=
      le_antisymm (Submodule.finrank_le _) hle
    have htop : (LinearMap.range (FDMod.lin φ)).restrictScalars k = ⊤ :=
      Submodule.eq_top_of_finrank_eq hrank
    intro y
    have : y ∈ (LinearMap.range (FDMod.lin φ)).restrictScalars k := by rw [htop]; trivial
    exact this
  have hinj : Function.Injective ((FDMod.lin φ).restrictScalars k) :=
    LinearMap.injective_iff_surjective.2 hsurj
  exact ⟨hinj, hsurj⟩

/-- **A left almost split map out of a non-injective module is injective.** -/
theorem injective_of_leftAS {U E W : FDMod k A} {f : U ⟶ E} (hf : IsLeftAS f) (ι : U ⟶ W)
    (hι : Function.Injective (FDMod.lin ι)) (hns : ¬∃ r : W ⟶ U, ι ≫ r = 𝟙 U) :
    Function.Injective (FDMod.lin f) := by
  obtain ⟨v, hv⟩ := hf.2 W ι hns
  intro x y hxy
  apply hι
  rw [← hv]
  change FDMod.lin v (FDMod.lin f x) = FDMod.lin v (FDMod.lin f y)
  rw [hxy]

/-- **The target of a right almost split map is indecomposable.** -/
theorem isIndecMod_of_rightAS {E V : FDMod k A} {g : E ⟶ V} (hg : IsRightAS g) :
    IsIndecMod A V := by
  intro V₁ V₂ h
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  let e := Submodule.prodEquivOfIsCompl V₁ V₂ h
  let π₁ : V →ₗ[A] V₁ := LinearMap.fst A V₁ V₂ ∘ₗ e.symm.toLinearMap
  let π₂ : V →ₗ[A] V₂ := LinearMap.snd A V₁ V₂ ∘ₗ e.symm.toLinearMap
  have hns₁ : ¬∃ s : V ⟶ FDMod.ofSub V₁, s ≫ (show FDMod.ofSub V₁ ⟶ V from (FDMod.ofLin V₁.subtype)) = 𝟙 V := by
    rintro ⟨s, hs⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
    have hmem : ((FDMod.lin s v : V₁) : V) = v := LinearMap.congr_fun (congrArg FDMod.lin hs) v
    have hv1 : v ∈ V₁ := hmem ▸ (FDMod.lin s v).2
    exact hv0 ((Submodule.mem_bot A).1 (h.disjoint.le_bot ⟨hv1, hv⟩))
  have hns₂ : ¬∃ s : V ⟶ FDMod.ofSub V₂, s ≫ (show FDMod.ofSub V₂ ⟶ V from (FDMod.ofLin V₂.subtype)) = 𝟙 V := by
    rintro ⟨s, hs⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    have hmem : ((FDMod.lin s v : V₂) : V) = v := LinearMap.congr_fun (congrArg FDMod.lin hs) v
    have hv2 : v ∈ V₂ := hmem ▸ (FDMod.lin s v).2
    exact hv0 ((Submodule.mem_bot A).1 (h.disjoint.le_bot ⟨hv, hv2⟩))
  obtain ⟨t₁, ht₁⟩ := hg.2 (FDMod.ofSub V₁) (FDMod.ofLin V₁.subtype) hns₁
  obtain ⟨t₂, ht₂⟩ := hg.2 (FDMod.ofSub V₂) (FDMod.ofLin V₂.subtype) hns₂
  refine hg.1 ⟨(FDMod.ofLin (show V →ₗ[A] E from FDMod.lin t₁ ∘ₗ π₁ + FDMod.lin t₂ ∘ₗ π₂)), ?_⟩
  apply FDMod.hom_ext; apply LinearMap.ext; intro v
  have h1' : ∀ x : V₁, FDMod.lin g (FDMod.lin t₁ x) = x := fun x ↦ LinearMap.congr_fun (congrArg FDMod.lin ht₁) x
  have h2' : ∀ x : V₂, FDMod.lin g (FDMod.lin t₂ x) = x := fun x ↦ LinearMap.congr_fun (congrArg FDMod.lin ht₂) x
  change FDMod.lin g (FDMod.lin t₁ (π₁ v) + FDMod.lin t₂ (π₂ v)) = v
  rw [map_add, h1', h2']
  change ((e.symm v).1 : V) + ((e.symm v).2 : V) = v
  rw [← Submodule.coe_prodEquivOfIsCompl' V₁ V₂ h, LinearEquiv.apply_symm_apply]

/-- **The cokernel map of an injective left minimal left almost split map is right almost
split.** -/
theorem isRightAS_coker {U E : FDMod k A} {f : U ⟶ E} (hf : IsLeftAS f)
    (hinj : Function.Injective (FDMod.lin f))
    (hmin : ∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ)) :
    IsRightAS (show E ⟶ FDMod.ofQuot E (LinearMap.range (FDMod.lin f)) from
      (FDMod.ofLin ((LinearMap.range (FDMod.lin f)).mkQ))) := by
  set R := LinearMap.range (FDMod.lin f) with hR
  let V := FDMod.ofQuot E R
  let g : E →ₗ[A] V := R.mkQ
  have hgsurj : Function.Surjective g := Submodule.mkQ_surjective R
  have hgf : ∀ u, g (FDMod.lin f u) = 0 := fun u ↦
    (Submodule.Quotient.mk_eq_zero R).2 (LinearMap.mem_range_self _ u)
  let ef := LinearEquiv.ofInjective (FDMod.lin f) hinj
  have hef : ∀ u, ef.symm ⟨FDMod.lin f u, LinearMap.mem_range_self _ u⟩ = u := fun u ↦ by
    rw [LinearEquiv.symm_apply_eq]; rfl
  refine ⟨fun ⟨s, hs⟩ ↦ hf.1 ?_, fun W w hw ↦ ?_⟩
  · -- a section of `g` gives a retraction of `f`
    have hmem : ∀ e, e - FDMod.lin s (g e) ∈ R := fun e ↦ by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      change g e - g (FDMod.lin s (g e)) = 0
      rw [show g (FDMod.lin s (g e)) = g e from LinearMap.congr_fun (congrArg FDMod.lin hs) (g e), sub_self]
    refine ⟨(FDMod.ofLin (show E →ₗ[A] U from ef.symm.toLinearMap ∘ₗ
      LinearMap.codRestrict R (LinearMap.id - FDMod.lin s ∘ₗ g) hmem)), (FDMod.hom_ext (LinearMap.ext fun u ↦ ?_))⟩
    change ef.symm ⟨FDMod.lin f u - FDMod.lin s (g (FDMod.lin f u)), _⟩ = u
    have : (⟨FDMod.lin f u - FDMod.lin s (g (FDMod.lin f u)), hmem _⟩ : R) =
        ⟨FDMod.lin f u, LinearMap.mem_range_self _ u⟩ := by
      apply Subtype.ext
      change FDMod.lin f u - FDMod.lin s (g (FDMod.lin f u)) = FDMod.lin f u
      rw [hgf, map_zero, sub_zero]
    rw [this, hef]
  · -- the pullback `{(x, e) | w x = g e}`
    let Pb : Submodule A (W × E) := LinearMap.ker (FDMod.lin w ∘ₗ LinearMap.fst A W E -
      g ∘ₗ LinearMap.snd A W E)
    have hPb : ∀ p : W × E, p ∈ Pb ↔ FDMod.lin w p.1 = g p.2 := fun p ↦ by
      simp [Pb, sub_eq_zero]
    let PbM := FDMod.ofSub (P := FDMod.prod W E) Pb
    let f' : U →ₗ[A] Pb := LinearMap.codRestrict Pb (LinearMap.inr A W E ∘ₗ FDMod.lin f)
      fun u ↦ (hPb _).2 (by simp [hgf])
    let p₁ : Pb →ₗ[A] W := LinearMap.fst A W E ∘ₗ Pb.subtype
    let p₂ : Pb →ₗ[A] E := LinearMap.snd A W E ∘ₗ Pb.subtype
    have hp : ∀ x : Pb, FDMod.lin w (p₁ x) = g (p₂ x) := fun x ↦ (hPb x).1 x.2
    by_cases hsplit : ∃ ρ : PbM ⟶ U, (show U ⟶ PbM from (FDMod.ofLin f')) ≫ ρ = 𝟙 U
    · obtain ⟨ρ, hρ⟩ := hsplit
      have hρ' : ∀ u, FDMod.lin ρ (f' u) = u := fun u ↦ LinearMap.congr_fun (congrArg FDMod.lin hρ) u
      let q : Pb →ₗ[A] E := p₂ - FDMod.lin f ∘ₗ FDMod.lin ρ
      have hp₁ : Function.Surjective p₁ := fun x ↦ by
        obtain ⟨e, he⟩ := hgsurj (FDMod.lin w x)
        exact ⟨⟨(x, e), (hPb _).2 he.symm⟩, rfl⟩
      have hker : LinearMap.ker p₁ ≤ LinearMap.ker q := by
        intro x hx
        have hx1 : (x : W × E).1 = 0 := hx
        have hg0 : g (x : W × E).2 = 0 := by
          have := hp x
          change FDMod.lin w (x : W × E).1 = g (x : W × E).2 at this
          rw [← this, hx1, map_zero]
        obtain ⟨u, hu⟩ : (x : W × E).2 ∈ R := (Submodule.Quotient.mk_eq_zero R).1 hg0
        have hxf : x = f' u := by
          apply Subtype.ext
          change (x : W × E) = (0, FDMod.lin f u)
          ext
          · exact hx1
          · exact hu.symm
        rw [LinearMap.mem_ker, hxf]
        change FDMod.lin f u - FDMod.lin f (FDMod.lin ρ (f' u)) = 0
        rw [hρ', sub_self]
      let e₁ := LinearMap.quotKerEquivOfSurjective p₁ hp₁
      let t : W →ₗ[A] E := (LinearMap.ker p₁).liftQ q hker ∘ₗ e₁.symm.toLinearMap
      refine ⟨(FDMod.ofLin t), (FDMod.hom_ext (LinearMap.ext fun x ↦ ?_))⟩
      obtain ⟨y, rfl⟩ := hp₁ x
      have he : e₁.symm (p₁ y) = Submodule.Quotient.mk y := e₁.symm_apply_eq.2 rfl
      change g (t (p₁ y)) = FDMod.lin w (p₁ y)
      simp only [t, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        Submodule.liftQ_apply]
      change g (p₂ y - FDMod.lin f (FDMod.lin ρ y)) = _
      rw [map_sub, hgf, sub_zero, hp]
    · exfalso
      obtain ⟨h, hh⟩ := hf.2 PbM (FDMod.ofLin f') hsplit
      have hh' : ∀ u, FDMod.lin h (FDMod.lin f u) = f' u := fun u ↦ LinearMap.congr_fun (congrArg FDMod.lin hh) u
      let ψ : E →ₗ[A] E := p₂ ∘ₗ FDMod.lin h
      have hfψ : f ≫ FDMod.ofLin ψ = f := FDMod.hom_ext <| LinearMap.ext fun u ↦ by
        change p₂ (FDMod.lin h (FDMod.lin f u)) = FDMod.lin f u
        rw [hh']; rfl
      have hψb := hmin _ hfψ
      -- `ψ` preserves `R`, and induces a bijection `ψ̄` of `V`
      have hRψ : R ≤ R.comap ψ := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u, (LinearMap.congr_fun (congrArg FDMod.lin hfψ) u).symm⟩
      let ψb : V →ₗ[A] V := R.mapQ R ψ hRψ
      have hψbg : ∀ e, ψb (g e) = g (ψ e) := fun e ↦ rfl
      have hψbs : Function.Surjective ψb := fun v ↦ by
        obtain ⟨e, rfl⟩ := hgsurj v
        obtain ⟨e', he'⟩ := hψb.2 e
        exact ⟨g e', by rw [hψbg, ← he']; rfl⟩
      have hψbb : Function.Bijective ψb :=
        ⟨(LinearMap.injective_iff_surjective (f := ψb.restrictScalars k)).2 hψbs, hψbs⟩
      -- `p₁ h` kills `R`
      have hR1 : R ≤ LinearMap.ker (p₁ ∘ₗ FDMod.lin h) := by
        rintro _ ⟨u, rfl⟩
        change p₁ (FDMod.lin h (FDMod.lin f u)) = 0
        rw [hh']; rfl
      let τ : V →ₗ[A] W := R.liftQ (p₁ ∘ₗ FDMod.lin h) hR1
      have hτ : ∀ e, FDMod.lin w (τ (g e)) = ψb (g e) := fun e ↦ by
        change FDMod.lin w (p₁ (FDMod.lin h e)) = g (ψ e)
        rw [hp]
        rfl
      let eψ := LinearEquiv.ofBijective ψb hψbb
      apply hw
      refine ⟨(FDMod.ofLin (show V →ₗ[A] W from τ ∘ₗ eψ.symm.toLinearMap)), (FDMod.hom_ext (LinearMap.ext fun v ↦ ?_))⟩
      change FDMod.lin w (τ (eψ.symm v)) = v
      obtain ⟨e, he⟩ := hgsurj (eψ.symm v)
      rw [← he, hτ, he]
      exact eψ.apply_symm_apply v

/-- **Auslander–Reiten sequences starting at a non-injective module**: for `U` with local
endomorphism ring admitting a non-split monomorphism, there is `0 → U → E → V → 0` with `f`
injective, left almost split and left minimal, `E → V` right almost split, and `V` nonzero
indecomposable (`V = τ⁻¹U`). -/
theorem exists_arSeqL [FiniteDimensional k A] (U : FDMod k A) [IsLocalRing (Module.End A U)]
    (W : FDMod k A) (ι : U ⟶ W) (hι : Function.Injective (FDMod.lin ι))
    (hns : ¬∃ r : W ⟶ U, ι ≫ r = 𝟙 U) :
    ∃ (E : FDMod k A) (f : U ⟶ E), IsLeftAS f ∧ Function.Injective (FDMod.lin f) ∧
      (∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ)) ∧
      IsRightAS (show E ⟶ FDMod.ofQuot E (LinearMap.range (FDMod.lin f)) from
        (FDMod.ofLin ((LinearMap.range (FDMod.lin f)).mkQ))) ∧
      IndNT (FDMod.ofQuot E (LinearMap.range (FDMod.lin f))) := by
  obtain ⟨E, f, hf, hmin⟩ := exists_minimal_leftAS U
  have hinj := injective_of_leftAS hf ι hι hns
  have hg := isRightAS_coker hf hinj hmin
  refine ⟨E, f, hf, hinj, hmin, hg, isIndecMod_of_rightAS hg, ?_⟩
  by_contra htr
  rw [not_nontrivial_iff_subsingleton] at htr
  have hsurj : Function.Surjective (FDMod.lin f) := fun e ↦ by
    have : (LinearMap.range (FDMod.lin f)).mkQ e = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  let ef := LinearEquiv.ofBijective (FDMod.lin f) ⟨hinj, hsurj⟩
  exact hf.1 ⟨(FDMod.ofLin ef.symm.toLinearMap), (FDMod.hom_ext (LinearMap.ext fun u ↦ ef.symm_apply_apply u))⟩

end LargeIndecomposable.AR
