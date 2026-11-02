module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.LeftAS

/-!
# Auslander–Reiten sequences

Let `g : E → Z` be right almost split and right minimal (every `φ` with `g φ = g` is bijective).
Then the inclusion of `ker g` into `E` is left almost split (`isLeftAS_ker`): for `u : ker g → W`,
the pushout of the sequence along `u` either splits, and `u` extends to `E`, or its projection to
`Z` factors through `g`, which makes `u` a split monomorphism by right minimality. No transpose is
needed. If `Z` is not a summand of a free module, `g` is surjective (`surjective_of_rightAS`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- A quotient of a finite-dimensional module, as an object. -/
abbrev FDMod.ofQuot (E : FDMod k A) (U : Submodule A E) : FDMod k A where
  carrier := E ⧸ U
  isFD := Module.Finite.of_surjective (U.mkQ.restrictScalars k) (Submodule.Quotient.mk_surjective U)

/-- The product of two objects. -/
abbrev FDMod.prod (W E : FDMod k A) : FDMod k A where
  carrier := W × E

/-- A finite free module, as an object. -/
abbrev FDMod.free [FiniteDimensional k A] (n : ℕ) : FDMod k A where
  carrier := Fin n → A

/-- **A right almost split map onto a module that is not a summand of a free module is
surjective.** -/
theorem surjective_of_rightAS [FiniteDimensional k A] {E Z : FDMod k A} {g : E ⟶ Z}
    (hg : IsRightAS g) (hZ : ¬IsFreeSummand A Z) (P : FreePres A Z) :
    Function.Surjective (FDMod.lin g) := by
  let π : (Fin P.n₀ → A) →ₗ[A] Z :=
    { toFun := fun p ↦ ∑ j, p j • P.z j
      map_add' := fun p q ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a p ↦ by simp [Finset.smul_sum, mul_smul] }
  obtain ⟨v, hv⟩ := hg.2 (FDMod.free P.n₀) (FDMod.ofLin π) fun ⟨s, hs⟩ ↦ hZ ⟨P.n₀, (FDMod.lin s), π, ((FDMod.comp_eq_id_iff _ _).1 hs)⟩
  intro z
  obtain ⟨p, hp⟩ := P.span z
  exact ⟨FDMod.lin v p, (LinearMap.congr_fun (congrArg FDMod.lin hv) p).trans hp⟩

/-- A surjection splits if an endomorphism of its source fixes it and kills its kernel. -/
lemma split_of_endo' {E X Z : Type*} [AddCommGroup E] [Module A E] [AddCommGroup X] [Module A X]
    [AddCommGroup Z] [Module A Z] (i : X →ₗ[A] E) (p : E →ₗ[A] Z) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) (e : E →ₗ[A] E) (he1 : ∀ x, p (e x) = p x)
    (he2 : ∀ m, e (i m) = 0) : ∃ s : Z →ₗ[A] E, p ∘ₗ s = LinearMap.id := by
  have hker : LinearMap.ker p ≤ LinearMap.ker e := by
    intro x hx
    rw [← hex] at hx
    obtain ⟨m, rfl⟩ := hx
    exact he2 m
  let q := LinearMap.quotKerEquivOfSurjective p hp
  refine ⟨((LinearMap.ker p).liftQ e hker) ∘ₗ q.symm.toLinearMap, ?_⟩
  ext m
  obtain ⟨x, rfl⟩ := hp m
  have hq : q.symm (p x) = Submodule.Quotient.mk x := q.symm_apply_eq.2 rfl
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hq,
    Submodule.liftQ_apply, LinearMap.id_coe, id_eq]
  exact he1 x

/-- **The inclusion of the kernel of a surjective right minimal right almost split map is left
almost split.** -/
theorem isLeftAS_ker {E Z : FDMod k A} {g : E ⟶ Z} (hg : IsRightAS g)
    (hsurj : Function.Surjective (FDMod.lin g))
    (hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ)) :
    IsLeftAS (show FDMod.ofSub (LinearMap.ker (FDMod.lin g)) ⟶ E from
      (FDMod.ofLin ((LinearMap.ker (FDMod.lin g)).subtype))) := by
  set K := LinearMap.ker (FDMod.lin g) with hK
  have hexK : LinearMap.range K.subtype = LinearMap.ker (FDMod.lin g) := Submodule.range_subtype K
  refine ⟨fun ⟨r, hr⟩ ↦ hg.1 ?_, fun W u hu ↦ ?_⟩
  · obtain ⟨s, hs⟩ := split_of_endo' K.subtype (FDMod.lin g) hsurj hexK
      (LinearMap.id - K.subtype ∘ₗ FDMod.lin r)
      (fun x ↦ by
        have : FDMod.lin g (K.subtype (FDMod.lin r x)) = 0 := (FDMod.lin r x).2
        simp [this])
      (fun m ↦ by
        have : FDMod.lin r (K.subtype m) = m := LinearMap.congr_fun (congrArg FDMod.lin hr) m
        change (K.subtype m : E) - K.subtype (FDMod.lin r (K.subtype m)) = 0
        rw [this, sub_self])
    exact ⟨(FDMod.ofLin s), ((FDMod.comp_eq_id_iff _ _).2 hs)⟩
  · -- the pushout `P = (W × E) / {(u x, -x)}`
    let N : Submodule A (W × E) := LinearMap.range (LinearMap.prod (FDMod.lin u) (-K.subtype))
    let P := FDMod.ofQuot (FDMod.prod W E) N
    let j : W →ₗ[A] P := N.mkQ ∘ₗ LinearMap.inl A W E
    let v' : E →ₗ[A] P := N.mkQ ∘ₗ LinearMap.inr A W E
    have hN : N ≤ LinearMap.ker (FDMod.lin g ∘ₗ LinearMap.snd A W E) := by
      rintro _ ⟨x, rfl⟩
      change FDMod.lin g (-(x : E)) = 0
      rw [map_neg, x.2, neg_zero]
    let g' : P →ₗ[A] Z := N.liftQ (FDMod.lin g ∘ₗ LinearMap.snd A W E) hN
    have hg'j : ∀ w, g' (j w) = 0 := fun w ↦ by
      change FDMod.lin g 0 = 0; exact map_zero _
    have hg'v : ∀ e, g' (v' e) = FDMod.lin g e := fun e ↦ rfl
    have hvj : ∀ x : K, v' x = j (FDMod.lin u x) := fun x ↦ by
      change N.mkQ (0, (x : E)) = N.mkQ (FDMod.lin u x, 0)
      rw [eq_comm, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, by simp⟩
    have hjinj : Function.Injective j := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      change Submodule.Quotient.mk (w, (0 : E)) = (0 : (W × E) ⧸ N) at hw
      rw [Submodule.Quotient.mk_eq_zero] at hw
      obtain ⟨x, hx⟩ := hw
      have h1 : -(x : E) = 0 := congrArg Prod.snd hx
      have hx0 : x = 0 := Subtype.ext (neg_eq_zero.1 h1)
      have h2 : FDMod.lin u x = w := congrArg Prod.fst hx
      rw [← h2, hx0, map_zero]
    by_cases hs : ∃ s : Z →ₗ[A] P, g' ∘ₗ s = LinearMap.id
    · obtain ⟨s, hs⟩ := hs
      -- a retraction of `j`
      have hmem : ∀ p : P, p - s (g' p) ∈ LinearMap.range j := by
        intro p
        obtain ⟨⟨w, e⟩, rfl⟩ := Submodule.mkQ_surjective N p
        have hd : g' (N.mkQ (w, e) - s (g' (N.mkQ (w, e)))) = 0 := by
          rw [map_sub, show g' (s _) = _ from LinearMap.congr_fun hs _, LinearMap.id_apply, sub_self]
        obtain ⟨⟨w', e'⟩, he⟩ := Submodule.mkQ_surjective N (N.mkQ (w, e) - s (g' (N.mkQ (w, e))))
        rw [← he] at hd ⊢
        have he' : FDMod.lin g e' = 0 := hd
        refine ⟨w' + FDMod.lin u ⟨e', he'⟩, ?_⟩
        rw [map_add, ← hvj ⟨e', he'⟩]
        change N.mkQ (w', 0) + N.mkQ (0, e') = N.mkQ (w', e')
        rw [← map_add]
        simp
      let r : P →ₗ[A] W := (LinearEquiv.ofInjective j hjinj).symm.toLinearMap ∘ₗ
        LinearMap.codRestrict (LinearMap.range j) (LinearMap.id - s ∘ₗ g') hmem
      have hrj : ∀ w, r (j w) = w := fun w ↦ by
        change (LinearEquiv.ofInjective j hjinj).symm ⟨j w - s (g' (j w)), _⟩ = w
        rw [LinearEquiv.symm_apply_eq]
        apply Subtype.ext
        change j w - s (g' (j w)) = j w
        rw [hg'j, map_zero, sub_zero]
      refine ⟨(FDMod.ofLin (r ∘ₗ v')), FDMod.hom_ext (LinearMap.ext fun x ↦ ?_)⟩
      change r (v' x) = FDMod.lin u x
      rw [hvj, hrj]
    · obtain ⟨h, hh⟩ := hg.2 P (FDMod.ofLin g') fun ⟨s, hs'⟩ ↦ hs ⟨(FDMod.lin s), ((FDMod.comp_eq_id_iff _ _).1 hs')⟩
      have hhv : ∀ e, FDMod.lin g (FDMod.lin h (v' e)) = FDMod.lin g e := fun e ↦ by
        rw [← hg'v]; exact LinearMap.congr_fun (congrArg FDMod.lin hh) (v' e)
      have hψ := hmin (show E ⟶ E from (FDMod.ofLin (FDMod.lin h ∘ₗ v'))) (FDMod.hom_ext ((LinearMap.ext hhv)))
      have hmemK : ∀ w, FDMod.lin h (j w) ∈ K := fun w ↦ by
        change FDMod.lin g (FDMod.lin h (j w)) = 0
        rw [show FDMod.lin g (FDMod.lin h (j w)) = g' (j w) from LinearMap.congr_fun (congrArg FDMod.lin hh) (j w),
          hg'j]
      haveI : FiniteDimensional k K := inferInstanceAs (FiniteDimensional k (K.restrictScalars k))
      let hj : W →ₗ[A] K := LinearMap.codRestrict K (FDMod.lin h ∘ₗ j) hmemK
      let φ : K →ₗ[A] K := hj ∘ₗ FDMod.lin u
      have hφ : ∀ x : K, (φ x : E) = FDMod.lin h (v' x) := fun x ↦ by
        change FDMod.lin h (j (FDMod.lin u x)) = _
        rw [hvj]
      have hφinj : Function.Injective φ := fun x y hxy ↦ by
        have := congrArg Subtype.val hxy
        rw [hφ, hφ] at this
        exact Subtype.ext (hψ.1 this)
      have hφbij : Function.Bijective φ :=
        ⟨hφinj, (LinearMap.injective_iff_surjective (f := φ.restrictScalars k)).1 hφinj⟩
      let e := LinearEquiv.ofBijective φ hφbij
      refine absurd ⟨(FDMod.ofLin (e.symm.toLinearMap ∘ₗ hj)), (FDMod.hom_ext (LinearMap.ext fun x ↦ ?_))⟩ hu
      change e.symm (hj (FDMod.lin u x)) = x
      rw [LinearEquiv.symm_apply_eq]
      rfl

/-- **The source of a left almost split map is indecomposable.** -/
theorem isIndecMod_of_leftAS {X E : FDMod k A} {f : X ⟶ E} (hf : IsLeftAS f) : IsIndecMod A X := by
  intro U V h
  by_contra hne
  push Not at hne
  obtain ⟨hU, hV⟩ := hne
  let e := Submodule.prodEquivOfIsCompl U V h
  let πU : X →ₗ[A] U := LinearMap.fst A U V ∘ₗ e.symm.toLinearMap
  let πV : X →ₗ[A] V := LinearMap.snd A U V ∘ₗ e.symm.toLinearMap
  have hnsU : ¬∃ r : FDMod.ofSub U ⟶ X, (show X ⟶ FDMod.ofSub U from (FDMod.ofLin πU)) ≫ r = 𝟙 X := by
    rintro ⟨r, hr⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    have h1 : πU v = 0 := by
      have := Submodule.prodEquivOfIsCompl_symm_apply_right U V h ⟨v, hv⟩
      change (e.symm ((⟨v, hv⟩ : V) : X)).1 = 0
      rw [this]
    apply hv0
    have := LinearMap.congr_fun (congrArg FDMod.lin hr) v
    change FDMod.lin r (πU v) = v at this
    rw [h1, map_zero] at this
    exact this.symm
  have hnsV : ¬∃ r : FDMod.ofSub V ⟶ X, (show X ⟶ FDMod.ofSub V from (FDMod.ofLin πV)) ≫ r = 𝟙 X := by
    rintro ⟨r, hr⟩
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have h1 : πV u = 0 := by
      have := Submodule.prodEquivOfIsCompl_symm_apply_left U V h ⟨u, hu⟩
      change (e.symm ((⟨u, hu⟩ : U) : X)).2 = 0
      rw [this]
    apply hu0
    have := LinearMap.congr_fun (congrArg FDMod.lin hr) u
    change FDMod.lin r (πV u) = u at this
    rw [h1, map_zero] at this
    exact this.symm
  obtain ⟨a, ha⟩ := hf.2 (FDMod.ofSub U) (FDMod.ofLin πU) hnsU
  obtain ⟨b, hb⟩ := hf.2 (FDMod.ofSub V) (FDMod.ofLin πV) hnsV
  refine hf.1 ⟨(FDMod.ofLin (show E →ₗ[A] X from U.subtype ∘ₗ FDMod.lin a + V.subtype ∘ₗ FDMod.lin b)), ?_⟩
  apply FDMod.hom_ext; apply LinearMap.ext
  intro x
  have ha' : FDMod.lin a (FDMod.lin f x) = πU x := LinearMap.congr_fun (congrArg FDMod.lin ha) x
  have hb' : FDMod.lin b (FDMod.lin f x) = πV x := LinearMap.congr_fun (congrArg FDMod.lin hb) x
  change (U.subtype (FDMod.lin a (FDMod.lin f x)) + V.subtype (FDMod.lin b (FDMod.lin f x))) = x
  rw [ha', hb']
  change ((e.symm x).1 : X) + ((e.symm x).2 : X) = x
  rw [← Submodule.coe_prodEquivOfIsCompl' U V h, LinearEquiv.apply_symm_apply]

/-- **Auslander–Reiten sequences.** For `Z` with local endomorphism ring that is not a summand of
a free module, there is an exact sequence `0 → X → E → Z → 0` with `E → Z` right almost split and
right minimal, `X → E` left almost split, and `X` nonzero indecomposable. -/
theorem exists_arSeq [FiniteDimensional k A] (Z : FDMod k A) [IsLocalRing (Module.End A Z)]
    (hZ : ¬IsFreeSummand A Z) :
    ∃ (E : FDMod k A) (g : E ⟶ Z), IsRightAS g ∧ Function.Surjective (FDMod.lin g) ∧
      (∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ)) ∧
      IsLeftAS (show FDMod.ofSub (LinearMap.ker (FDMod.lin g)) ⟶ E from
        (FDMod.ofLin ((LinearMap.ker (FDMod.lin g)).subtype))) ∧
      IsIndecMod A (LinearMap.ker (FDMod.lin g)) ∧ Nontrivial (LinearMap.ker (FDMod.lin g)) := by
  obtain ⟨E, g, hg, hmin⟩ := exists_minimal_rightAS Z
  obtain ⟨P⟩ := FreePres.exists k A Z
  have hsurj := surjective_of_rightAS hg hZ P
  have hleft := isLeftAS_ker hg hsurj hmin
  refine ⟨E, g, hg, hsurj, hmin, hleft, isIndecMod_of_leftAS hleft, ?_⟩
  by_contra htr
  rw [not_nontrivial_iff_subsingleton] at htr
  have hinj : Function.Injective (FDMod.lin g) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker (FDMod.lin g)) 0
    exact congrArg Subtype.val this
  let eg := LinearEquiv.ofBijective (FDMod.lin g) ⟨hinj, hsurj⟩
  exact hg.1 ⟨(FDMod.ofLin eg.symm.toLinearMap), FDMod.hom_ext (LinearMap.ext fun z ↦ eg.apply_symm_apply z)⟩

end LargeIndecomposable.AR
