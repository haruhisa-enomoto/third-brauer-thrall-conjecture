module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARSeq

/-!
# Irreducible maps

A map is irreducible when it is neither a split monomorphism nor a split epimorphism and every
factorization has a split mono first factor or a split epi second factor (`IsIrr`). An irreducible
map into the target of a right almost split map factors through it by a split mono
(`IsIrr.factor_rightAS`), and dually (`IsIrr.factor_leftAS`). The left map of an exact sequence
`0 → X → E → Z → 0` with left almost split `f` and `Z` local is irreducible (`isIrr_of_leftAS`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `f` is a split monomorphism. -/
def SplitMono {X Y : FDMod k A} (f : X ⟶ Y) : Prop := ∃ r : Y ⟶ X, f ≫ r = 𝟙 X

/-- `f` is a split epimorphism. -/
def SplitEpi {X Y : FDMod k A} (f : X ⟶ Y) : Prop := ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y

/-- An irreducible map. -/
def IsIrr {X Y : FDMod k A} (f : X ⟶ Y) : Prop :=
  ¬SplitMono f ∧ ¬SplitEpi f ∧
    ∀ (W : FDMod k A) (a : X ⟶ W) (b : W ⟶ Y), a ≫ b = f → SplitMono a ∨ SplitEpi b

/-- **An irreducible map factors through a right almost split map by a split mono.** -/
lemma IsIrr.factor_rightAS {X E Z : FDMod k A} {f : X ⟶ Z} (hf : IsIrr f) {g : E ⟶ Z}
    (hg : IsRightAS g) : ∃ v : X ⟶ E, v ≫ g = f ∧ SplitMono v := by
  obtain ⟨v, hv⟩ := hg.2 X f hf.2.1
  rcases hf.2.2 E v g hv with h | h
  · exact ⟨v, hv, h⟩
  · exact absurd h hg.1

/-- **An irreducible map factors through a left almost split map by a split epi.** -/
lemma IsIrr.factor_leftAS {X E Z : FDMod k A} {f : X ⟶ Z} (hf : IsIrr f) {g : X ⟶ E}
    (hg : IsLeftAS g) : ∃ v : E ⟶ Z, g ≫ v = f ∧ SplitEpi v := by
  obtain ⟨v, hv⟩ := hg.2 Z f hf.1
  rcases hf.2.2 E g v hv with h | h
  · exact absurd h hg.1
  · exact ⟨v, hv, h⟩

/-- Jacobson's trick for maps: if `1 - g t` is invertible then so is `1 - t g`. -/
lemma isUnit_one_sub_comp {E Z : Type*} [AddCommGroup E] [Module A E] [AddCommGroup Z]
    [Module A Z] (t : Z →ₗ[A] E) (g : E →ₗ[A] Z)
    (h : IsUnit (1 - g ∘ₗ t : Module.End A Z)) : IsUnit (1 - t ∘ₗ g : Module.End A E) := by
  obtain ⟨w, hw1, hw2⟩ := isUnit_iff_exists.1 h
  refine isUnit_iff_exists.2 ⟨1 + t ∘ₗ w ∘ₗ g, ?_, ?_⟩
  · have hw1' : (1 - g ∘ₗ t) ∘ₗ w = 1 := hw1
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hw1' (g x)
    change (1 - g ∘ₗ t) (w (g x)) = g x at this
    change (1 - t ∘ₗ g) ((1 + t ∘ₗ w ∘ₗ g) x) = x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.comp_apply] at this ⊢
    have h2 : t (w (g x)) - t (g (t (w (g x)))) = t (g x) := by rw [← map_sub, this]
    simp only [map_add]
    rw [← h2]
    abel
  · have hw2' : w ∘ₗ (1 - g ∘ₗ t) = 1 := hw2
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hw2' (g x)
    change w ((1 - g ∘ₗ t) (g x)) = g x at this
    change (1 + t ∘ₗ w ∘ₗ g) ((1 - t ∘ₗ g) x) = x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.comp_apply, map_sub] at this ⊢
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    simp only [map_add, map_sub]
    abel

/-- **In an exact sequence with left almost split `f`, right almost split surjective `g` and local
`End(Z)`, the map `f` is irreducible.** -/
theorem isIrr_left {X E Z : FDMod k A} {f : X ⟶ E} {g : E ⟶ Z} (hf : IsLeftAS f)
    (hg : IsRightAS g) (hsurj : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g))
    [IsLocalRing (Module.End A Z)] : IsIrr f := by
  refine ⟨hf.1, fun ⟨s, hs⟩ ↦ ?_, fun W a b hab ↦ ?_⟩
  · -- `f` surjective forces `Z = 0`
    have hfs : ∀ e, e ∈ LinearMap.ker (FDMod.lin g) := fun e ↦ by
      rw [← hex]
      exact ⟨FDMod.lin s e, LinearMap.congr_fun hs e⟩
    have h0 : (1 : Module.End A Z) = 0 := by
      apply LinearMap.ext; intro z
      obtain ⟨e, rfl⟩ := hsurj z
      exact hfs e
    exact one_ne_zero h0
  · by_cases ha : SplitMono a
    · exact Or.inl ha
    right
    obtain ⟨c, hc⟩ := hf.2 W a ha
    -- `1 - b c` vanishes on `ker g`
    have hker : LinearMap.ker (FDMod.lin g) ≤
        LinearMap.ker (LinearMap.id - FDMod.lin b ∘ₗ FDMod.lin c) := by
      intro e he
      rw [← hex] at he
      obtain ⟨x, rfl⟩ := he
      have h1 : FDMod.lin b (FDMod.lin c (FDMod.lin f x)) = FDMod.lin f x := by
        have h2 : FDMod.lin c (FDMod.lin f x) = FDMod.lin a x := LinearMap.congr_fun hc x
        rw [h2]
        exact LinearMap.congr_fun hab x
      change FDMod.lin f x - FDMod.lin b (FDMod.lin c (FDMod.lin f x)) = 0
      rw [h1, sub_self]
    let q := LinearMap.quotKerEquivOfSurjective (FDMod.lin g) hsurj
    let t : Z →ₗ[A] E := ((LinearMap.ker (FDMod.lin g)).liftQ _ hker) ∘ₗ q.symm.toLinearMap
    have ht : ∀ e, t (FDMod.lin g e) = e - FDMod.lin b (FDMod.lin c e) := fun e ↦ by
      have hq : q.symm (FDMod.lin g e) = Submodule.Quotient.mk e := q.symm_apply_eq.2 rfl
      change (LinearMap.ker (FDMod.lin g)).liftQ _ hker (q.symm (FDMod.lin g e)) = _
      rw [hq, Submodule.liftQ_apply]
      rfl
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (FDMod.lin g ∘ₗ t) with h | h
    · -- `g` would split
      obtain ⟨w, hw1, -⟩ := isUnit_iff_exists.1 h
      exact absurd ⟨show Z ⟶ E from t ∘ₗ w, hw1⟩ hg.1
    · have hu := isUnit_one_sub_comp t (FDMod.lin g) h
      have heq : (1 - t ∘ₗ FDMod.lin g : Module.End A E) = FDMod.lin b ∘ₗ FDMod.lin c := by
        apply LinearMap.ext; intro e
        change e - t (FDMod.lin g e) = _
        rw [ht]
        simp
      rw [heq] at hu
      obtain ⟨w, hw1, -⟩ := isUnit_iff_exists.1 hu
      exact ⟨show E ⟶ W from FDMod.lin c ∘ₗ w, hw1⟩

/-- **Dually, `g` is irreducible when `End(X)` is local and `f` is injective.** -/
theorem isIrr_right {X E Z : FDMod k A} {f : X ⟶ E} {g : E ⟶ Z} (hf : IsLeftAS f)
    (hg : IsRightAS g) (hinj : Function.Injective (FDMod.lin f))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g))
    [IsLocalRing (Module.End A X)] : IsIrr g := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, hg.1, fun W a b hab ↦ ?_⟩
  · -- `g` injective forces `X = 0`
    have h0 : (1 : Module.End A X) = 0 := by
      apply LinearMap.ext; intro x
      apply hinj
      have hx : FDMod.lin f x ∈ LinearMap.ker (FDMod.lin g) := hex ▸ LinearMap.mem_range_self _ x
      have h1 : FDMod.lin r (FDMod.lin g (FDMod.lin f x)) = FDMod.lin f x := LinearMap.congr_fun hr _
      rw [show FDMod.lin g (FDMod.lin f x) = 0 from hx, map_zero] at h1
      change FDMod.lin f x = FDMod.lin f 0
      rw [map_zero, ← h1]
    exact one_ne_zero h0
  · by_cases hb : SplitEpi b
    · exact Or.inr hb
    left
    obtain ⟨c, hc⟩ := hg.2 W b hb
    -- `1 - c a` lands in `ker g = range f`
    have hmem : ∀ e, e - FDMod.lin c (FDMod.lin a e) ∈ LinearMap.range (FDMod.lin f) := by
      intro e
      rw [hex]
      change FDMod.lin g (e - FDMod.lin c (FDMod.lin a e)) = 0
      have h1 : FDMod.lin g (FDMod.lin c (FDMod.lin a e)) = FDMod.lin b (FDMod.lin a e) :=
        LinearMap.congr_fun hc _
      have h2 : FDMod.lin b (FDMod.lin a e) = FDMod.lin g e := LinearMap.congr_fun hab e
      rw [map_sub, h1, h2, sub_self]
    let ef := LinearEquiv.ofInjective (FDMod.lin f) hinj
    let t : E →ₗ[A] X := ef.symm.toLinearMap ∘ₗ LinearMap.codRestrict _
      (LinearMap.id - FDMod.lin c ∘ₗ FDMod.lin a) hmem
    have ht : ∀ e, FDMod.lin f (t e) = e - FDMod.lin c (FDMod.lin a e) := fun e ↦ by
      have := ef.apply_symm_apply ⟨e - FDMod.lin c (FDMod.lin a e), hmem e⟩
      exact congrArg Subtype.val this
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (t ∘ₗ FDMod.lin f) with h | h
    · obtain ⟨w, -, hw2⟩ := isUnit_iff_exists.1 h
      exact absurd ⟨show E ⟶ X from w ∘ₗ t, hw2⟩ hf.1
    · have hu := isUnit_one_sub_comp (FDMod.lin f) t h
      have heq : (1 - FDMod.lin f ∘ₗ t : Module.End A E) = FDMod.lin c ∘ₗ FDMod.lin a := by
        apply LinearMap.ext; intro e
        change e - FDMod.lin f (t e) = _
        rw [ht]
        simp
      rw [heq] at hu
      obtain ⟨w, -, hw2⟩ := isUnit_iff_exists.1 hu
      exact ⟨show W ⟶ E from w ∘ₗ FDMod.lin c, hw2⟩

/-- **The components of a right minimal right almost split map on a summand factor only
trivially**: if `g` is right minimal right almost split and `E = U ⊕ V`, then `g` restricted to `U`
does not factor as `b a` with `a` not split mono and `b` not split epi. -/
theorem component_factor {E Z : FDMod k A} {g : E ⟶ Z} (hg : IsRightAS g)
    (hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ))
    (U V : Submodule A E) (hUV : IsCompl U V) (W : FDMod k A)
    (a : FDMod.ofSub U ⟶ W) (b : W ⟶ Z)
    (hab : a ≫ b = (show FDMod.ofSub U ⟶ Z from FDMod.lin g ∘ₗ U.subtype)) :
    SplitMono a ∨ SplitEpi b := by
  by_cases hb : SplitEpi b
  · exact Or.inr hb
  left
  obtain ⟨c, hc⟩ := hg.2 W b hb
  let e := Submodule.prodEquivOfIsCompl U V hUV
  let πU : E →ₗ[A] U := LinearMap.fst A U V ∘ₗ e.symm.toLinearMap
  let πV : E →ₗ[A] V := LinearMap.snd A U V ∘ₗ e.symm.toLinearMap
  have hsplit : ∀ x : E, (πU x : E) + (πV x : E) = x := fun x ↦ by
    change ((e.symm x).1 : E) + ((e.symm x).2 : E) = x
    rw [← Submodule.coe_prodEquivOfIsCompl' U V hUV, LinearEquiv.apply_symm_apply]
  -- `φ = c a` on `U`, identity on `V`
  let ca : U →ₗ[A] E := FDMod.lin c ∘ₗ FDMod.lin a
  let φ : E →ₗ[A] E := ca ∘ₗ πU + V.subtype ∘ₗ πV
  have hca : ∀ u : U, FDMod.lin g (ca u) = FDMod.lin g u := fun u ↦ by
    have h1 : FDMod.lin g (FDMod.lin c (FDMod.lin a u)) = FDMod.lin b (FDMod.lin a u) :=
      LinearMap.congr_fun hc _
    rw [show ca u = FDMod.lin c (FDMod.lin a u) from rfl, h1]
    exact LinearMap.congr_fun hab u
  have hφ : (show E ⟶ E from φ) ≫ g = g := by
    apply LinearMap.ext; intro x
    change FDMod.lin g (ca (πU x) + (πV x : E)) = FDMod.lin g x
    rw [map_add, hca, ← map_add, hsplit]
  have hbij := hmin _ hφ
  let eφ := LinearEquiv.ofBijective φ hbij
  -- the `U`-block `πU c a` is injective, hence bijective
  let τ : U →ₗ[A] U := πU ∘ₗ ca
  have hπUφ : ∀ u : U, πU (φ u) = τ u := fun u ↦ by
    have h1 : πU (u : E) = u := by
      change (e.symm ((u : U) : E)).1 = u
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    have h2 : πV (u : E) = 0 := by
      change (e.symm ((u : U) : E)).2 = 0
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    change πU (ca (πU (u : E)) + (πV (u : E) : E)) = πU (ca u)
    rw [h1, h2, Submodule.coe_zero, add_zero]
  haveI : FiniteDimensional k U := inferInstanceAs (FiniteDimensional k (U.restrictScalars k))
  have hτinj : Function.Injective τ := by
    intro u u' huu
    -- `φ u - φ u'` lies in `V`, so it is `φ` of an element of `V`, forcing `u = u'`
    have hv : φ (u : E) - φ (u' : E) ∈ V := by
      have : πU (φ (u : E) - φ (u' : E)) = 0 := by rw [map_sub, hπUφ, hπUφ, huu, sub_self]
      have h3 := hsplit (φ (u : E) - φ (u' : E))
      rw [this, Submodule.coe_zero, zero_add] at h3
      rw [← h3]; exact (πV _).2
    have hφv : φ (φ (u : E) - φ (u' : E)) = φ (u : E) - φ (u' : E) := by
      have h1 : πU (φ (u : E) - φ (u' : E)) = 0 := by rw [map_sub, hπUφ, hπUφ, huu, sub_self]
      change ca (πU _) + (πV _ : E) = _
      rw [h1, map_zero, zero_add]
      have h3 := hsplit (φ (u : E) - φ (u' : E))
      rw [h1, Submodule.coe_zero, zero_add] at h3
      exact h3
    have h4 : φ (φ (u : E) - φ (u' : E)) = φ ((u : E) - (u' : E)) := by rw [hφv, map_sub]
    have h4' : φ (u : E) - φ (u' : E) = (u : E) - (u' : E) := hbij.1 h4
    have h5 : ((u : E) - (u' : E)) ∈ V := h4' ▸ hv
    have h6 : ((u : E) - (u' : E)) ∈ U := Submodule.sub_mem _ u.2 u'.2
    have h7 := hUV.disjoint.le_bot ⟨h6, h5⟩
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot A).1 h7))
  have hτbij : Function.Bijective τ :=
    ⟨hτinj, (LinearMap.injective_iff_surjective (f := τ.restrictScalars k)).1 hτinj⟩
  let eτ := LinearEquiv.ofBijective τ hτbij
  refine ⟨show W →ₗ[A] U from eτ.symm.toLinearMap ∘ₗ πU ∘ₗ FDMod.lin c, LinearMap.ext fun u ↦ ?_⟩
  change eτ.symm (πU (FDMod.lin c (FDMod.lin a u))) = u
  rw [LinearEquiv.symm_apply_eq]
  rfl

end LargeIndecomposable.AR
