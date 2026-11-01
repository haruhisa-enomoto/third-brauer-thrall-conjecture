module

public import LargeIndecomposable.DirectedAlgebras.Directing.Degeneration
public import LargeIndecomposable.DirectedAlgebras.Directing.Directing
public import LargeIndecomposable.AuslanderReiten.AlmostSplit.RightAS
public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARSeq

/-!
# Modules with minimal endomorphism ring are rigid

`ExtVanish X Y` says that every short exact sequence `0 → Y → E → X → 0` splits. It passes to
direct sums in both variables (`extVanish_fst`, `extVanish_snd`). If every nonzero indecomposable
module is rigid, then a module `V` whose endomorphism ring has minimal dimension among modules
with the same value of an additive invariant (such as the dimension vector) is rigid
(`extVanish_of_minEnd`; ASS IX.3.3, proof): a nonsplit extension between a summand and its
complement would have a smaller endomorphism ring (ASS VIII.2.8, `finrank_end_lt`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

section Split

variable {L M N : FDMod k A}

lemma mem_ker_of_range {f : L →ₗ[A] M} {g : M →ₗ[A] N}
    (hex : LinearMap.range f = LinearMap.ker g) (l : L) : g (f l) = 0 := by
  have : f l ∈ LinearMap.ker g := by rw [← hex]; exact ⟨l, rfl⟩
  exact this

/-- A retraction gives a section. -/
lemma exists_section_of_retr (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (r : M →ₗ[A] L) (hr : r ∘ₗ f = LinearMap.id) :
    ∃ s : N →ₗ[A] M, g ∘ₗ s = LinearMap.id := by
  obtain ⟨s, hs⟩ := exists_factor f g hg hex (LinearMap.id - f ∘ₗ r) (by
    refine LinearMap.ext fun l ↦ ?_
    have := LinearMap.congr_fun hr l
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this])
  refine ⟨s, LinearMap.ext fun n ↦ ?_⟩
  obtain ⟨m, rfl⟩ := hg n
  have h1 := LinearMap.congr_fun hs m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1 ⊢
  rw [h1, map_sub, mem_ker_of_range hex, sub_zero]

/-- A section gives a retraction. -/
lemma exists_retr_of_section (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f)
    (hex : LinearMap.range f = LinearMap.ker g) (s : N →ₗ[A] M) (hs : g ∘ₗ s = LinearMap.id) :
    ∃ r : M →ₗ[A] L, r ∘ₗ f = LinearMap.id := by
  obtain ⟨r, hr⟩ := exists_lift f g hf hex (LinearMap.id - s ∘ₗ g) (by
    refine LinearMap.ext fun m ↦ ?_
    have := LinearMap.congr_fun hs (g m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this])
  refine ⟨r, LinearMap.ext fun l ↦ hf ?_⟩
  have h1 := LinearMap.congr_fun hr (f l)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1 ⊢
  rw [h1, mem_ker_of_range hex, map_zero, sub_zero]

end Split

/-- **Every short exact sequence `0 → Y → E → X → 0` splits.** -/
def ExtVanish (X Y : FDMod k A) : Prop :=
  ∀ (E : FDMod k A) (i : Y →ₗ[A] E) (p : E →ₗ[A] X), Function.Injective i →
    Function.Surjective p → LinearMap.range i = LinearMap.ker p →
    ∃ s : X →ₗ[A] E, p ∘ₗ s = LinearMap.id

/-- Directing modules are rigid. -/
lemma Directing.extVanish [FiniteDimensional k A] {M : FDMod k A} (hM : Directing M) :
    ExtVanish M M := fun _ i p hi hp hex ↦ hM.split i p hi hp hex

section Sums

variable {X Y E : FDMod k A}

/-- Pulling back along a split summand of the end term. -/
lemma exists_lift_summand {X' : FDMod k A} (ι : X' →ₗ[A] X) (π : X →ₗ[A] X')
    (hπι : π ∘ₗ ι = LinearMap.id) (hv : ExtVanish X' Y) (i : Y →ₗ[A] E) (p : E →ₗ[A] X)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) :
    ∃ s : X' →ₗ[A] E, p ∘ₗ s = ι := by
  have hπι' : ∀ x, π (ι x) = x := fun x ↦ LinearMap.congr_fun hπι x
  let U : Submodule A E := Submodule.comap p (LinearMap.range ι)
  have hiU : ∀ y, i y ∈ U := fun y ↦ by
    change p (i y) ∈ LinearMap.range ι
    rw [mem_ker_of_range hex]; exact Submodule.zero_mem _
  let i' : Y →ₗ[A] FDMod.ofSub U := i.codRestrict U hiU
  let p' : FDMod.ofSub U →ₗ[A] X' := π ∘ₗ p ∘ₗ U.subtype
  have hi' : Function.Injective i' := fun a b h ↦ hi (congrArg Subtype.val h)
  have hp' : Function.Surjective p' := by
    intro x
    obtain ⟨e, he⟩ := hp (ι x)
    refine ⟨⟨e, ?_⟩, ?_⟩
    · change p e ∈ LinearMap.range ι
      rw [he]; exact ⟨x, rfl⟩
    · change π (p e) = x
      rw [he, hπι']
  have hex' : LinearMap.range i' = LinearMap.ker p' := by
    ext ⟨e, heU⟩
    constructor
    · rintro ⟨y, hy⟩
      rw [LinearMap.mem_ker]
      rw [← hy]
      change π (p (i y)) = 0
      rw [mem_ker_of_range hex, map_zero]
    · intro h
      rw [LinearMap.mem_ker] at h
      obtain ⟨x, hx⟩ := heU
      have h0 : π (p e) = 0 := h
      have hx0 : x = 0 := by rw [← hπι' x, hx, h0]
      have hpe : e ∈ LinearMap.ker p := by
        rw [LinearMap.mem_ker, ← hx, hx0, map_zero]
      rw [← hex] at hpe
      obtain ⟨y, hy⟩ := hpe
      exact ⟨y, Subtype.ext hy⟩
  obtain ⟨s', hs'⟩ := hv (FDMod.ofSub U) i' p' hi' hp' hex'
  refine ⟨U.subtype ∘ₗ s', LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := (s' x).2
  have h1 : π (p (s' x)) = x := LinearMap.congr_fun hs' x
  change p (s' x) = ι x
  rw [← hx₀] at h1 ⊢
  rw [hπι'] at h1
  rw [h1]

/-- **Vanishing in the first variable passes to binary sums.** -/
theorem extVanish_fst {X₁ X₂ : FDMod k A} (ι₁ : X₁ →ₗ[A] X) (ι₂ : X₂ →ₗ[A] X)
    (π₁ : X →ₗ[A] X₁) (π₂ : X →ₗ[A] X₂) (h₁ : π₁ ∘ₗ ι₁ = LinearMap.id)
    (h₂ : π₂ ∘ₗ ι₂ = LinearMap.id) (hs : ι₁ ∘ₗ π₁ + ι₂ ∘ₗ π₂ = LinearMap.id)
    (e₁ : ExtVanish X₁ Y) (e₂ : ExtVanish X₂ Y) : ExtVanish X Y := by
  intro E i p hi hp hex
  obtain ⟨s₁, hs₁⟩ := exists_lift_summand ι₁ π₁ h₁ e₁ i p hi hp hex
  obtain ⟨s₂, hs₂⟩ := exists_lift_summand ι₂ π₂ h₂ e₂ i p hi hp hex
  refine ⟨s₁ ∘ₗ π₁ + s₂ ∘ₗ π₂, ?_⟩
  rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, hs₁, hs₂, hs]

/-- Pushing out along a split summand of the first term. -/
lemma exists_retr_summand {Y' : FDMod k A} (ι : Y' →ₗ[A] Y) (π : Y →ₗ[A] Y')
    (hπι : π ∘ₗ ι = LinearMap.id) (hv : ExtVanish X Y') (i : Y →ₗ[A] E) (p : E →ₗ[A] X)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) :
    ∃ r : E →ₗ[A] Y', r ∘ₗ i = π := by
  have hπι' : ∀ y, π (ι y) = y := fun y ↦ LinearMap.congr_fun hπι y
  let U : Submodule A E := Submodule.map i (LinearMap.ker π)
  have hUp : U ≤ LinearMap.ker p := by
    rintro _ ⟨y, -, rfl⟩
    exact mem_ker_of_range hex y
  let i' : Y' →ₗ[A] FDMod.ofQuot E U := U.mkQ ∘ₗ i ∘ₗ ι
  let p' : FDMod.ofQuot E U →ₗ[A] X := U.liftQ p hUp
  have hsub : ∀ y, U.mkQ (i y) = U.mkQ (i (ι (π y))) := by
    intro y
    rw [← sub_eq_zero, ← map_sub, ← map_sub, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    refine ⟨y - ι (π y), ?_, rfl⟩
    change π (y - ι (π y)) = 0
    rw [map_sub, hπι', sub_self]
  have hi' : Function.Injective i' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    change U.mkQ (i (ι y)) = 0 at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = ι y := hi hyy
    rw [← hπι' y, ← this]
    exact hy'
  have hp' : Function.Surjective p' := by
    intro x
    obtain ⟨e, rfl⟩ := hp x
    exact ⟨U.mkQ e, rfl⟩
  have hex' : LinearMap.range i' = LinearMap.ker p' := by
    ext q
    obtain ⟨e, rfl⟩ := U.mkQ_surjective q
    constructor
    · rintro ⟨y, hy⟩
      rw [LinearMap.mem_ker, ← hy]
      change p (i (ι y)) = 0
      exact mem_ker_of_range hex _
    · intro h
      have hpe : e ∈ LinearMap.ker p := h
      rw [← hex] at hpe
      obtain ⟨y, rfl⟩ := hpe
      exact ⟨π y, (hsub y).symm⟩
  obtain ⟨s', hs'⟩ := hv (FDMod.ofQuot E U) i' p' hi' hp' hex'
  obtain ⟨r', hr'⟩ := exists_retr_of_section i' p' hi' hex' s' hs'
  refine ⟨r' ∘ₗ U.mkQ, LinearMap.ext fun y ↦ ?_⟩
  change r' (U.mkQ (i y)) = π y
  rw [hsub y]
  exact LinearMap.congr_fun hr' (π y)

/-- **Vanishing in the second variable passes to finite sums.** -/
theorem extVanish_snd {J : Type*} [Fintype J] {Yj : J → FDMod k A} (ι : ∀ j, Yj j →ₗ[A] Y)
    (π : ∀ j, Y →ₗ[A] Yj j) (hπι : ∀ j, π j ∘ₗ ι j = LinearMap.id)
    (hs : ∑ j, ι j ∘ₗ π j = LinearMap.id) (hv : ∀ j, ExtVanish X (Yj j)) : ExtVanish X Y := by
  intro E i p hi hp hex
  choose r hr using fun j ↦ exists_retr_summand (ι j) (π j) (hπι j) (hv j) i p hi hp hex
  refine exists_section_of_retr i p hp hex (∑ j, ι j ∘ₗ r j) ?_
  rw [← hs]
  refine LinearMap.ext fun y ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (ι j) (LinearMap.congr_fun (hr j) y)

end Sums

section Binary

variable {V V₁ V₂ : FDMod k A} (ι₁ : V₁ →ₗ[A] V) (ι₂ : V₂ →ₗ[A] V) (π₁ : V →ₗ[A] V₁)
  (π₂ : V →ₗ[A] V₂)

/-- Endomorphisms of a binary direct sum as four blocks. -/
def endBlocks (h₁₁ : ∀ x, π₁ (ι₁ x) = x) (h₂₂ : ∀ x, π₂ (ι₂ x) = x) (h₁₂ : ∀ x, π₁ (ι₂ x) = 0)
    (h₂₁ : ∀ x, π₂ (ι₁ x) = 0) (hs : ∀ v, ι₁ (π₁ v) + ι₂ (π₂ v) = v) :
    (V →ₗ[A] V) ≃ₗ[k] ((V₁ →ₗ[A] V₁) × (V₂ →ₗ[A] V₂)) × ((V₁ →ₗ[A] V₂) × (V₂ →ₗ[A] V₁)) where
  toFun φ := ((π₁ ∘ₗ φ ∘ₗ ι₁, π₂ ∘ₗ φ ∘ₗ ι₂), (π₂ ∘ₗ φ ∘ₗ ι₁, π₁ ∘ₗ φ ∘ₗ ι₂))
  map_add' φ ψ := by
    simp only [LinearMap.add_comp, LinearMap.comp_add, Prod.mk_add_mk]
  map_smul' c φ := by
    simp only [RingHom.id_apply, Prod.smul_mk]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact LinearMap.ext fun x ↦ by simp
  invFun b := ι₁ ∘ₗ b.1.1 ∘ₗ π₁ + ι₂ ∘ₗ b.1.2 ∘ₗ π₂ + ι₂ ∘ₗ b.2.1 ∘ₗ π₁ + ι₁ ∘ₗ b.2.2 ∘ₗ π₂
  left_inv φ := by
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    conv_rhs => rw [← hs (φ v), ← hs v]
    simp only [map_add]
    abel
  right_inv b := by
    obtain ⟨⟨a, b'⟩, c, d⟩ := b
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
      exact LinearMap.ext fun x ↦ by simp [h₁₁, h₂₂, h₁₂, h₂₁]

/-- **The endomorphism dimension of a binary direct sum.** -/
lemma finrank_end_sum (h₁₁ : ∀ x, π₁ (ι₁ x) = x) (h₂₂ : ∀ x, π₂ (ι₂ x) = x)
    (h₁₂ : ∀ x, π₁ (ι₂ x) = 0) (h₂₁ : ∀ x, π₂ (ι₁ x) = 0) (hs : ∀ v, ι₁ (π₁ v) + ι₂ (π₂ v) = v) :
    finrank k (V →ₗ[A] V) = finrank k (V₁ →ₗ[A] V₁) + finrank k (V₂ →ₗ[A] V₂) +
      finrank k (V₁ →ₗ[A] V₂) + finrank k (V₂ →ₗ[A] V₁) := by
  rw [(endBlocks ι₁ ι₂ π₁ π₂ h₁₁ h₂₂ h₁₂ h₂₁ hs).finrank_eq, Module.finrank_prod,
    Module.finrank_prod, Module.finrank_prod]
  ring

end Binary

/-- **A module of minimal endomorphism dimension is rigid** (ASS IX.3.3, proof). Here `d` is any
invariant additive on short exact sequences, and all nonzero indecomposables are rigid. -/
theorem extVanish_of_minEnd_on {Δ : Type*} [Add Δ] (d : FDMod k A → Δ)
    (hd : ∀ (L M N : FDMod k A) (f : L →ₗ[A] M) (g : M →ₗ[A] N), Function.Injective f →
      Function.Surjective g → LinearMap.range f = LinearMap.ker g → d M = d L + d N)
    (V : FDMod k A)
    (hrig : ∀ M : FDMod k A, IsIndecMod A M → Nontrivial M →
      (∃ f : M →ₗ[A] V, Function.Injective f) → ExtVanish M M)
    (hmin : ∀ W : FDMod k A, d W = d V → finrank k (V →ₗ[A] V) ≤ finrank k (W →ₗ[A] W)) :
    ExtVanish V V := by
  classical
  obtain ⟨D⟩ := FDMod.exists_decomp V
  let inc : ∀ j, D.obj j →ₗ[A] V := fun j ↦ FDMod.lin (D.inc j)
  let pr : ∀ j, V →ₗ[A] D.obj j := fun j ↦ FDMod.lin (D.proj j)
  have hretr : ∀ j x, pr j (inc j x) = x := fun j x ↦ LinearMap.congr_fun (D.retr j) x
  have hsum : ∀ v, ∑ j, inc j (pr j v) = v := fun v ↦ by
    have := LinearMap.congr_fun D.sum_id v
    simpa using this
  -- the complement of the `j`-th summand
  let C : D.ι → FDMod k A := fun j ↦ FDMod.ofSub (LinearMap.ker (pr j))
  haveI : ∀ j, FiniteDimensional k (C j) := fun j ↦ (C j).isFD
  have hmemC : ∀ j v, v - inc j (pr j v) ∈ LinearMap.ker (pr j) := fun j v ↦ by
    rw [LinearMap.mem_ker, map_sub, hretr, sub_self]
  let ιC : ∀ j, C j →ₗ[A] V := fun j ↦ (LinearMap.ker (pr j)).subtype
  let πC : ∀ j, V →ₗ[A] C j := fun j ↦
    (LinearMap.id - inc j ∘ₗ pr j).codRestrict (LinearMap.ker (pr j)) (hmemC j)
  have hCC : ∀ j (c : C j), πC j (ιC j c) = c := fun j c ↦ by
    apply Subtype.ext
    change (c : V) - inc j (pr j c) = c
    rw [show pr j c = 0 from c.2, map_zero, sub_zero]
  have hCi : ∀ j x, πC j (inc j x) = 0 := fun j x ↦ by
    apply Subtype.ext
    change inc j x - inc j (pr j (inc j x)) = 0
    rw [hretr, sub_self]
  have hiC : ∀ j (c : C j), pr j (ιC j c) = 0 := fun j c ↦ c.2
  have hsC : ∀ j v, inc j (pr j v) + ιC j (πC j v) = v := fun j v ↦ by
    change inc j (pr j v) + (v - inc j (pr j v)) = v
    abel
  -- the complement has no extension by the summand
  have hA : ∀ j, ExtVanish (C j) (D.obj j) := by
    intro j E i p hi hp hex
    by_contra hns
    have hnr : ¬∃ r : E →ₗ[A] D.obj j, r ∘ₗ i = LinearMap.id := fun ⟨r, hr⟩ ↦
      hns (exists_section_of_retr i p hp hex r hr)
    have hlt := finrank_end_lt (k := k) i p hi hp hex hnr
    have hV := finrank_end_sum (k := k) (inc j) (ιC j) (pr j) (πC j) (hretr j) (hCC j) (hiC j)
      (hCi j) (hsC j)
    have hdE := hd _ _ _ i p hi hp hex
    have hdV : d V = d (D.obj j) + d (C j) := by
      refine hd _ _ _ (inc j) (πC j) (fun a b h ↦ by rw [← hretr j a, h, hretr]) (fun c ↦
        ⟨ιC j c, hCC j c⟩) ?_
      ext v
      constructor
      · rintro ⟨x, rfl⟩; exact hCi j x
      · intro h
        refine ⟨pr j v, ?_⟩
        have := hsC j v
        rw [show πC j v = 0 from h, map_zero, add_zero] at this
        exact this
    have := hmin E (hdE.trans hdV.symm)
    omega
  refine extVanish_snd inc pr (fun j ↦ LinearMap.ext (hretr j))
    (LinearMap.ext fun v ↦ by simpa using hsum v) fun j ↦ ?_
  refine extVanish_fst (inc j) (ιC j) (pr j) (πC j) (LinearMap.ext (hretr j))
    (LinearMap.ext (hCC j)) (LinearMap.ext fun v ↦ hsC j v)
    (hrig _ (D.indec j) (D.nt j) ⟨inc j, Function.LeftInverse.injective (hretr j)⟩) (hA j)

/-- **A module of minimal endomorphism dimension is rigid**, if all indecomposables are. -/
theorem extVanish_of_minEnd {Δ : Type*} [Add Δ] (d : FDMod k A → Δ)
    (hd : ∀ (L M N : FDMod k A) (f : L →ₗ[A] M) (g : M →ₗ[A] N), Function.Injective f →
      Function.Surjective g → LinearMap.range f = LinearMap.ker g → d M = d L + d N)
    (hrig : ∀ M : FDMod k A, IsIndecMod A M → Nontrivial M → ExtVanish M M)
    (V : FDMod k A)
    (hmin : ∀ W : FDMod k A, d W = d V → finrank k (V →ₗ[A] V) ≤ finrank k (W →ₗ[A] W)) :
    ExtVanish V V :=
  extVanish_of_minEnd_on d hd V (fun M h1 h2 _ ↦ hrig M h1 h2) hmin

end LargeIndecomposable.AR
