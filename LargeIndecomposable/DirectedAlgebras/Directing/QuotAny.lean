module

public import LargeIndecomposable.AuslanderReiten.Lengths.ChainBound
public import LargeIndecomposable.DirectedAlgebras.Directing.LiveOn
public import LargeIndecomposable.DirectedAlgebras.Directing.ProjClass

/-!
# Quotients by arbitrary sets of idempotents

For any set `T'` of live points, `A / ⟨e_v : v ∉ T'⟩` is directed (`quotAny`), with points `T'` and
an arrow for each nonzero corner. Chains ending at a projective of the quotient lift by pullbacks
to chains of the same length ending at a projective of `A` (`chain_lift`, ASS IX.5.2), so
indecomposable projectives of the quotient are good if those of `A` are (`good_quot`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A) {T' : Set D.ι}

/-- The character of a point of `T'` on the quotient. -/
def qchiA (hT : T' ⊆ D.T) (x : D.ι) (hx : x ∈ T') : D.QAlg T' →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨D.chi x (hT hx), by
    rintro a b ⟨⟨v, hv, rfl⟩, rfl⟩
    rw [map_zero]
    exact D.chi_e_ne x (hT hx) (fun h ↦ hv (h ▸ hx))⟩

lemma qchiA_qmap (hT : T' ⊆ D.T) (x : D.ι) (hx : x ∈ T') (a : A) :
    D.qchiA hT x hx (D.qmap T' a) = D.chi x (hT hx) a := by
  simp [qchiA]

/-- **The quotient by the idempotents outside any set is directed.** -/
def quotAny (hT : T' ⊆ D.T) : DirData k (D.QAlg T') where
  ι := T'
  fin := Fintype.ofFinite _
  dec := Classical.decEq _
  e x := D.qmap T' (D.e x)
  idem x := (D.idem x).map (D.qmap T')
  orth x y h := by
    rw [← map_mul, D.orth _ _ (fun h' ↦ h (Subtype.ext h')), map_zero]
  sum := by
    classical
    letI : Fintype T' := Fintype.ofFinite _
    have h1 : ∑ x : D.ι, D.qmap T' (D.e x) = 1 := by rw [← map_sum, D.sum, map_one]
    rw [← h1, ← Finset.sum_subtype (Finset.univ.filter (· ∈ T')) (by simp) (fun x ↦ D.qmap T' (D.e x)),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x ∈ T'
    · rw [if_pos hx]
    · rw [if_neg hx, D.qmap_e_out T' hx]
  T := Set.univ
  zero v hv := absurd (Set.mem_univ v) hv
  ne x _ h := by
    have := congrArg (D.qchiA hT x.1 x.2) h
    rw [D.qchiA_qmap, D.chi_e_self, map_zero] at this
    exact one_ne_zero this
  local_ x a := by
    obtain ⟨a, rfl⟩ := D.qmap_surjective T' a
    obtain ⟨c, hc⟩ := D.local_ x a
    exact ⟨c, by rw [← map_mul, ← map_mul, hc, map_smul]⟩
  Arr x y := x ≠ y ∧ ∃ a, D.qmap T' (D.e y) * a * D.qmap T' (D.e x) ≠ 0
  arrT _ _ _ := ⟨Set.mem_univ _, Set.mem_univ _⟩
  hom x y a h := by
    by_cases hxy : x = y
    · subst hxy; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hxy, a, h⟩
  acyc x y h h' := by
    have hstep : ∀ a b : T', (a ≠ b ∧ ∃ c, D.qmap T' (D.e b) * c * D.qmap T' (D.e a) ≠ 0) →
        Relation.TransGen D.Arr a.1 b.1 := by
      rintro a b ⟨hab, c, hc⟩
      obtain ⟨c, rfl⟩ := D.qmap_surjective T' c
      have h0 : D.e b.1 * c * D.e a.1 ≠ 0 := fun h0 ↦ hc (by
        rw [← map_mul, ← map_mul, h0, map_zero])
      exact D.transGen_of_ne (D.hom _ _ c h0) (fun h' ↦ hab (Subtype.ext h'))
    have h1 : ∀ {a b : T'}, Relation.TransGen (fun x y : T' ↦ x ≠ y ∧
        ∃ c, D.qmap T' (D.e y) * c * D.qmap T' (D.e x) ≠ 0) a b →
        Relation.TransGen D.Arr a.1 b.1 := by
      intro a b hab
      induction hab with
      | single h => exact hstep _ _ h
      | tail _ h ih => exact ih.trans (hstep _ _ h)
    have h2 : ∀ {a b : T'}, Relation.ReflTransGen (fun x y : T' ↦ x ≠ y ∧
        ∃ c, D.qmap T' (D.e y) * c * D.qmap T' (D.e x) ≠ 0) a b →
        Relation.ReflTransGen D.Arr a.1 b.1 := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h ih => exact ih.trans (hstep _ _ h).to_reflTransGen
    exact D.acyc _ _ (h1 h) (h2 h')
  gen x a := by
    classical
    letI : Fintype T' := Fintype.ofFinite _
    have hsum : ∑ y : T', D.qmap T' (D.e y) = 1 := by
      have h1 : ∑ x : D.ι, D.qmap T' (D.e x) = 1 := by rw [← map_sum, D.sum, map_one]
      rw [← h1, ← Finset.sum_subtype (Finset.univ.filter (· ∈ T')) (by simp)
        (fun x ↦ D.qmap T' (D.e x)), Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : x ∈ T'
      · rw [if_pos hx]
      · rw [if_neg hx, D.qmap_e_out T' hx]
    have h2 : (1 - D.qmap T' (D.e x)) * a * D.qmap T' (D.e x) =
        ∑ y ∈ Finset.univ.erase x, D.qmap T' (D.e y) * a * D.qmap T' (D.e x) := by
      have h3 : (1 : D.QAlg T') - D.qmap T' (D.e x) = ∑ y ∈ Finset.univ.erase x, D.qmap T' (D.e y) := by
        rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x), add_sub_cancel_left]
      rw [h3, Finset.sum_mul, Finset.sum_mul]
    rw [h2]
    refine Submodule.sum_mem _ fun y hy ↦ ?_
    by_cases h0 : D.qmap T' (D.e y) * a * D.qmap T' (D.e x) = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨y, a, ⟨(Finset.ne_of_mem_erase hy).symm, a, h0⟩, rfl⟩
  arrNe x y h := h.2

/-- **The kernel of the quotient map.** -/
lemma mem_outIdeal_of_qmap (m : A) (h0 : D.qmap T' m = 0) : m ∈ D.outIdeal T' := by
  let N := D.outIdeal T'
  let ρ : A →ₐ[k] Module.End k (A ⧸ N) := Algebra.lsmul k k (A ⧸ N)
  have hρ : ∀ v, v ∉ T' → ρ (D.e v) = 0 := fun v hv ↦ by
    apply LinearMap.ext; intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N m
    change D.e v • N.mkQ m = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨v, m, hv, rfl⟩
  let ρ' : D.QAlg T' →ₐ[k] Module.End k (A ⧸ N) := RingQuot.liftAlgHom k ⟨ρ, by
    rintro _ _ ⟨⟨v, hv, rfl⟩, rfl⟩
    rw [hρ v hv, map_zero]⟩
  have h1 : ρ' (D.qmap T' m) = ρ m := by simp [ρ']
  rw [h0, map_zero] at h1
  have h2 := LinearMap.congr_fun h1 (N.mkQ 1)
  change (0 : A ⧸ N) = m • N.mkQ 1 at h2
  rw [← map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply, eq_comm,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- The trace of the idempotents outside `T'`. -/
def tr (T' : Set D.ι) (L : FDMod k A) : Submodule A L :=
  Submodule.span A {m | ∃ v l, v ∉ T' ∧ m = D.e v • l}

variable {D}

lemma map_tr {X Y : FDMod k A} (g : X →ₗ[A] Y) {m : X} (hm : m ∈ D.tr T' X) : g m ∈ D.tr T' Y := by
  induction hm using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨v, l, hv, rfl⟩ := hr
    rw [map_smul]
    exact Submodule.subset_span ⟨v, g l, hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ a hb

/-- Maps to restrictions kill the trace. -/
lemma tr_kill {X : FDMod k A} {Y : FDMod k (D.QAlg T')} (p : X →ₗ[A] resFD (D.qmap T') Y) {m : X}
    (hm : m ∈ D.tr T' X) : p m = 0 := by
  induction hm using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨v, l, hv, rfl⟩ := hr
    rw [map_smul]
    apply toX_injective
    change D.qmap T' (D.e v) • toX (p l) = 0
    rw [D.qmap_e_out T' hv, zero_smul]
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul a b _ hb => rw [map_smul, hb, smul_zero]

/-- **One step of the pullback lift** (ASS IX.5.2, proof). -/
theorem lift_step {L : FDMod k A} {M M' : FDMod k (D.QAlg T')}
    (π : L →ₗ[A] resFD (D.qmap T') M) (hπ : Function.Surjective π)
    (hker : ∀ l, π l = 0 → l ∈ D.tr T' L) (hM' : IndNT M') (f : M' ⟶ M)
    (hf : FDMod.lin f ≠ 0) (hnb : ¬Function.Bijective (FDMod.lin f)) :
    ∃ (L' : FDMod k A) (π' : L' →ₗ[A] resFD (D.qmap T') M') (g : L' ⟶ L), IndNT L' ∧
      Function.Surjective π' ∧ (∀ l, π' l = 0 → l ∈ D.tr T' L') ∧ FDMod.lin g ≠ 0 ∧
      ¬Function.Bijective (FDMod.lin g) := by
  classical
  let R := resFD (D.qmap T') M'
  let rf : R →ₗ[A] resFD (D.qmap T') M := resHom (D.qmap T') f
  have hrf : ∀ x : M', rf (ofX x) = ofX (FDMod.lin f x) := fun _ ↦ rfl
  let N : Submodule A (L × R) := LinearMap.ker
    (π ∘ₗ LinearMap.fst A L R - rf ∘ₗ LinearMap.snd A L R)
  have hmemN : ∀ l m, (l, m) ∈ N ↔ π l = rf m := fun l m ↦ by
    change π l - rf m = 0 ↔ _
    exact sub_eq_zero
  let NM : FDMod k A := FDMod.ofSub (P := FDMod.prod L R) N
  let ρ : NM →ₗ[A] R := LinearMap.snd A L R ∘ₗ N.subtype
  have hρ : Function.Surjective ρ := fun m ↦ by
    obtain ⟨l, hl⟩ := hπ (rf m)
    exact ⟨⟨(l, m), (hmemN l m).2 hl⟩, rfl⟩
  -- the kernel of `ρ` is the trace
  have haux : ∀ l, l ∈ D.tr T' L → ∃ h : (l, (0 : R)) ∈ N, (⟨(l, 0), h⟩ : NM) ∈ D.tr T' NM := by
    intro l hl
    induction hl using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨v, l₀, hv, rfl⟩ := hr
      have h0 : π (D.e v • l₀) = 0 := tr_kill π (Submodule.subset_span ⟨v, l₀, hv, rfl⟩)
      have h1 : (D.e v • l₀, (0 : R)) ∈ N := (hmemN _ _).2 (by rw [h0, map_zero])
      refine ⟨h1, Submodule.subset_span ⟨v, ⟨_, h1⟩, hv, Subtype.ext ?_⟩⟩
      refine Prod.ext ?_ (smul_zero _).symm
      change D.e v • l₀ = D.e v • D.e v • l₀
      rw [← mul_smul, D.e_mul_e]
    | zero => exact ⟨N.zero_mem, Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨h1, h2⟩ := ha
      obtain ⟨h3, h4⟩ := hb
      have h5 : (a + b, (0 : R)) ∈ N := by simpa using N.add_mem h1 h3
      refine ⟨h5, ?_⟩
      have h6 : (⟨(a + b, 0), h5⟩ : NM) = (⟨(a, 0), h1⟩ : NM) + (⟨(b, 0), h3⟩ : NM) :=
        Subtype.ext (Prod.ext rfl (add_zero (0 : R)).symm)
      rw [h6]
      exact Submodule.add_mem _ h2 h4
    | smul a b _ hb =>
      obtain ⟨h1, h2⟩ := hb
      have h5 : (a • b, (0 : R)) ∈ N := by simpa using N.smul_mem a h1
      refine ⟨h5, ?_⟩
      have h6 : (⟨(a • b, 0), h5⟩ : NM) = a • (⟨(b, 0), h1⟩ : NM) :=
        Subtype.ext (Prod.ext rfl (smul_zero a).symm)
      rw [h6]
      exact Submodule.smul_mem _ a h2
  have hρker : ∀ n : NM, ρ n = 0 → n ∈ D.tr T' NM := by
    rintro ⟨⟨l, m⟩, hn⟩ h0
    have hm : m = 0 := h0
    subst hm
    have hl : π l = 0 := by
      rw [(hmemN l 0).1 hn, map_zero]
    obtain ⟨h1, h2⟩ := haux l (hker l hl)
    exact h2
  obtain ⟨d⟩ := FDMod.exists_decomp NM
  -- the induced idempotents of `M'`
  let E : ∀ j, NM →ₗ[A] NM := fun j ↦ FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
  have hE : ∀ j, ∃ ε : R →ₗ[A] R, ε ∘ₗ ρ = ρ ∘ₗ E j := by
    intro j
    refine exists_factor (L := FDMod.ofSub (LinearMap.ker ρ)) (LinearMap.ker ρ).subtype ρ hρ
      (Submodule.range_subtype _) (ρ ∘ₗ E j) (LinearMap.ext fun n ↦ ?_)
    exact tr_kill ρ (map_tr (E j) (hρker n.1 n.2))
  choose ε hε using hE
  have hsum : ∑ j, ε j = LinearMap.id := by
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨n, rfl⟩ := hρ m
    rw [LinearMap.sum_apply]
    have h1 : ∀ j, ε j (ρ n) = ρ (E j n) := fun j ↦ LinearMap.congr_fun (hε j) n
    simp only [h1, ← map_sum, LinearMap.id_apply]
    congr 1
    have := LinearMap.congr_fun d.sum_id n
    simpa [E] using this
  have hind : IsIndecMod A R := (isIndecMod_res_iff (D.qmap_surjective T') M').2 hM'.1
  haveI hnt : Nontrivial R := hM'.2
  haveI hFD : FiniteDimensional k R := R.isFD
  haveI : IsLocalRing (Module.End A R) := hind.isLocalRing (k := k)
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ε j : Module.End A R) := by
    by_contra hall
    push Not at hall
    have hs : ∀ s : Finset d.ι, ¬IsUnit (∑ j ∈ s, (ε j : Module.End A R)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact not_isUnit_zero
      | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        intro hu
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
        · exact hall i h
        · exact ih h
    apply hs Finset.univ
    rw [hsum]
    exact isUnit_one
  have hjb : Function.Bijective (ε j) := (Module.End.isUnit_iff _).1 hj
  let π' : d.obj j →ₗ[A] R := ρ ∘ₗ FDMod.lin (d.inc j)
  have hπ' : Function.Surjective π' := fun m ↦ by
    obtain ⟨m₁, rfl⟩ := hjb.2 m
    obtain ⟨n, rfl⟩ := hρ m₁
    exact ⟨FDMod.lin (d.proj j) n, (LinearMap.congr_fun (hε j) n).symm⟩
  have hker' : ∀ l, π' l = 0 → l ∈ D.tr T' (d.obj j) := fun l hl ↦ by
    have h1 := map_tr (FDMod.lin (d.proj j)) (hρker _ hl)
    rwa [show FDMod.lin (d.proj j) (FDMod.lin (d.inc j) l) = l from
      LinearMap.congr_fun (d.retr j) l] at h1
  let g : d.obj j →ₗ[A] L := LinearMap.fst A L R ∘ₗ N.subtype ∘ₗ FDMod.lin (d.inc j)
  have hcomm : ∀ x, π (g x) = rf (π' x) := fun x ↦
    (hmemN _ _).1 (FDMod.lin (d.inc j) x).2
  refine ⟨d.obj j, π', (FDMod.ofLin (g)), ⟨d.indec j, d.nt j⟩, hπ', hker', ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨x, hx⟩ := hπ' (ofX m)
    have h1 := hcomm x
    have h2 : g x = 0 := LinearMap.congr_fun h0 x
    rw [h2, map_zero, hx] at h1
    exact h1.symm
  · intro hb
    apply hnb
    constructor
    · rw [injective_iff_map_eq_zero]
      intro m hm
      obtain ⟨x, hx⟩ := hπ' (ofX m)
      have h1 : π (g x) = 0 := by
        rw [hcomm, hx]
        exact (hrf m).trans (by rw [hm]; rfl)
      have h2 := map_tr (LinearEquiv.ofBijective g hb).symm.toLinearMap (hker _ h1)
      have h3 : (LinearEquiv.ofBijective g hb).symm.toLinearMap (g x) = x :=
        (LinearEquiv.ofBijective g hb).symm_apply_apply x
      rw [h3] at h2
      have h4 := tr_kill π' h2
      rw [hx] at h4
      exact h4
    · intro m
      obtain ⟨l, hl⟩ := hπ (ofX m)
      obtain ⟨x, rfl⟩ := hb.2 l
      refine ⟨toX (π' x), ?_⟩
      exact (hcomm x).symm.trans hl

variable (D) in
/-- The quotient projection between vertex projectives. -/
def piP (hT : T' ⊆ D.T) (x : T') :
    projE (k := k) (D.idem x.1) →ₗ[A]
      resFD (D.qmap T') (projE (k := k) ((D.quotAny hT).idem x)) where
  toFun a := ofX ⟨D.qmap T' a, by
    change D.qmap T' a * D.qmap T' (D.e x.1) = _
    rw [← map_mul, show (a : A) * D.e x.1 = a from a.2]⟩
  map_add' a b := by
    apply toX_injective
    exact Subtype.ext (map_add _ _ _)
  map_smul' a b := by
    apply toX_injective
    exact Subtype.ext (map_mul _ _ _)

lemma piP_surjective (hT : T' ⊆ D.T) (x : T') : Function.Surjective (D.piP hT x) := by
  intro m
  obtain ⟨c, hc⟩ := D.qmap_surjective T' (toX m).1
  have h1 : (c * D.e x.1) * D.e x.1 = c * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
  refine ⟨⟨c * D.e x.1, h1⟩, ?_⟩
  apply toX_injective
  apply Subtype.ext
  change D.qmap T' (c * D.e x.1) = (toX m).1
  rw [map_mul, hc]
  exact (toX m).2

lemma piP_ker (hT : T' ⊆ D.T) (x : T') (l : projE (k := k) (D.idem x.1)) (h0 : D.piP hT x l = 0) :
    l ∈ D.tr T' (projE (k := k) (D.idem x.1)) := by
  have h1 : D.qmap T' (l : A) = 0 := by
    have h := congrArg (fun z : resFD (D.qmap T') (projE (k := k) ((D.quotAny hT).idem x)) ↦
      ((toX z : leftIdeal ((D.quotAny hT).idem x)) : D.QAlg T')) h0
    exact h
  have h2 := D.mem_outIdeal_of_qmap (l : A) h1
  have h3 : ∀ m ∈ D.outIdeal T', ∀ hm : m * D.e x.1 * D.e x.1 = m * D.e x.1,
      (⟨m * D.e x.1, hm⟩ : projE (k := k) (D.idem x.1)) ∈
        D.tr T' (projE (k := k) (D.idem x.1)) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨v, c, hv, rfl⟩ := hr
      intro hh
      have h4 : (c * D.e x.1) * D.e x.1 = c * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
      refine Submodule.subset_span ⟨v, ⟨c * D.e x.1, h4⟩, hv, Subtype.ext ?_⟩
      change D.e v * c * D.e x.1 = D.e v * (c * D.e x.1)
      rw [mul_assoc]
    | zero =>
      intro hh
      have : (⟨0 * D.e x.1, hh⟩ : projE (k := k) (D.idem x.1)) = 0 := Subtype.ext (zero_mul _)
      rw [this]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro hh
      have h4 : a * D.e x.1 * D.e x.1 = a * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
      have h5 : b * D.e x.1 * D.e x.1 = b * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
      have : (⟨(a + b) * D.e x.1, hh⟩ : projE (k := k) (D.idem x.1)) =
          ⟨a * D.e x.1, h4⟩ + ⟨b * D.e x.1, h5⟩ := Subtype.ext (add_mul _ _ _)
      rw [this]
      exact Submodule.add_mem _ (ha h4) (hb h5)
    | smul a b _ hb =>
      intro hh
      have h4 : b * D.e x.1 * D.e x.1 = b * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
      have : (⟨(a • b) * D.e x.1, hh⟩ : projE (k := k) (D.idem x.1)) =
          a • ⟨b * D.e x.1, h4⟩ := Subtype.ext (mul_assoc _ _ _)
      rw [this]
      exact Submodule.smul_mem _ a (hb h4)
  have h6 : (l : A) * D.e x.1 = l := l.2
  have hh : (l : A) * D.e x.1 * D.e x.1 = (l : A) * D.e x.1 := by rw [mul_assoc, D.e_mul_e]
  have h7 := h3 _ h2 hh
  have h8 : (⟨(l : A) * D.e x.1, hh⟩ : projE (k := k) (D.idem x.1)) = l := Subtype.ext h6
  rwa [h8] at h7

/-- **Chains ending at a projective of the quotient lift.** -/
theorem chain_lift (hT : T' ⊆ D.T) (x : T') (hL : IndNT (projE (k := k) (D.idem x.1))) :
    ∀ {n : ℕ} {M' : FDMod k (D.QAlg T')},
      ChainTo (projE (k := k) ((D.quotAny hT).idem x)) n M' →
      ∃ (L' : FDMod k A) (π' : L' →ₗ[A] resFD (D.qmap T') M'),
        ChainTo (projE (k := k) (D.idem x.1)) n L' ∧ Function.Surjective π' ∧
          ∀ l, π' l = 0 → l ∈ D.tr T' L' := by
  intro n M' h
  induction h with
  | nil _ => exact ⟨_, D.piP hT x, ChainTo.nil hL, D.piP_surjective hT x, D.piP_ker hT x⟩
  | step _ hW f hf hnb ih =>
    obtain ⟨L, π, hc, hs, hk⟩ := ih
    obtain ⟨L', π', g, hL', hs', hk', hg, hgb⟩ := lift_step π hs hk hW f hf hnb
    exact ⟨L', π', ChainTo.step hc hL' g hg hgb, hs', hk'⟩

/-- **Projectives of a quotient are good if those of `A` are** (ASS IX.5.2). -/
theorem good_quot (hT : T' ⊆ D.T) (x : T') (hg : Good (projE (k := k) (D.idem x.1))) :
    Good (projE (k := k) ((D.quotAny hT).idem x)) := by
  obtain ⟨N, hN⟩ := hg.chain_bdd
  refine good_of_bdd N _ ((D.quotAny hT).projIndNT x (Set.mem_univ x)) fun n X h ↦ ?_
  obtain ⟨L', -, hc, -⟩ := chain_lift hT x hg.1 h
  exact hN n L' hc

end DirData

end LargeIndecomposable.AR
