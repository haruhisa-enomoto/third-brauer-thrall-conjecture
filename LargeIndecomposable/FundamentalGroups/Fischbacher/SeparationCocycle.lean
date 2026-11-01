module

public import LargeIndecomposable.FundamentalGroups.Basic.Cocycle

/-!
# The separation step in cocycle form

Cocycles and coboundaries on a set `D` of objects (`IsCocycleOn`, `IsCoboundaryOn`) only see
paths and arrows inside `D`. Let `b ∈ D` admit no arrow into `D`. If every cocycle on `D` is a
coboundary on `D`, then two arrows into `b` whose sources are joined by a walk in `D \ {b}`
lie in the same connected component of the poset of nonzero morphisms into `b` from
`D \ {b}` (`sepComp_of_coboundary`): weight `1` on the arrows into `b` from one component is a
cocycle on `D`. This is the separation property of Bautista–Larrión used in Fischbacher's
Lemma 4.2, in the direction needed there.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- All vertices of a path lie in `H`. -/
def PathIn (H : Set A) {x : RayVert A} : ∀ {y : RayVert A}, Quiver.Path x y → Prop
  | _, .nil => x.out ∈ H
  | y, .cons p _ => PathIn H p ∧ y.out ∈ H

/-- A cocycle on the paths inside `H`. -/
def IsCocycleOn (H : Set A) (c : ArrowWeight A) : Prop :=
  ∀ {x y : RayVert A} (p q : Quiver.Path x y), PathIn H p → PathIn H q →
    pathVal p = pathVal q → pathVal p ≠ 0 → pathWeight c p = pathWeight c q

/-- A coboundary on the arrows inside `H`. -/
def IsCoboundaryOn (H : Set A) (c : ArrowWeight A) : Prop :=
  ∃ φ : A → ℤ, ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ H → y.out ∈ H → c e = φ y.out - φ x.out

variable (D : Set A) (b : A)

/-- Comparability of nonzero morphisms into `b` with source in `D \ {b}`: `g = h ≫ f`. -/
def SepLe (f g : Σ x : A, x ⟶ b) : Prop :=
  f.2 ≠ 0 ∧ g.2 ≠ 0 ∧ f.1 ∈ D ∧ g.1 ∈ D ∧ f.1 ≠ b ∧ g.1 ≠ b ∧ ∃ h : g.1 ⟶ f.1, g.2 = h ≫ f.2

/-- The connected components of the poset of nonzero morphisms into `b`. -/
def SepComp (f g : Σ x : A, x ⟶ b) : Prop := Relation.EqvGen (SepLe D b) f g

/-- Adjacency by an arrow inside `D \ {b}`. -/
def AdjOff (s t : A) : Prop :=
  s ∈ D ∧ t ∈ D ∧ s ≠ b ∧ t ≠ b ∧
    (Nonempty (RayVert.mk s ⟶ RayVert.mk t) ∨ Nonempty (RayVert.mk t ⟶ RayVert.mk s))

variable {D b}

section Weight

variable (t₁ : A) (e₁ : t₁ ⟶ b)

open Classical in
/-- Weight `1` on the arrows into `b` from `D \ {b}` in the component of `e₁`. -/
def sepWeight : ArrowWeight A := fun {x y} e ↦
  if ∃ h : y.out = b, x.out ∈ D ∧ x.out ≠ b ∧ SepComp D b ⟨t₁, e₁⟩ ⟨x.out, e.1 ≫ eqToHom h⟩
  then 1 else 0

lemma sepWeight_eq_zero {x y : RayVert A} (e : x ⟶ y) (hy : y.out ≠ b) :
    sepWeight (D := D) t₁ e₁ e = 0 := by
  unfold sepWeight
  rw [if_neg]
  rintro ⟨h, -⟩
  exact hy h

variable (hmax : ∀ {y : RayVert A} (_ : RayVert.mk b ⟶ y), y.out ∉ D)
include hmax

lemma pathWeight_sep_eq_zero {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    PathIn D p → y.out ≠ b → pathWeight (sepWeight (D := D) t₁ e₁) p = 0
  | _, .nil, _, _ => rfl
  | _, .cons (b := y') p e, hp, hy => by
    have hy' : y'.out ≠ b := by
      intro h
      obtain rfl : y' = RayVert.mk b := h
      exact hmax e hp.2
    rw [pathWeight, pathWeight_sep_eq_zero p hp.1 hy', sepWeight_eq_zero t₁ e₁ e hy, add_zero]

omit hmax in
lemma PathIn.start {x : RayVert A} : ∀ {y : RayVert A} {p : Quiver.Path x y},
    PathIn D p → x.out ∈ D
  | _, .nil, h => h
  | _, .cons p _, h => PathIn.start (p := p) h.1

omit hmax in
lemma PathIn.target {x : RayVert A} : ∀ {y : RayVert A} {p : Quiver.Path x y},
    PathIn D p → y.out ∈ D
  | _, .nil, h => h
  | _, .cons _ _, h => h.2

omit t₁ e₁ in
lemma length_zero_of_start {x : RayVert A} (hx : x.out = b) :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn D p → p.length = 0
  | _, .nil, _ => rfl
  | _, .cons (b := y') p e, hp => by
    have h0 := length_zero_of_start hx p hp.1
    have hxy := Quiver.Path.eq_of_length_zero p h0
    subst hxy
    obtain rfl : x = RayVert.mk b := hx
    exact absurd hp.2 (hmax e)

omit t₁ e₁ in
lemma ne_of_arrow {y' y : RayVert A} (e : y' ⟶ y) (hy : y.out ∈ D) : y'.out ≠ b := by
  intro h
  obtain rfl : y' = RayVert.mk b := h
  exact hmax e hy

lemma isCocycleOn_sepWeight : IsCocycleOn D (sepWeight (D := D) t₁ e₁) := by
  intro x y p q hp hq hpq h0
  by_cases hy : y.out = b
  swap
  · rw [pathWeight_sep_eq_zero t₁ e₁ hmax p hp hy, pathWeight_sep_eq_zero t₁ e₁ hmax q hq hy]
  obtain rfl : RayVert.mk b = y := hy.symm
  by_cases hx : x.out = b
  · obtain rfl : RayVert.mk b = x := hx.symm
    rw [Quiver.Path.eq_nil_of_length_zero p (length_zero_of_start hmax rfl p hp),
      Quiver.Path.eq_nil_of_length_zero q (length_zero_of_start hmax rfl q hq)]
  rcases p with _ | ⟨p', ep⟩
  · exact absurd rfl hx
  rcases q with _ | ⟨q', eq⟩
  · exact absurd rfl hx
  have hp' := ne_of_arrow hmax ep hp.2
  have hq' := ne_of_arrow hmax eq hq.2
  rw [pathWeight, pathWeight, pathWeight_sep_eq_zero t₁ e₁ hmax p' hp.1 hp',
    pathWeight_sep_eq_zero t₁ e₁ hmax q' hq.1 hq', zero_add, zero_add]
  have hxD : x.out ∈ D := PathIn.start hp
  have hcp : SepComp D b ⟨_, ep.1⟩ ⟨x.out, pathVal p' ≫ ep.1⟩ :=
    Relation.EqvGen.rel _ _ ⟨ep.2.1, h0, PathIn.target hp.1, hxD, hp', hx, pathVal p', rfl⟩
  have hval : pathVal p' ≫ ep.1 = pathVal q' ≫ eq.1 := hpq
  have hcq : SepComp D b ⟨_, eq.1⟩ ⟨x.out, pathVal q' ≫ eq.1⟩ :=
    Relation.EqvGen.rel _ _ ⟨eq.2.1, fun h ↦ h0 (hval.trans h), PathIn.target hq.1, hxD, hq', hx,
      pathVal q', rfl⟩
  rw [hval] at hcp
  have hpq' : SepComp D b ⟨_, ep.1⟩ ⟨_, eq.1⟩ := hcp.trans _ _ _ hcq.symm
  have E : ∀ {s : A} (g : s ⟶ b) (h : b = b), g ≫ eqToHom h = g := fun g _ ↦ by simp
  unfold sepWeight
  classical
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨h, -, -, hc⟩
    refine ⟨h, PathIn.target hq.1, hq', ?_⟩
    rw [E] at hc ⊢
    exact hc.trans _ _ _ hpq'
  · rintro ⟨h, -, -, hc⟩
    refine ⟨h, PathIn.target hp.1, hp', ?_⟩
    rw [E] at hc ⊢
    exact hc.trans _ _ _ hpq'.symm

end Weight

lemma eq_of_adjOff (φ : A → ℤ) (c : ArrowWeight A)
    (hφ : ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ D → y.out ∈ D → c e = φ y.out - φ x.out)
    (h0 : ∀ {x y : RayVert A} (e : x ⟶ y), x.out ≠ b → y.out ≠ b → c e = 0) {s t : A}
    (h : Relation.EqvGen (AdjOff D b) s t) : φ s = φ t := by
  induction h with
  | rel s t hst =>
    obtain ⟨hs, ht, hsb, htb, he⟩ := hst
    rcases he with he | he
    · obtain ⟨e⟩ := he
      have h := hφ e hs ht
      rw [h0 e hsb htb] at h
      change 0 = φ t - φ s at h
      omega
    · obtain ⟨e⟩ := he
      have h := hφ e ht hs
      rw [h0 e htb hsb] at h
      change 0 = φ s - φ t at h
      omega
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- **The separation step.** If every cocycle on `D` is a coboundary and `b ∈ D` admits no arrow
into `D`, two arrows into `b` whose sources are joined by a walk in `D \ {b}` lie in the same
component of the nonzero morphisms into `b`. -/
theorem sepComp_of_coboundary (hb : b ∈ D) (hmax : ∀ {y : RayVert A} (_ : RayVert.mk b ⟶ y), y.out ∉ D)
    (hcob : ∀ c : ArrowWeight A, IsCocycleOn D c → IsCoboundaryOn D c) {t₁ t₂ : A}
    (e₁ : RayVert.mk t₁ ⟶ RayVert.mk b) (e₂ : RayVert.mk t₂ ⟶ RayVert.mk b) (ht₁ : t₁ ∈ D)
    (ht₂ : t₂ ∈ D) (h₁ : t₁ ≠ b) (h₂ : t₂ ≠ b) (hconn : Relation.EqvGen (AdjOff D b) t₁ t₂) :
    SepComp D b ⟨t₁, e₁.1⟩ ⟨t₂, e₂.1⟩ := by
  classical
  obtain ⟨φ, hφ⟩ := hcob _ (isCocycleOn_sepWeight t₁ e₁.1 hmax)
  have hφeq : φ t₁ = φ t₂ :=
    eq_of_adjOff φ _ hφ (fun e _ hy ↦ sepWeight_eq_zero t₁ e₁.1 e hy) hconn
  have hw₁ : sepWeight (D := D) t₁ e₁.1 e₁ = 1 := by
    unfold sepWeight
    rw [if_pos]
    refine ⟨rfl, ht₁, h₁, ?_⟩
    simp only [eqToHom_refl, Category.comp_id]
    exact Relation.EqvGen.refl _
  have hw₂ : sepWeight (D := D) t₁ e₁.1 e₂ = 1 := by
    have a₁ := hφ e₁ ht₁ hb
    have a₂ := hφ e₂ ht₂ hb
    change sepWeight t₁ e₁.1 e₁ = φ b - φ t₁ at a₁
    change sepWeight t₁ e₁.1 e₂ = φ b - φ t₂ at a₂
    omega
  unfold sepWeight at hw₂
  split_ifs at hw₂ with hc
  · obtain ⟨h, -, -, hc⟩ := hc
    simpa using hc
  · exact absurd hw₂ (by norm_num)

end LargeIndecomposable.RayCat
