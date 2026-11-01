module

public import LargeIndecomposable.Modules.Homological.Radical

/-!
# Separating points

`QSet x` is the set of live non-predecessors of `x`. A decomposition of `rad P(x)` into
indecomposables separates `x` if the supports of different summands are not connected inside
`QSet x` (`SepDecomp`); `x` is separating when such a decomposition exists. Helper facts on supports: invariance under isomorphism,
nonemptiness, supports of summands of `rad P(x)` lie in `QSet x`, and a nonzero quotient of
`rad P(y)` lives at a neighbour of `y` (`exists_nbr`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A)

/-- Live non-predecessors of `x`. -/
def QSet (x : D.ι) : Set D.ι := {y | y ∈ D.T ∧ ¬Relation.ReflTransGen D.Arr y x}

/-- Adjacency inside a set. -/
def Adj (S : Set D.ι) (a b : D.ι) : Prop := a ∈ S ∧ b ∈ S ∧ (D.Arr a b ∨ D.Arr b a)

/-- Connectedness inside a set. -/
def Conn (S : Set D.ι) : D.ι → D.ι → Prop := Relation.ReflTransGen (D.Adj S)

/-- **Separating points.** -/
def SepDecomp (x : D.ι) (d : Decomp (D.RadP x)) : Prop :=
  ∀ (i j : d.ι), i ≠ j → ∀ u v, u ∈ D.Supp (d.obj i) → v ∈ D.Supp (d.obj j) →
    ¬D.Conn (D.QSet x) u v

variable {D}

lemma conn_symm {S : Set D.ι} {a b : D.ι} (h : D.Conn S a b) : D.Conn S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    exact Relation.ReflTransGen.head ⟨h2.2.1, h2.1, h2.2.2.symm⟩ ih

lemma conn_mono {S S' : Set D.ι} (hSS : S ⊆ S') {a b : D.ι} (h : D.Conn S a b) : D.Conn S' a b :=
  rtg_mono (fun _ _ h ↦ ⟨hSS h.1, hSS h.2.1, h.2.2⟩) h

lemma conn_mem {S : Set D.ι} {a b : D.ι} (ha : a ∈ S) (h : D.Conn S a b) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ h2 _ => exact h2.2.1

/-- Supports are invariant under isomorphism. -/
lemma supp_iso {M N : FDMod k A} (h : IsoM M N) : D.Supp M ⊆ D.Supp N := by
  rintro y ⟨m, hm⟩
  obtain ⟨g, hg⟩ := h
  refine ⟨FDMod.lin g m, fun h0 ↦ hm (hg.1 ?_)⟩
  rw [map_smul, h0, map_zero]

/-- Supports of nonzero modules are nonempty. -/
lemma supp_nonempty (M : FDMod k A) [Nontrivial M] : (D.Supp M).Nonempty := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hm
  have hm1 : m = ∑ y, D.e y • m := by rw [← Finset.sum_smul, D.sum, one_smul]
  rw [hm1]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  by_contra hy
  have : y ∈ D.Supp M := ⟨m, hy⟩
  rw [h] at this
  exact this

/-- Supports along surjections. -/
lemma supp_of_surj {M N : FDMod k A} (g : M ⟶ N) (hg : Function.Surjective (FDMod.lin g)) :
    D.Supp N ⊆ D.Supp M := by
  rintro y ⟨n, hn⟩
  obtain ⟨m, rfl⟩ := hg n
  exact ⟨m, fun h0 ↦ hn (by rw [← map_smul, h0, map_zero])⟩

/-- Supports along injections. -/
lemma supp_of_inj {M N : FDMod k A} (g : M ⟶ N) (hg : Function.Injective (FDMod.lin g)) :
    D.Supp M ⊆ D.Supp N := by
  rintro y ⟨m, hm⟩
  exact ⟨FDMod.lin g m, fun h0 ↦ hm (hg (by rw [map_smul, h0, map_zero]))⟩

lemma decomp_inc_inj {E : FDMod k A} (d : Decomp E) (i : d.ι) :
    Function.Injective (FDMod.lin (d.inc i)) := fun a b h ↦ by
  have := congrArg (FDMod.lin (d.proj i)) h
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, d.retr i] at this

lemma decomp_proj_surj {E : FDMod k A} (d : Decomp E) (i : d.ι) :
    Function.Surjective (FDMod.lin (d.proj i)) := fun m ↦
  ⟨FDMod.lin (d.inc i) m, LinearMap.congr_fun (d.retr i) m⟩

lemma supp_summand {E : FDMod k A} (d : Decomp E) (i : d.ι) :
    D.Supp (d.obj i) ⊆ D.Supp E := supp_of_inj _ (decomp_inc_inj d i)

/-- Supports of `rad P(x)` lie among the non-predecessors of `x`. -/
lemma supp_radP_sub (x : D.ι) : D.Supp (D.RadP x) ⊆ D.QSet x := by
  rintro u ⟨m, hm⟩
  let p : projE (k := k) (D.idem x) := (m : D.radP x)
  let a : A := (p : A)
  have hm' : D.e u * a ≠ 0 := fun h0 ↦ hm (Subtype.ext (Subtype.ext h0))
  have hmx : a * D.e x = a := p.2
  have hrad : D.e x * a = 0 := (m : D.radP x).2
  have hux : u ≠ x := by
    rintro rfl
    exact hm' hrad
  have hne : D.e u * a * D.e x ≠ 0 := by
    rwa [mul_assoc, hmx]
  have hpath := D.hom x u _ hne
  have huT : u ∈ D.T := by
    by_contra hu
    apply hne
    rw [D.zero u hu, zero_mul, zero_mul]
  refine ⟨huT, fun h ↦ D.acyc x u (D.transGen_of_ne hpath (Ne.symm hux)) h⟩

/-- **A nonzero quotient of `rad P(y)` lives at a neighbour of `y`.** -/
lemma exists_nbr (y : D.ι) {M : FDMod k A} [Nontrivial M] (g : D.RadP y ⟶ M)
    (hg : Function.Surjective (FDMod.lin g)) : ∃ y', D.Arr y y' ∧ y' ∈ D.Supp M := by
  classical
  by_contra hno
  push Not at hno
  -- the generators `e_{y'} b e_y` of the radical
  have hgen : ∀ y' b, D.Arr y y' → D.e y * (D.e y' * b * D.e y) = 0 := fun y' b h ↦ by
    rw [← mul_assoc, ← mul_assoc, D.orth y y' (D.ne_of_arr h), zero_mul, zero_mul]
  let G : Set (D.RadP y) := {r | ∃ y' b, D.Arr y y' ∧ ((r : projE (k := k) (D.idem y)) : A) =
    D.e y' * b * D.e y}
  have hG : Submodule.span A G = ⊤ := by
    let ι : D.radP y →ₗ[A] A :=
      (leftIdeal (D.idem y)).subtype ∘ₗ (D.radP y).subtype
    have hι : Function.Injective ι := fun a b h ↦ Subtype.ext (Subtype.ext h)
    have himg : ι '' G = {r | ∃ y' b, D.Arr y y' ∧ r = D.e y' * b * D.e y} := by
      ext r
      constructor
      · rintro ⟨g, ⟨y', b, h, hg⟩, rfl⟩
        exact ⟨y', b, h, hg⟩
      · rintro ⟨y', b, h, rfl⟩
        have h1 : D.e y' * b * D.e y ∈ leftIdeal (D.idem y) := by
          change D.e y' * b * D.e y * D.e y = D.e y' * b * D.e y
          rw [mul_assoc, D.e_mul_e]
        have h2 : (⟨D.e y' * b * D.e y, h1⟩ : projE (k := k) (D.idem y)) ∈ D.radP y :=
          hgen y' b h
        exact ⟨⟨_, h2⟩, ⟨y', b, h, rfl⟩, rfl⟩
    rw [eq_top_iff]
    intro r _
    have hr : ι r ∈ Submodule.span A (ι '' G) := by
      rw [himg]
      have ha : ι r = (1 - D.e y) * ι r * D.e y := by
        have h1 : D.e y * ι r = 0 := r.2
        have h2 : ι r * D.e y = ι r := (r : projE (k := k) (D.idem y)).2
        rw [sub_mul, one_mul, h1, sub_zero, h2]
      rw [ha]
      exact D.gen y (ι r)
    rw [← Submodule.map_span] at hr
    obtain ⟨g, hg, hgr⟩ := hr
    rwa [← hι hgr]
  have hzero : ∀ r ∈ G, FDMod.lin g r = 0 := by
    rintro r ⟨y', b, h, hr⟩
    have hr' : r = D.e y' • r := by
      apply Subtype.ext; apply Subtype.ext
      change ((r : projE (k := k) (D.idem y)) : A) = D.e y' * (r : A)
      rw [hr, ← mul_assoc, ← mul_assoc, D.e_mul_e]
    rw [hr', map_smul]
    by_contra h0
    exact hno y' h ⟨_, h0⟩
  have key : ∀ r, r ∈ Submodule.span A G → FDMod.lin g r = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr => exact hzero r hr
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [map_smul, hb, smul_zero]
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨r, rfl⟩ := hg m
  exact hm (key r (by rw [hG]; trivial))

end DirData

end LargeIndecomposable.AR
