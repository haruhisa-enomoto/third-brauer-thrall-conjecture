module

public import LargeIndecomposable.DirectedAlgebras.Separation.Separation

/-!
# Bongartz's Lemma 2.4 (a)

Fix separating decompositions `sd z` of all `rad P(z)`. For a point `x` and a summand `R = (sd x)ᵢ`,
let `B` be the points connected inside `QSet x` to the support of `R` (`Bset`). If an
indecomposable module `U` supported in `B` maps irreducibly to a projective `P(y)`, then `y ∈ B`,
or `y = x` and `U ≅ R` (`lemma24a`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A}

/-- The component of `QSet x` containing the support of a summand. -/
def Bset (x : D.ι) (d : Decomp (D.RadP x)) (i : d.ι) : Set D.ι :=
  {b | ∃ u ∈ D.Supp (d.obj i), D.Conn (D.QSet x) u b}

lemma Bset_sub (x : D.ι) (d : Decomp (D.RadP x)) (i : d.ι) : Bset x d i ⊆ D.QSet x := by
  rintro b ⟨u, hu, hc⟩
  exact conn_mem (supp_radP_sub x (supp_summand d i hu)) hc

/-- A walk from a successor of `y` along arrows stays among the non-predecessors of `y`. -/
lemma conn_of_path {y a b : D.ι} (hya : Relation.TransGen D.Arr y a)
    (hab : Relation.ReflTransGen D.Arr a b) : D.Conn (D.QSet y) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hac hcd ih =>
    rename_i c d
    have hyc : Relation.TransGen D.Arr y c := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hac with h | h
      · exact h ▸ hya
      · exact hya.trans h
    have hyd : Relation.TransGen D.Arr y d := hyc.tail hcd
    have hmem : ∀ w, Relation.TransGen D.Arr y w → w ∈ D.QSet y := by
      intro w h
      obtain ⟨w', _, h'⟩ := Relation.TransGen.tail'_iff.1 h
      exact ⟨(D.arrT w' w h').2, D.acyc y w h⟩
    exact Relation.ReflTransGen.tail ih ⟨hmem c hyc, hmem d hyd, Or.inl hcd⟩

/-- An arrow target lies in the support of some summand of the radical. -/
lemma exists_summand_supp {y z : D.ι} (h : D.Arr y z) (d : Decomp (D.RadP y)) :
    ∃ j, z ∈ D.Supp (d.obj j) := by
  classical
  obtain ⟨a, ha⟩ := D.arrNe y z h
  have h1 : D.e z * a * D.e y ∈ leftIdeal (D.idem y) := by
    change D.e z * a * D.e y * D.e y = D.e z * a * D.e y
    rw [mul_assoc, D.e_mul_e]
  have h2 : (⟨D.e z * a * D.e y, h1⟩ : projE (k := k) (D.idem y)) ∈ D.radP y := by
    change D.e y * (D.e z * a * D.e y) = 0
    rw [← mul_assoc, ← mul_assoc, D.orth y z (D.ne_of_arr h), zero_mul, zero_mul]
  let r : D.RadP y := ⟨_, h2⟩
  have hr : D.e z • r ≠ 0 := by
    intro h0
    apply ha
    have := congrArg (fun t : D.RadP y ↦ (((t : D.radP y) : projE (k := k) (D.idem y)) : A)) h0
    simp only at this
    change D.e z * (D.e z * a * D.e y) = 0 at this
    rwa [← mul_assoc, ← mul_assoc, D.e_mul_e] at this
  by_contra hno
  push Not at hno
  apply hr
  have hsum : r = ∑ i, FDMod.lin (d.inc i) (FDMod.lin (d.proj i) r) := by
    have := LinearMap.congr_fun d.sum_id r
    simpa using this.symm
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← map_smul]
  by_contra h0
  exact hno i ⟨_, fun h' ↦ h0 (by rw [h', map_zero])⟩

/-- Points of the support of `rad P(x)` are reached from `x`. -/
lemma path_of_supp_radP {x u : D.ι} (hu : u ∈ D.Supp (D.RadP x)) :
    Relation.ReflTransGen D.Arr x u := by
  obtain ⟨m, hm⟩ := hu
  let p : projE (k := k) (D.idem x) := (m : D.radP x)
  let a : A := (p : A)
  have hm' : D.e u * a ≠ 0 := fun h0 ↦ hm (Subtype.ext (Subtype.ext h0))
  have hmx : a * D.e x = a := p.2
  exact D.hom x u a (by rwa [mul_assoc, hmx])

/-- Non-predecessors of `x` are non-predecessors of a predecessor `y` of `x`. -/
lemma qset_sub {x y : D.ι} (hyx : Relation.ReflTransGen D.Arr y x) : D.QSet x ⊆ D.QSet y :=
  fun _ hb ↦ ⟨hb.1, fun h ↦ hb.2 (h.trans hyx)⟩

/-- **Bongartz's Lemma 2.4 (a).** -/
theorem lemma24a (sd : ∀ z, Decomp (D.RadP z)) (hsd : ∀ z, z ∈ D.T → D.SepDecomp z (sd z))
    {x : D.ι} (i0 : (sd x).ι) {U : FDMod k A} (hU : IndNT U)
    (hUB : D.Supp U ⊆ Bset x (sd x) i0) {y : D.ι} (hy : y ∈ D.T)
    {f : U ⟶ projE (k := k) (D.idem y)} (hf : IsIrr f) :
    y ∈ Bset x (sd x) i0 ∨ (y = x ∧ IsoM U ((sd x).obj i0)) := by
  obtain ⟨v, -, r, hr⟩ := hf.factor_rightAS (D.isRightAS_radP y hy)
  obtain ⟨j, hj⟩ := iso_summand_of_splitMono hU (sd y) v r hr
  haveI := hU.2
  have hSU : D.Supp ((sd y).obj j) ⊆ D.Supp U := supp_iso hj.symm
  have hUS : D.Supp U ⊆ D.Supp ((sd y).obj j) := supp_iso hj
  obtain ⟨g, hg⟩ := hj.symm
  obtain ⟨y', hyy', hy'U⟩ := exists_nbr y ((sd y).proj j ≫ g)
    (hg.2.comp (decomp_proj_surj (sd y) j))
  have hBQ := Bset_sub x (sd x) i0
  by_cases hyQ : y ∈ D.QSet x
  · left
    obtain ⟨u, hu, hc⟩ := hUB hy'U
    exact ⟨u, hu, hc.tail ⟨hBQ (hUB hy'U), hyQ, Or.inr hyy'⟩⟩
  · have hyx' : Relation.ReflTransGen D.Arr y x := by
      by_contra h
      exact hyQ ⟨hy, h⟩
    by_cases hyx : y = x
    · subst hyx
      right
      refine ⟨rfl, ?_⟩
      by_cases hji : j = i0
      · subst hji
        exact hj
      · exfalso
        obtain ⟨u, hu, hc⟩ := hUB hy'U
        exact hsd y hy j i0 hji y' u (hUS hy'U) hu (conn_symm hc)
    · exfalso
      have hyxT := D.transGen_of_ne hyx' hyx
      obtain ⟨z, hyz, hzx⟩ := Relation.TransGen.head'_iff.1 hyxT
      obtain ⟨j', hj'⟩ := exists_summand_supp hyz (sd y)
      obtain ⟨u, hu, hc⟩ := hUB hy'U
      have hxu := path_of_supp_radP (supp_summand (sd x) i0 hu)
      have h1 : D.Conn (D.QSet y) z x := conn_of_path (Relation.TransGen.single hyz) hzx
      have h2 : D.Conn (D.QSet y) x u := conn_of_path hyxT hxu
      have h3 : ∀ w, D.Conn (D.QSet x) u w → D.Conn (D.QSet y) u w := by
        intro w hw
        induction hw with
        | refl => exact Relation.ReflTransGen.refl
        | tail hua hab ih =>
          rename_i a b
          exact ih.tail ⟨qset_sub hyx' hab.1, qset_sub hyx' hab.2.1, hab.2.2⟩
      have hconn := h1.trans (h2.trans (h3 y' hc))
      by_cases hjj : j' = j
      · subst hjj
        exact (hBQ (hUB (hSU hj'))).2 hzx
      · exact hsd y hy j' j hjj z y' hj' (hUS hy'U) hconn

end DirData

end LargeIndecomposable.AR
