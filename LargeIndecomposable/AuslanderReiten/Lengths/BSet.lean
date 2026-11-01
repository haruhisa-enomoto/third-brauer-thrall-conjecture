module

public import LargeIndecomposable.DirectedAlgebras.Directing.ProjClass

/-!
# The subcategory `B = Bᵢ(x)`

`B` is closed under successors (`Bset_succ`) and convex (`Bset_convex`); the summand `Rᵢ(x)` lives
on `B` (`livesOn_R`), and so does `P(z)` for `z ∈ B` (`livesOn_proj`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} (x : D.ι) (d : Decomp (D.RadP x)) (i : d.ι)

/-- **`B` is closed under arrows.** -/
lemma Bset_arr {b c : D.ι} (hb : b ∈ Bset x d i) (h : D.Arr b c) : c ∈ Bset x d i := by
  obtain ⟨u, hu, hc⟩ := hb
  have hbQ : b ∈ D.QSet x := Bset_sub x d i ⟨u, hu, hc⟩
  have hcQ : c ∈ D.QSet x :=
    ⟨(D.arrT b c h).2, fun h' ↦ hbQ.2 (Relation.ReflTransGen.head h h')⟩
  exact ⟨u, hu, hc.tail ⟨hbQ, hcQ, Or.inl h⟩⟩

/-- **`B` is closed under successors.** -/
lemma Bset_succ {b c : D.ι} (hb : b ∈ Bset x d i) (h : Relation.ReflTransGen D.Arr b c) :
    c ∈ Bset x d i := by
  induction h with
  | refl => exact hb
  | tail _ h2 ih => exact Bset_arr x d i ih h2

/-- **`B` is convex.** -/
lemma Bset_convex : D.ConvexSet (Bset x d i) :=
  ⟨fun b hb ↦ (Bset_sub x d i hb).1, fun a b _ ha _ hab _ ↦ Bset_succ x d i ha hab⟩

/-- **`Rᵢ(x)` lives on `B`.** -/
lemma livesOn_R : LivesOn (Bset x d i) (d.obj i) := by
  rw [livesOn_iff_supp]
  intro u hu
  exact ⟨u, hu, Relation.ReflTransGen.refl⟩

/-- The support of `P(z)` consists of successors of `z`. -/
lemma supp_proj (z : D.ι) {y : D.ι} (hy : y ∈ D.Supp (projE (k := k) (D.idem z))) :
    Relation.ReflTransGen D.Arr z y := by
  obtain ⟨m, hm⟩ := hy
  have hm' : D.e y * (m : A) ≠ 0 := fun h0 ↦ hm (Subtype.ext h0)
  have hmz : (m : A) * D.e z = m := m.2
  exact D.hom z y (m : A) (by rwa [mul_assoc, hmz])

/-- **`P(z)` lives on `B` for `z ∈ B`.** -/
lemma livesOn_proj {z : D.ι} (hz : z ∈ Bset x d i) :
    LivesOn (Bset x d i) (projE (k := k) (D.idem z)) := by
  rw [livesOn_iff_supp]
  intro y hy
  exact Bset_succ x d i hz (supp_proj z hy)

end DirData

end LargeIndecomposable.AR
