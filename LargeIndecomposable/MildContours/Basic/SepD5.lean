module

public import LargeIndecomposable.MildContours.Basic.Separated
public import LargeIndecomposable.Cleaving.Shapes.ShapeSD5
public import LargeIndecomposable.Cleaving.Shapes.ShapeOut4
public import LargeIndecomposable.Cleaving.Shapes.ShapeSD6

/-!
# Separated-quiver `D̃₅` at a loop

A loop `ρ` at `x` together with two further distinct arrows out of `x` and two
further distinct arrows into `x` gives a `D̃₅` in the separated quiver
(`x⁺ → x⁻` along `ρ`). Made of arrows only, it cleaves into every proper
residue `P/τ` with `τ` not irreducible (`MildHyp.not_loop_d5`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- **No loop with three arrows out and three arrows in.** -/
theorem MildHyp.not_loop_d5 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτi : ¬IsIrreducible τ) {x u v z t : RayVert P} (ρ : x ⟶ x)
    (ea : x ⟶ u) (eb : x ⟶ v) (eα : z ⟶ x) (eβ : t ⟶ x)
    (h1 : ¬∃ h : x = u, HEq ρ ea) (h2 : ¬∃ h : x = v, HEq ρ eb) (h3 : ¬∃ h : u = v, HEq ea eb)
    (h4 : ¬∃ h : x = z, HEq ρ eα) (h5 : ¬∃ h : x = t, HEq ρ eβ) (h6 : ¬∃ h : z = t, HEq eα eβ) :
    False := by
  have o1 := arrows_out_apart ρ ea h1
  have o2 := arrows_out_apart ρ eb h2
  have o3 := arrows_out_apart ea eb h3
  have i1 := arrows_in_apart ρ eα h4
  have i2 := arrows_in_apart ρ eβ h5
  have i3 := arrows_in_apart eα eβ h6
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism τ e.1 :=
    fun e ↦ not_ftm_of_irreducible hτ hτi e.2
  exact hM.not_sd5 τ hτ hτ0 ρ.1 ea.1 eb.1 eα.1 eβ.1 (hf ρ) (hf ea) (hf eb) (hf eα) (hf eβ)
    ρ.2.2.1 ea.2.2.1 eb.2.2.1 eα.2.2.1 eβ.2.2.1 o1.1 o2.1 o1.2 o3.1 o2.2 o3.2
    (fun ⟨g, hg⟩ ↦ i1.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i2.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i1.1 ⟨g, hg⟩)
    (fun ⟨g, hg⟩ ↦ i3.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i2.1 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i3.1 ⟨g, hg⟩)

/-- **No arrow with two further arrows out of its source and two further arrows into
its target** (separated-quiver `D̃₅`). -/
theorem MildHyp.not_arrow_d5 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτi : ¬IsIrreducible τ) {x y u v z t : RayVert P} (ρ : x ⟶ y)
    (ea : x ⟶ u) (eb : x ⟶ v) (eα : z ⟶ y) (eβ : t ⟶ y)
    (h1 : ¬∃ h : y = u, HEq ρ ea) (h2 : ¬∃ h : y = v, HEq ρ eb) (h3 : ¬∃ h : u = v, HEq ea eb)
    (h4 : ¬∃ h : x = z, HEq ρ eα) (h5 : ¬∃ h : x = t, HEq ρ eβ) (h6 : ¬∃ h : z = t, HEq eα eβ) :
    False := by
  have o1 := arrows_out_apart ρ ea h1
  have o2 := arrows_out_apart ρ eb h2
  have o3 := arrows_out_apart ea eb h3
  have i1 := arrows_in_apart ρ eα h4
  have i2 := arrows_in_apart ρ eβ h5
  have i3 := arrows_in_apart eα eβ h6
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism τ e.1 :=
    fun e ↦ not_ftm_of_irreducible hτ hτi e.2
  exact hM.not_sd5 τ hτ hτ0 ρ.1 ea.1 eb.1 eα.1 eβ.1 (hf ρ) (hf ea) (hf eb) (hf eα) (hf eβ)
    ρ.2.2.1 ea.2.2.1 eb.2.2.1 eα.2.2.1 eβ.2.2.1 o1.1 o2.1 o1.2 o3.1 o2.2 o3.2
    (fun ⟨g, hg⟩ ↦ i1.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i2.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i1.1 ⟨g, hg⟩)
    (fun ⟨g, hg⟩ ↦ i3.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i2.1 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i3.1 ⟨g, hg⟩)

/-- **No point with four distinct arrows out** (`D̃₄` star). -/
theorem MildHyp.not_four_out (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτi : ¬IsIrreducible τ) {y u v w t : RayVert P} (e₁ : y ⟶ u) (e₂ : y ⟶ v)
    (e₃ : y ⟶ w) (e₄ : y ⟶ t)
    (h12 : ¬∃ h : u = v, HEq e₁ e₂) (h13 : ¬∃ h : u = w, HEq e₁ e₃) (h14 : ¬∃ h : u = t, HEq e₁ e₄)
    (h23 : ¬∃ h : v = w, HEq e₂ e₃) (h24 : ¬∃ h : v = t, HEq e₂ e₄)
    (h34 : ¬∃ h : w = t, HEq e₃ e₄) : False := by
  have o12 := arrows_out_apart e₁ e₂ h12
  have o13 := arrows_out_apart e₁ e₃ h13
  have o14 := arrows_out_apart e₁ e₄ h14
  have o23 := arrows_out_apart e₂ e₃ h23
  have o24 := arrows_out_apart e₂ e₄ h24
  have o34 := arrows_out_apart e₃ e₄ h34
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism τ e.1 :=
    fun e ↦ not_ftm_of_irreducible hτ hτi e.2
  exact hM.not_out4 τ hτ hτ0 e₁.1 e₂.1 e₃.1 e₄.1 (hf e₁) (hf e₂) (hf e₃) (hf e₄)
    e₁.2.2.1 e₂.2.2.1 e₃.2.2.1 e₄.2.2.1 o12.1 o13.1 o14.1 o12.2 o23.1 o24.1 o13.2 o23.2 o34.1
    o14.2 o24.2 o34.2

/-- **Separated-quiver `D̃₆`**: three distinct arrows out of `p`, three distinct arrows
out of `r`, one from each ending at a common `q`. -/
theorem MildHyp.not_sep_d6 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτi : ¬IsIrreducible τ) {p q r c c₂ s t : RayVert P}
    (eγ : p ⟶ c) (eγ' : p ⟶ c₂) (eβ : p ⟶ q) (eρ : r ⟶ q) (ea : r ⟶ s) (eε : r ⟶ t)
    (h1 : ¬∃ h : c = c₂, HEq eγ eγ') (h2 : ¬∃ h : c = q, HEq eγ eβ) (h3 : ¬∃ h : c₂ = q, HEq eγ' eβ)
    (h4 : ¬∃ h : q = s, HEq eρ ea) (h5 : ¬∃ h : q = t, HEq eρ eε) (h6 : ¬∃ h : s = t, HEq ea eε)
    (h7 : ¬∃ h : p = r, HEq eβ eρ) : False := by
  have o1 := arrows_out_apart eγ eγ' h1
  have o2 := arrows_out_apart eγ eβ h2
  have o3 := arrows_out_apart eγ' eβ h3
  have o4 := arrows_out_apart eρ ea h4
  have o5 := arrows_out_apart eρ eε h5
  have o6 := arrows_out_apart ea eε h6
  have i1 := arrows_in_apart eβ eρ h7
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism τ e.1 :=
    fun e ↦ not_ftm_of_irreducible hτ hτi e.2
  exact hM.not_sd6 τ hτ hτ0 eγ.1 eγ'.1 eβ.1 eρ.1 ea.1 eε.1 (hf eγ) (hf eγ') (hf eβ) (hf eρ)
    (hf ea) (hf eε) eγ.2.2.1 eγ'.2.2.1 eβ.2.2.1 eρ.2.2.1 ea.2.2.1 eε.2.2.1
    o1.1 o2.1 o1.2 o3.1 o2.2 o3.2 o4.1 o5.1 o4.2 o6.1 o5.2 o6.2
    (fun ⟨g, hg⟩ ↦ i1.2 ⟨g, hg⟩) (fun ⟨g, hg⟩ ↦ i1.1 ⟨g, hg⟩)

end RayCat

end LargeIndecomposable
