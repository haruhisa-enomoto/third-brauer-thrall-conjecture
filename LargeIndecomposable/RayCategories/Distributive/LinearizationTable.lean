module

public import LargeIndecomposable.Cleaving.Functors.Cleaving
public import LargeIndecomposable.RayCategories.RayTables.TableOfBasis

/-!
# The multiplication table of the linearization of a ray category

The nonzero morphisms of a finite ray category `P` form a multiplicative basis
of `Linearization P k`. The ray table of that basis (`RayQuiver.linTable`, in
the sense of the multiplicative-bases library) has the nonzero
morphisms as rays, the codomain as source and the domain as target, and its
linearization is `Linearization P k` (`RayQuiver.linTableEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

universe u

namespace RayQuiver

variable (k : Type u) [Field k] (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P]

instance : Fintype (NZ P) := Fintype.ofFinite _

instance : DecidableEq (NZ P) := Classical.decEq _

variable {P}

lemma linBasis_eq_morElt (μ : NZ P) : linBasis k μ = morElt k μ.2.2.1 := by
  rw [linBasis_apply, morElt_of_ne k _ μ.2.2.2]

variable (P) in
/-- `linBasis`, typed with the module structure coming from the ring structure. -/
def linBasisR : @Module.Basis (NZ P) k (Linearization P k) _
    Ring.toSemiring.toNonUnitalSemiring.toNonUnitalNonAssocSemiring.toAddCommMonoid
    Algebra.toModule := by
  exact linBasis k

lemma linBasisR_apply (μ : NZ P) : linBasisR k P μ = morElt k μ.2.2.1 := by
  change linBasis k μ = _
  exact linBasis_eq_morElt k μ

/-- The identity of `x` as a basis index. -/
def idNZ (x : P) : NZ P := ⟨x, x, 𝟙 x, IsRayCategory.id_ne_zero x⟩

variable (P) in
lemma isMultiplicativeBasis_linBasis : IsMultiplicativeBasis (linBasisR k P) := by
  rintro ⟨a, b, f, hf⟩ ⟨c, d, g, hg⟩
  rw [linBasisR_apply, linBasisR_apply]
  by_cases hdb : d = a
  · subst hdb
    rw [morElt_mul]
    by_cases h0 : g ≫ f = 0
    · exact Or.inl (by rw [h0, morElt_zero])
    · exact Or.inr ⟨⟨c, b, g ≫ f, h0⟩, by rw [linBasisR_apply]⟩
  · exact Or.inl (morElt_mul_ne k g f hdb)

variable (P) in
lemma complete_linBasis_id :
    CompleteOrthogonalIdempotents fun x : P ↦ linBasisR k P (idNZ x) := by
  refine ⟨⟨fun x ↦ ?_, fun x y hxy ↦ ?_⟩, ?_⟩
  · change linBasisR k P (idNZ x) * linBasisR k P (idNZ x) = linBasisR k P (idNZ x)
    rw [linBasisR_apply, idNZ, morElt_mul, Category.comp_id]
  · change linBasisR k P (idNZ x) * linBasisR k P (idNZ y) = 0
    rw [linBasisR_apply, linBasisR_apply]
    exact morElt_mul_ne k _ _ (Ne.symm hxy)
  · simp only [linBasisR_apply, idNZ]
    exact sum_morElt_id k

lemma linBasis_corner (r : NZ P) :
    linBasisR k P (idNZ r.2.1) * linBasisR k P r * linBasisR k P (idNZ r.1) = linBasisR k P r := by
  obtain ⟨a, b, f, hf⟩ := r
  simp only [linBasisR_apply, idNZ]
  rw [morElt_mul, Category.comp_id, morElt_mul, Category.id_comp]

variable (P) in
/-- **The ray table of the linearization of `P`.** -/
def linTable : RaySys.Mult P (NZ P) :=
  RaySys.OfBasis.multOfBasis (linBasisR k P) (isMultiplicativeBasis_linBasis k P) idNZ
    (complete_linBasis_id k P) (fun r ↦ r.2.1) (fun r ↦ r.1) (linBasis_corner k)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

variable (P) in
/-- **The linearization of the ray table is the linearization of `P`.** -/
def linTableEquiv : (linTable k P).Lin k ≃ₐ[k] Linearization P k :=
  RaySys.OfBasis.linEquiv (linBasisR k P) (isMultiplicativeBasis_linBasis k P) idNZ
    (complete_linBasis_id k P) (fun r ↦ r.2.1) (fun r ↦ r.1) (linBasis_corner k)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

lemma linTable_mul_eq_some {r s t : NZ P} : (linTable k P).mul r s = some t ↔
    morElt k r.2.2.1 * morElt k s.2.2.1 = morElt k t.2.2.1 := by
  change RaySys.OfBasis.mulB (linBasisR k P) r s = some t ↔ _
  rw [RaySys.OfBasis.mulB_eq_some, linBasisR_apply, linBasisR_apply, linBasisR_apply]

lemma linTable_src (r : NZ P) : (linTable k P).src r = r.2.1 := rfl

lemma linTable_tgt (r : NZ P) : (linTable k P).tgt r = r.1 := rfl

lemma morElt_injective_nz {r t : NZ P} (h : morElt k r.2.2.1 = morElt k t.2.2.1) : r = t := by
  apply (linBasisR k P).injective
  rw [linBasisR_apply, linBasisR_apply, h]

end RayQuiver

end LargeIndecomposable
