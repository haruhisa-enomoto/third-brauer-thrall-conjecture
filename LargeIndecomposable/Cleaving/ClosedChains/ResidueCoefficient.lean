module

public import LargeIndecomposable.Cleaving.ClosedChains.SpanCoefficient

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

/-- Residue maps at vertices together with normalized endpoint-radical
coefficients on every path line.  No separate endpoint-whiskering axiom is
present: it follows from the endpoint-radical kernel and the split residue
maps.  Consequently the only remaining functorial input is strict span drop
for empty-middle cross composites. -/
structure ClosedZigzagResidueCoefficientData
    (n : ℕ) (hn : 2 ≤ n)
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k] where
  residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
    End (D.obj X) →ₐ[k] k
  residue_zero : ∀
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (a : End (D.obj X)),
    residue X a = 0 ↔ a ∈ Ring.jacobson (End (D.obj X))
  coefficient : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj X ⟶ D.obj Y) →ₗ[k] k
  normalized : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    coefficient p (D.map (LinearPathCategory.pathHom p)) = 1
  endpoint_kernel : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      LinearMap.ker (coefficient p)
  coefficient_nil : ∀
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (g : End (D.obj X)),
    coefficient
        (Quiver.Path.nil : Quiver.Path
          (LinearPathCategory.vertex X) (LinearPathCategory.vertex X))
        g.asHom = residue X g
  cross_span_lt : ∀
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X')),
    IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) →
      twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom p) ≫ g ≫
            D.map (LinearPathCategory.pathHom q)) <
        twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom r))

namespace ClosedZigzagResidueCoefficientData

variable {n : ℕ} {hn : 2 ≤ n}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]

/-- Choose the vertex residue on an endomorphism Hom and a normalized
endpoint-radical coefficient on every off-diagonal path Hom. -/
def pathCoefficient
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (hmap : ∀
      {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
      End (D.obj X) →ₐ[k] k)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] k := by
  classical
  by_cases hXY : X = Y
  · subst Y
    exact (residue X).toLinearMap
  · exact Classical.choose
      (exists_normalized_endpointRadicalCoefficient
        (D.map (LinearPathCategory.pathHom p)) (hmap p))

omit [D.Additive] [D.Linear k] in
@[simp]
theorem pathCoefficient_self
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (hmap : ∀
      {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
      End (D.obj X) →ₐ[k] k)
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X)) :
    pathCoefficient hmap residue p = (residue X).toLinearMap := by
  simp [pathCoefficient]

omit [D.Additive] [D.Linear k] in
theorem pathCoefficient_spec_of_ne
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (hmap : ∀
      {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
      End (D.obj X) →ₐ[k] k)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) (hXY : X ≠ Y) :
    pathCoefficient hmap residue p
        (D.map (LinearPathCategory.pathHom p)) = 1 ∧
      endpointRadicalSubmodule (k := k)
          (D.map (LinearPathCategory.pathHom p)) ≤
        LinearMap.ker (pathCoefficient hmap residue p) := by
  simpa [pathCoefficient, hXY] using
    (Classical.choose_spec
      (exists_normalized_endpointRadicalCoefficient
        (D.map (LinearPathCategory.pathHom p)) (hmap p)))

/-- Build all residue/endpoint coefficients canonically.  Once every path
basis image is nonzero, the only supplied datum is strict span drop for the
empty-middle cross composites. -/
def ofMapPathNeZero
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (hmap : ∀
      {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
      End (D.obj X) →ₐ[k] k)
    (residue_zero : ∀
      (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
      (a : End (D.obj X)),
      residue X a = 0 ↔ a ∈ Ring.jacobson (End (D.obj X)))
    (cross_span_lt : ∀
      {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj X ⟶ D.obj Y)
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X')),
      IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)) →
        twoSidedEndomorphismSpan k
            (D.map (LinearPathCategory.pathHom p) ≫ g ≫
              D.map (LinearPathCategory.pathHom q)) <
          twoSidedEndomorphismSpan k
            (D.map (LinearPathCategory.pathHom r))) :
    ClosedZigzagResidueCoefficientData (k := k) n hn D where
  residue := residue
  residue_zero := residue_zero
  coefficient := pathCoefficient hmap residue
  normalized := by
    intro X Y p
    classical
    by_cases hXY : X = Y
    · subst Y
      letI : Subsingleton
          (Quiver.Path (LinearPathCategory.vertex X)
            (LinearPathCategory.vertex X)) :=
        opposite_path_subsingleton n hn _ _
      rw [Subsingleton.elim p Quiver.Path.nil]
      rw [LinearPathCategory.pathHom_nil, D.map_id,
        pathCoefficient_self]
      exact (residue X).map_one
    · exact (pathCoefficient_spec_of_ne hmap residue p hXY).1
  endpoint_kernel := by
    intro X Y p
    classical
    by_cases hXY : X = Y
    · subst Y
      letI : Subsingleton
          (Quiver.Path (LinearPathCategory.vertex X)
            (LinearPathCategory.vertex X)) :=
        opposite_path_subsingleton n hn _ _
      rw [Subsingleton.elim p Quiver.Path.nil]
      intro g hg
      rcases hg with ⟨a, ha, b, hb, hab⟩
      simp only [LinearPathCategory.pathHom_nil, D.map_id,
        Category.comp_id, Category.id_comp] at hab
      rw [pathCoefficient_self]
      change residue X (End.of g) = 0
      have hend : End.of g = a + b := by
        apply End.ext
        change g = a.asHom + b.asHom
        exact hab
      rw [hend, map_add, (residue_zero X a).2 ha,
        (residue_zero X b).2 hb, add_zero]
    · exact (pathCoefficient_spec_of_ne hmap residue p hXY).2
  coefficient_nil := by
    intro X g
    change pathCoefficient hmap residue Quiver.Path.nil g.asHom = _
    rw [pathCoefficient_self]
    rfl
  cross_span_lt := cross_span_lt

/-- Endpoint-radical coefficients automatically satisfy every whiskering
equation whose middle path is an identity.  The alternating quiver has no
length-two paths, so at most one outer path can be an arrow; the two cases are
exactly the left and right endpoint coefficient lemmas. -/
theorem identity_middle_whisker
    (h : ClosedZigzagResidueCoefficientData (k := k) n hn D)
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X'))
    (s : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))
    (hs0 : s.length = 0) :
    h.coefficient r
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) = h.coefficient s g := by
  classical
  letI : Subsingleton
      (Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X')) :=
    opposite_path_subsingleton n hn _ _
  have hsEq := s.eq_of_length_zero hs0
  change Y = X at hsEq
  subst Y
  rw [Quiver.Path.eq_nil_of_length_zero s hs0]
  have htotal := closedZigzagOpposite_path_length_le_one n
    (q.comp ((Quiver.Path.nil : Quiver.Path
      (LinearPathCategory.vertex X) (LinearPathCategory.vertex X)).comp p))
  rw [Quiver.Path.length_comp, Quiver.Path.length_comp] at htotal
  by_cases hp0 : p.length = 0
  · have hpEq := p.eq_of_length_zero hp0
    change X = X' at hpEq
    subst X'
    rw [Quiver.Path.eq_nil_of_length_zero p hp0]
    by_cases hq0 : q.length = 0
    · have hqEq := q.eq_of_length_zero hq0
      change Y' = X at hqEq
      subst Y'
      rw [Quiver.Path.eq_nil_of_length_zero q hq0]
      rw [Subsingleton.elim r
        (Quiver.Path.nil : Quiver.Path
          (LinearPathCategory.vertex X) (LinearPathCategory.vertex X))]
      simp
    · letI : Subsingleton
          (Quiver.Path (LinearPathCategory.vertex Y')
            (LinearPathCategory.vertex X)) :=
        opposite_path_subsingleton n hn _ _
      rw [Subsingleton.elim r q]
      simp only [LinearPathCategory.pathHom_nil, D.map_id,
        Category.id_comp]
      rw [h.coefficient_nil X (End.of g)]
      exact endpointRadicalCoefficient_comp_left
        (D.map (LinearPathCategory.pathHom q)) (h.residue X)
        (h.residue_zero X) (h.coefficient q) (h.normalized q)
        (h.endpoint_kernel q) (End.of g)
  · have hpPos : 1 ≤ p.length := Nat.one_le_iff_ne_zero.mpr hp0
    have hq0 : q.length = 0 := by omega
    have hqEq := q.eq_of_length_zero hq0
    change Y' = X at hqEq
    subst Y'
    rw [Quiver.Path.eq_nil_of_length_zero q hq0]
    letI : Subsingleton
        (Quiver.Path (LinearPathCategory.vertex X)
          (LinearPathCategory.vertex X')) :=
      opposite_path_subsingleton n hn _ _
    rw [Subsingleton.elim r p]
    simp only [LinearPathCategory.pathHom_nil, D.map_id,
      Category.comp_id]
    rw [h.coefficient_nil X (End.of g)]
    exact endpointRadicalCoefficient_comp_right
      (D.map (LinearPathCategory.pathHom p)) (h.residue X)
      (h.residue_zero X) (h.coefficient p) (h.normalized p)
      (h.endpoint_kernel p) (End.of g)

/-- Residue/endpoint coefficient data and strict cross-span drop provide the
strict-span boundary used by the generic pathwise retraction. -/
def toSpanCoefficientData
    (h : ClosedZigzagResidueCoefficientData (k := k) n hn D) :
    ClosedZigzagSpanCoefficientData (k := k) n hn D where
  coefficient := h.coefficient
  normalized := h.normalized
  endpoint_kernel := h.endpoint_kernel
  identity_middle_whisker := h.identity_middle_whisker
  cross_span_lt := h.cross_span_lt

/-- Once strict cross-span drop is supplied, the residue coefficients give
the full BGRS 3.2 Hom-bifunctor retraction. -/
def homBifunctorRetraction
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (h : ClosedZigzagResidueCoefficientData (k := k) n hn D) :
    HomBifunctorRetraction (k := k) D :=
  h.toSpanCoefficientData.homBifunctorRetraction

end ClosedZigzagResidueCoefficientData
end LargeIndecomposable.ClosedZigzagTransfer
