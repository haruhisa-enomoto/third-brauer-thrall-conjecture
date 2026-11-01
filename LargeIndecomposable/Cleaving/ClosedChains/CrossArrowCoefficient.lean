module

public import LargeIndecomposable.Cleaving.ClosedChains.ThinPathRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.ClosedZigzag

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C]
  [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

/-- Every path in the opposite alternating zigzag has length at most one. -/
theorem closedZigzagOpposite_path_length_le_one
    (n : ℕ) {a b : (Vertex n)ᵒᵖ} (p : Quiver.Path a b) :
    p.length ≤ 1 := by
  cases p with
  | nil => simp
  | cons p e =>
      have hp0 := opposite_path_length_zero_before_arrow n p e
      simp [hp0]

/-- Coefficients on the identity and arrow Hom spaces of a closed zigzag,
with the naturality equations separated into two parts.  The
`identity_middle_whisker` field is exactly the endpoint-endomorphism part
handled by split residue maps and endpoint-radical coefficients.  The last
field is the genuinely cross-arrow condition: whiskering an ambient Hom for
which the source category has no middle path must have zero coefficient in a
landing arrow line. -/
structure ClosedZigzagCrossCoefficientData
    (n : ℕ) (hn : 2 ≤ n)
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k] where
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
  identity_middle_whisker : ∀
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X'))
    (s : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    s.length = 0 →
      coefficient r
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) = coefficient s g
  cross_whisker_vanish : ∀
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
      coefficient r
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) = 0

namespace ClosedZigzagCrossCoefficientData

variable {n : ℕ} {hn : 2 ≤ n}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]

/-- In a radical-square-zero alternating zigzag, the endpoint equations and
cross-arrow vanishing are sufficient for all two-variable coefficient
equations.  If the middle path is an arrow, both outer paths must be
identities and the equation is formal; if it is an identity, use the endpoint
field; if it does not exist, use the cross field. -/
def toThinPathCoefficientData
    (h : ClosedZigzagCrossCoefficientData (k := k) n hn D) :
    ThinPathCoefficientData (k := k) D where
  path_subsingleton := opposite_path_subsingleton n hn
  coefficient := h.coefficient
  normalized := h.normalized
  whisker_coefficient := by
    intro X' X Y Y' p g q r
    letI : Subsingleton
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X)) :=
      opposite_path_subsingleton n hn _ _
    letI : Subsingleton
        (Quiver.Path (LinearPathCategory.vertex Y')
          (LinearPathCategory.vertex X')) :=
      opposite_path_subsingleton n hn _ _
    by_cases hm : Nonempty
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X))
    · rw [coefficientOrZero_of_nonempty _ _ hm]
      let s := Classical.choice hm
      change h.coefficient r
          (D.map (LinearPathCategory.pathHom p) ≫ g ≫
            D.map (LinearPathCategory.pathHom q)) =
        h.coefficient s g
      by_cases hs0 : s.length = 0
      · exact h.identity_middle_whisker p g q r s hs0
      · have hspos : 1 ≤ s.length := Nat.one_le_iff_ne_zero.mpr hs0
        have htotal := closedZigzagOpposite_path_length_le_one n
          (q.comp (s.comp p))
        rw [Quiver.Path.length_comp, Quiver.Path.length_comp] at htotal
        have hp0 : p.length = 0 := by omega
        have hq0 : q.length = 0 := by omega
        have hpEq := p.eq_of_length_zero hp0
        have hqEq := q.eq_of_length_zero hq0
        change X = X' at hpEq
        change Y' = Y at hqEq
        subst X'
        subst Y'
        rw [Quiver.Path.eq_nil_of_length_zero p hp0,
          Quiver.Path.eq_nil_of_length_zero q hq0]
        simp only [LinearPathCategory.pathHom_nil, D.map_id,
          Category.id_comp, Category.comp_id]
        rw [Subsingleton.elim r s]
    · have hm' : IsEmpty
          (Quiver.Path (LinearPathCategory.vertex Y)
            (LinearPathCategory.vertex X)) :=
        not_nonempty_iff.mp hm
      rw [coefficientOrZero_of_isEmpty _ _ hm']
      exact h.cross_whisker_vanish p g q r hm'

/-- The separated source-specific boundary directly yields the BGRS 3.2
Hom-bifunctor retraction. -/
def homBifunctorRetraction
    (h : ClosedZigzagCrossCoefficientData (k := k) n hn D) :
    HomBifunctorRetraction (k := k) D :=
  h.toThinPathCoefficientData.homBifunctorRetraction

end ClosedZigzagCrossCoefficientData
end LargeIndecomposable.ClosedZigzagTransfer
