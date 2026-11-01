module

public import LargeIndecomposable.Cleaving.ClosedChains.ResidueCoefficient

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

/-- The span of all ambient cross composites landing in one source Hom
space.  The middle source Hom is required to be empty; these are exactly the
terms that a two-variable cleavage coefficient must annihilate. -/
def forbiddenCrossSubmodule
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    (X' Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ) :
    Submodule k (D.obj X' ⟶ D.obj Y') :=
  Submodule.span k {h | ∃
    (X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)),
    IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) ∧
    h = D.map (LinearPathCategory.pathHom p) ≫ g ≫
      D.map (LinearPathCategory.pathHom q)}

theorem crossComposite_mem_forbiddenCrossSubmodule
    {n : ℕ}
    {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
    [D.Additive] [D.Linear k]
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (hm : IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))) :
    D.map (LinearPathCategory.pathHom p) ≫ g ≫
        D.map (LinearPathCategory.pathHom q) ∈
      forbiddenCrossSubmodule (k := k) D X' Y' := by
  apply Submodule.subset_span
  exact ⟨X, Y, p, g, q, hm, rfl⟩

/-- The exact linear obstruction occurring in the BGRS supplement
construction: endpoint-Jacobson actions on the landing path generator,
together with every forbidden cross composite landing in the same Hom. -/
def pathSupplementObstruction
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    Submodule k (D.obj X ⟶ D.obj Y) :=
  endpointRadicalSubmodule (k := k)
      (D.map (LinearPathCategory.pathHom p)) ⊔
    forbiddenCrossSubmodule (k := k) D X Y

/-- A vector outside a subspace admits a normalized linear coefficient whose
kernel contains that subspace. -/
theorem exists_normalized_coefficient_killing
    {V : Type*} [AddCommGroup V] [Module k V]
    (S : Submodule k V) (f : V) (hf : f ∉ S) :
    ∃ ell : V →ₗ[k] k, ell f = 1 ∧ S ≤ LinearMap.ker ell := by
  obtain ⟨φ, hφf, hφ⟩ := S.exists_le_ker_of_notMem hf
  let ell : V →ₗ[k] k := (φ f)⁻¹ • φ
  refine ⟨ell, ?_, ?_⟩
  · dsimp [ell]
    simp [hφf]
  · intro g hg
    change (φ f)⁻¹ * φ g = 0
    rw [show φ g = 0 from hφ hg]
    simp

/-- Source-faithful BGRS supplement data.  Unlike the stronger principal-span
boundary, this asks only that the landing path generator not lie in the sum
of its endpoint radical layer and the cross-composite space.  This is exactly
the nonmembership established by the power calculation in BGRS 3.7. -/
structure ClosedZigzagSupplementData
    (n : ℕ) (hn : 2 ≤ n)
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k] where
  residue : ∀ X : LinearPathCategory.Category k (Vertex n)ᵒᵖ,
    End (D.obj X) →ₐ[k] k
  residue_zero : ∀
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (a : End (D.obj X)),
    residue X a = 0 ↔ a ∈ Ring.jacobson (End (D.obj X))
  separated : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    D.map (LinearPathCategory.pathHom p) ∉
      pathSupplementObstruction (k := k) D p

namespace ClosedZigzagSupplementData

variable {n : ℕ} {hn : 2 ≤ n}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]

/-- Choose the BGRS supplement coefficient on each path line. -/
def coefficient (h : ClosedZigzagSupplementData (k := k) n hn D)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] k :=
  Classical.choose (exists_normalized_coefficient_killing
    (pathSupplementObstruction (k := k) D p)
    (D.map (LinearPathCategory.pathHom p)) (h.separated p))

@[simp]
theorem coefficient_normalized
    (h : ClosedZigzagSupplementData (k := k) n hn D)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    h.coefficient p (D.map (LinearPathCategory.pathHom p)) = 1 :=
  (Classical.choose_spec (exists_normalized_coefficient_killing
    (pathSupplementObstruction (k := k) D p)
    (D.map (LinearPathCategory.pathHom p)) (h.separated p))).1

theorem obstruction_le_coefficient_ker
    (h : ClosedZigzagSupplementData (k := k) n hn D)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    pathSupplementObstruction (k := k) D p ≤
      LinearMap.ker (h.coefficient p) :=
  (Classical.choose_spec (exists_normalized_coefficient_killing
    (pathSupplementObstruction (k := k) D p)
    (D.map (LinearPathCategory.pathHom p)) (h.separated p))).2

theorem endpointRadical_le_coefficient_ker
    (h : ClosedZigzagSupplementData (k := k) n hn D)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      LinearMap.ker (h.coefficient p) :=
  le_trans le_sup_left (h.obstruction_le_coefficient_ker p)

theorem forbiddenCross_le_coefficient_ker
    (h : ClosedZigzagSupplementData (k := k) n hn D)
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    forbiddenCrossSubmodule (k := k) D X Y ≤
      LinearMap.ker (h.coefficient p) :=
  le_trans le_sup_right (h.obstruction_le_coefficient_ker p)

/-- On identity paths the chosen supplement coefficient is forced to be the
split residue: it is normalized at the identity and kills its Jacobson
layer. -/
theorem coefficient_nil
    (h : ClosedZigzagSupplementData (k := k) n hn D)
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (g : End (D.obj X)) :
    h.coefficient
        (Quiver.Path.nil : Quiver.Path
          (LinearPathCategory.vertex X) (LinearPathCategory.vertex X))
        g.asHom = h.residue X g := by
  simpa using endpointRadicalCoefficient_comp_left
    (D.map (LinearPathCategory.pathHom
      (Quiver.Path.nil : Quiver.Path
        (LinearPathCategory.vertex X) (LinearPathCategory.vertex X))))
    (h.residue X) (h.residue_zero X)
    (h.coefficient Quiver.Path.nil)
    (h.coefficient_normalized Quiver.Path.nil)
    (h.endpointRadical_le_coefficient_ker Quiver.Path.nil) g

/-- Endpoint-radical coefficients automatically satisfy every naturality
equation whose middle source path is an identity. -/
theorem identity_middle_whisker
    (h : ClosedZigzagSupplementData (k := k) n hn D)
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
        (h.residue_zero X) (h.coefficient q) (h.coefficient_normalized q)
        (h.endpointRadical_le_coefficient_ker q) (End.of g)
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
      (h.residue_zero X) (h.coefficient p) (h.coefficient_normalized p)
      (h.endpointRadical_le_coefficient_ker p) (End.of g)

/-- Exact BGRS supplements supply the separated cross-arrow coefficient
data, without any principal-span strengthening. -/
def toCrossCoefficientData
    (h : ClosedZigzagSupplementData (k := k) n hn D) :
    ClosedZigzagCrossCoefficientData (k := k) n hn D where
  coefficient := h.coefficient
  normalized := h.coefficient_normalized
  identity_middle_whisker := h.identity_middle_whisker
  cross_whisker_vanish := by
    intro X' X Y Y' p g q r hm
    apply h.forbiddenCross_le_coefficient_ker r
    exact crossComposite_mem_forbiddenCrossSubmodule p g q hm

/-- The exact source supplement nonmembership yields the full BGRS 3.2
two-variable Hom-bifunctor retraction. -/
def homBifunctorRetraction
    (h : ClosedZigzagSupplementData (k := k) n hn D) :
    HomBifunctorRetraction (k := k) D :=
  h.toCrossCoefficientData.homBifunctorRetraction

end ClosedZigzagSupplementData
end LargeIndecomposable.ClosedZigzagTransfer
