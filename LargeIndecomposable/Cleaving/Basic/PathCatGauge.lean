module

public import LargeIndecomposable.Cleaving.Basic.PathCatRep

/-!
# Twists are coboundaries along path categories

For a functor `F : PathCat Q ⥤ P` and a twisted multiplicative basis `B` over
`P`, the products of the twist along paths form a gauge (`RayCat.PathCat.gauge`):
path categories have no contours, so every twist becomes trivial along `F`.
With the cleaving lemma, a cleaving functor from a Euclidean path category
makes an algebra with a twisted multiplicative basis representation-infinite
(`RayCat.PathCat.not_isRepresentationFinite_of_cleaving`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

namespace PathCat

variable {Q : Type} [Quiver.{0} Q] {P : Type} [Category.{0} P] [HasZeroMorphisms P]
  [IsRayCategory P] [Fintype P] [DecidableEq P] {k : Type u} [Field k] {A : Type u} [Ring A]
  [Algebra k A] (B : MulBasis k P A) (F : PathCat Q ⥤ P) [F.PreservesZeroMorphisms]

lemma ofPath_comp {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    ofPath p ≫ ofPath q = ofPath (p.comp q) := rfl

/-- The product of the twist along a path. -/
def pathC {a : Q} : ∀ {b : Q}, Quiver.Path a b → kˣ
  | _, .nil => 1
  | _, .cons p e => pathC p * B.tw (F.map (ofPath p)) (F.map (ofPath e.toPath))

lemma pathC_comp {a b : Q} (p : Quiver.Path a b) : ∀ {c : Q} (q : Quiver.Path b c),
    F.map (ofPath (p.comp q)) ≠ 0 →
    pathC B F (p.comp q) = pathC B F p * pathC B F q * B.tw (F.map (ofPath p)) (F.map (ofPath q))
  | _, .nil, _ => by
    simp only [Quiver.Path.comp_nil, pathC, mul_one]
    rw [show (ofPath (Quiver.Path.nil : Quiver.Path b b) : (⟨b⟩ : PathCat Q) ⟶ ⟨b⟩) = 𝟙 _ from rfl,
      F.map_id, B.tw_id_right, mul_one]
  | _, .cons q e, h => by
    have hpq : ofPath (p.comp q) ≫ ofPath e.toPath = ofPath (p.comp (q.cons e)) := by
      rw [ofPath_comp]; simp
    have hq : ofPath q ≫ ofPath e.toPath = ofPath (q.cons e) := by
      rw [ofPath_comp]; simp
    have h' : F.map (ofPath (p.comp q)) ≠ 0 := fun h0 ↦ h (by
      rw [← hpq, F.map_comp, h0, zero_comp])
    rw [Quiver.Path.comp_cons, pathC, pathC_comp p q h', pathC]
    have hc := B.tw_cocycle (F.map (ofPath p)) (F.map (ofPath q)) (F.map (ofPath e.toPath)) (by
      rw [← F.map_comp, ← F.map_comp, ofPath_comp, ofPath_comp, ← Quiver.Path.comp_assoc]
      simpa using h)
    rw [← F.map_comp, ofPath_comp] at hc
    rw [← F.map_comp, hq] at hc
    rw [show p.comp q = p.comp q from rfl] at hc
    calc pathC B F p * pathC B F q * B.tw (F.map (ofPath p)) (F.map (ofPath q)) *
          B.tw (F.map (ofPath (p.comp q))) (F.map (ofPath e.toPath))
        = pathC B F p * pathC B F q * (B.tw (F.map (ofPath p)) (F.map (ofPath q)) *
          B.tw (F.map (ofPath (p.comp q))) (F.map (ofPath e.toPath))) := by group
      _ = pathC B F p * pathC B F q * (B.tw (F.map (ofPath q)) (F.map (ofPath e.toPath)) *
          B.tw (F.map (ofPath p)) (F.map (ofPath (q.cons e)))) := by rw [hc]
      _ = _ := by group

/-- The scalar of a possibly zero path. -/
def gaugeC {X Y : PathCat Q} : (X ⟶ Y) → kˣ
  | none => 1
  | some p => pathC B F p

/-- **The path gauge.** -/
@[instance_reducible]
def gauge : B.Gauge F where
  c f := gaugeC B F f
  c_id _ := rfl
  c_mul {X Y Z} f g h := by
    rcases f with _ | p
    · exact absurd (by rw [show (none : Option _) ≫ g = 0 from rfl, F.map_zero]) h
    rcases g with _ | q
    · have h0 : (some p : X ⟶ Y) ≫ (0 : Y ⟶ Z) = 0 := comp_zero
      exact absurd ((congrArg F.map h0).trans (F.map_zero _ _)) h
    exact (pathC_comp B F p q h).symm

variable [Fintype Q] [DecidableEq Q] [∀ a b : Q, Finite (a ⟶ b)]
  [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]

include B in
/-- **A cleaving functor from a representation-infinite path category makes an
algebra with a twisted multiplicative basis representation-infinite.** -/
theorem not_isRepresentationFinite_of_cleaving
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k)) (hF : IsCleaving F) :
    ¬Statement.IsRepresentationFinite A := fun h ↦
  hD (isRepresentationFinite_of_cleaving_gauge hF (gauge B F) h)

end PathCat

end RayCat

end LargeIndecomposable
