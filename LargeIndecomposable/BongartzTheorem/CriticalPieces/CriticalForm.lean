module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalConnected
public import LargeIndecomposable.DirectedAlgebras.Preprojective.NotWeaklyPositive
public import LargeIndecomposable.UnitForms.Restrict

/-!
# The Euler form of a critical piece is not weakly positive

A critical piece (a representation-infinite convex piece whose smaller convex pieces are
representation-finite) is connected (`connected_of_critical`), so it has indecomposables of every
size (`unbounded_of_not_pieceRepFin`) and so does its preprojective component
(`PreprojComp.unbounded`). Hence its Euler form is not weakly positive
(`not_weaklyPositive_critical`; the representation-theoretic half of Bongartz's criterion).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **The Euler form of a critical piece is not weakly positive.** -/
theorem not_weaklyPositive_critical [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀)))
    (hne : S.Nonempty) (hacycCov : CoverAcyclic x₀)
    (hint : ∀ a b : Cover x₀, (interval a b).Finite) (hlsc : CoverLocalSC x₀)
    (hrep : ¬PieceRepFin k S)
    (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < S.card →
      PieceRepFin k C') :
    ¬(AR.eulerForm (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov))
      (fun _ ↦ Set.mem_univ _)).WeaklyPositive := by
  have hconnS := connected_of_critical (k := k) hS hrep hmin
  obtain ⟨𝒞, h𝒞⟩ := piece_preprojComp (k := k) hS hne hacycCov hint hlsc
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  let D := pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)
  have hunb := unbounded_of_not_pieceRepFin hS hne hacycCov hint hlsc hconnS hrep
  have hunb𝒞 := AR.PreprojComp.unbounded D.e D.idem D.sum
    (fun x ↦ D.projIndNT x (Set.mem_univ x))
    (fun T hT hcl ↦ hconnS T hT fun α ↦
      ⟨fun h ↦ hcl _ _ h (Or.inr (D.arrNe _ _ (parr_arrow hpar α))),
        fun h ↦ hcl _ _ h (Or.inl (D.arrNe _ _ (parr_arrow hpar α)))⟩) h𝒞 hunb
  exact AR.not_weaklyPositive_of_unbounded D (fun _ ↦ Set.mem_univ _) h𝒞 hunb𝒞

/-- **(R2) The Euler form of a critical piece has a critical restriction.** -/
theorem exists_critical_restrict_critical [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀)))
    (hne : S.Nonempty) (hacycCov : CoverAcyclic x₀)
    (hint : ∀ a b : Cover x₀, (interval a b).Finite) (hlsc : CoverLocalSC x₀)
    (hrep : ¬PieceRepFin k S)
    (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < S.card →
      PieceRepFin k C') :
    ∃ s, ((AR.eulerForm (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov))
      (fun _ ↦ Set.mem_univ _)).restrict s).Critical :=
  Forms.UnitForm.exists_critical_restrict _
    (not_weaklyPositive_critical hS hne hacycCov hint hlsc hrep hmin)

end LargeIndecomposable.RayCat
