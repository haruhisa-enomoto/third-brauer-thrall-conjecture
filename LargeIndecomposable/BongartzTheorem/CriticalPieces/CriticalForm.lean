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
