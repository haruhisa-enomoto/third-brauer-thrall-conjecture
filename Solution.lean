module

public import LargeIndecomposable

@[expose] public section

universe u

/-- **Theorem A.** A representation-infinite finite-dimensional algebra over an
algebraically closed field admits a representation embedding of the category `D`
of Kronecker modules without the simple injective as a summand, closed under
colimits, which preserves dimensions. -/
theorem LargeIndecomposable.Challenge.theoremA : LargeIndecomposable.Statement.TheoremA.{u} :=
  LargeIndecomposable.theoremA

/-- **Corollary 1.1.** A representation-infinite finite-dimensional algebra over an
algebraically closed field has an indecomposable module of every infinite dimension. -/
theorem LargeIndecomposable.Challenge.corollaryDimension :
    LargeIndecomposable.Statement.CorollaryDimension.{u} :=
  LargeIndecomposable.corollaryDimension

/-- **Corollary 5.3.** Indecomposable modules of every infinite dimension whose
endomorphism rings are local with residue field `k` and radical of bounded
nilpotence index. -/
theorem LargeIndecomposable.Challenge.corollaryRadical :
    LargeIndecomposable.Statement.CorollaryRadical.{u} :=
  LargeIndecomposable.corollaryRadical
