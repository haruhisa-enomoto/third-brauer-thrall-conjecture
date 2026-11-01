# Long lines without the classification of sincere algebras

This note outlines the proof of `LargeIndecomposable.longLineNode`. Bongartz obtains long lines from his theorem on large simply connected sincere algebras, whose proof in the literature goes through the classification of those algebras. Theorem A needs only the weaker statement below. The Lean proof is the proof of record. An independent agent audit checked selected steps; no human has reviewed the mathematics.

## Statement

Let `B` be minimal representation-infinite and distributive, with ray category `P`, torsion-free fundamental group and representation-finite convex cover pieces. If graded indecomposables have unbounded support, the universal cover has lines of every length.

## Proof

Throughout, `U` is a sincere directing module and `q` the Euler form on its support algebra. All indecomposables are directing.

**Forms (`DirectedAlgebras/Sincere/SincereRoots.lean`, `UnitForms/Roots.lean`).** `q` is weakly positive. Dimension vectors of indecomposables are roots. Points with no directed path between them have `B = 0`.

**Directed paths are short (`DirectedAlgebras/Sincere/SincereTree.lean`).** By Vossieck's lemma each step of a directed path acts injectively or surjectively, and a strict drop cannot precede a strict rise. A composite of `N` steps vanishes when `N` bounds nonzero paths of `P`. So runs have length below `2N`.

**No contours (`BongartzTheorem/ContourExclusion/ContourFree.lean`, `DirectedAlgebras/Sincere/FarSummand.lean`, `DirectedAlgebras/Sincere/PolyBuild.lean`).** See [contours](contours.md). In summary:

1. A contour gives a branching morphism `w`: two first arrows, and proper left factors with one (`exists_isBranch`).
2. The interval of a lift of `w` is a polygon with arms, and all the required values of `B` come from thin indecomposable quotients of projectives. Parallel paths in a piece have equal composite (`ParEq`), so chords do no harm.
3. Two orthogonal polygons are never below a common root (`false_of_anchors`).
4. A large indecomposable sees a lift of `w`, because modules killed by `w` are bounded by minimality and push-downs of indecomposables are indecomposable (`isIndecMod_pdMod`).
5. Take a lift `H₀` acting on `U`. On the convex set `E` of points with no path to or from `H₀`, a summand of the truncation through a far point reaches the boundary, so it is large (`exists_far_summand`). So it carries a second lift, orthogonal to the first.

**Forests (`BongartzTheorem/LongLines/ForestPiece.lean`).** Without contours, parallel nonzero paths of the cover are equal, so every arrow weight is a cocycle. Local simple connectivity makes every arrow a bridge.

**Support (`DirectedAlgebras/Sincere/SincereGraph.lean`, `BongartzTheorem/LongLines/LineBuild.lean`).** The support of an indecomposable on a forest is convex, so one can pass to a sincere module on a subtree.

**The line (`DirectedAlgebras/Sincere/SincereGraph.lean`).** A large tree of bounded degree has a long path, and the path has a turn `t` in the middle. The two sides of `t` are convex and orthogonal. A summand of the truncation to a side through the far end reaches `t`. Lemma R (`end_or_line`) makes it a clean line from `t` or gives a good end at `t`. Two good ends contradict weak positivity (`false_of_glue`). So one side is a clean line, as long as that side. It is a line of the cover (`cline_of_seq`).

## Scope

The result is weaker than Bongartz's theorem: it gives lines of every length, with no linear bound `n/6`.
