# Reused Lean source

Mathlib is the only external Lake dependency. Much of the library reuses code
from earlier formalizations, reorganized here by mathematical topic, with code the main theorems do not use removed.
[`verification/module-origins.json`](verification/module-origins.json) records the
origin of every module that was reused.

| Origin | Modules | Licence |
| --- | --- | --- |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti), development state of October 28, 2026 (local commit `580b6f9d5`, not a published revision) | 45 | Apache 2.0, The Tau Ceti contributors |
| [`multiplicative-bases-deformations`](https://github.com/haruhisa-enomoto/multiplicative-bases-deformations) | 300 | Apache 2.0 |
| [`magnitude-conjecture`](https://github.com/haruhisa-enomoto/magnitude-conjecture) | 38 | Apache 2.0 |
| [`quotient-submodule-equidistribution`](https://github.com/haruhisa-enomoto/quotient-submodule-equidistribution) | 44 | Apache 2.0 |
| [`brick-accessibility-special-biserial`](https://github.com/haruhisa-enomoto/brick-accessibility-special-biserial) | finite quivers and path algebras in `Quivers/PathAlgebras/FiniteQuiver.lean` | Apache 2.0 |
| The author's unpublished formalization around the Cartan determinant conjecture | 106 | Apache 2.0 |

Files from Tau Ceti keep their copyright headers and a notice naming their source
module. They were changed for the Lean module system and the pinned Mathlib, moved
to new paths, and their declarations were placed in the `LargeIndecomposable`
namespace.

`Foundations/Ring/NilGen.lean` is also adapted from Tau Ceti.
