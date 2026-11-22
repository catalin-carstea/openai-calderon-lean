# Package validation

The 1,496 proof and consumer sources from Leanflow check `bc163604` are byte-identical in this package. `Proof/CalderonN/CheckedLocalExtension.lean` is also byte-identical to the local solution of check `0d2e9641`. The local consumer uses that module path with the rest of its source unchanged. [Checked source hashes](provenance/checked-sources.json)

The validation used a fresh package checkout and the pinned Mathlib dependency cache. Lake rebuilt all 1,494 supporting modules, the global solution, and both consumer modules. The proof build completed with linter and deprecation warnings from the existing sources. It reported zero declarations using `sorry`. Each challenge was compiled separately with its one intentional open theorem.

| Check | Result |
| --- | --- |
| `./check-challenge.sh` | Passed for the three challenge files, frozen imports, and dependency pins |
| `lake build` | Passed from fresh local build outputs |
| `lake query` import graph | Passed for all three challenges and all solution entry points. The challenge definitions and solution definitions have independent import paths |
| `lake env lean Check.lean` | Passed for the three results and four consumer theorems. Each uses only `propext`, `Quot.sound`, and `Classical.choice` |
| `lake comparator --config ComparatorChallenges/Theorem11.json` | Passed with fresh Lean kernel replay in about 10 minutes |
| `lake comparator --config ComparatorChallenges/Theorem31.json` | Passed with fresh Lean kernel replay in about 9 minutes |
| `lake comparator --config ComparatorChallenges/Proposition53.json` | Passed with fresh Lean kernel replay in about 8 minutes |

The stock Lake comparator built and exported both sides inside bubblewrap for all three runs. Each reported `Lean default kernel accepts the solution` and `Your solution is okay!`. Each configuration checks the theorem type and its reachable definitions with an empty `definition_names` list.

The archive contains the sources, independent challenges, frozen references, and dependency pins. [File checksums](../SHA256SUMS)
