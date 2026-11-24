# Package validation

## Independent challenge workspace

`./check-challenge.sh` validates the frozen source inventory, its contents, and the dependency pins. `./check-comparator.sh` rebuilds the challenge modules in their own Lake workspace. It exports the selected challenge and solution independently and passes the exports to the pinned stock Lake Comparator. The default checks all 24 manuscript statements together. A selector checks one manuscript statement and its required supporting theorem types. [Statement index](../README.md#manuscript-statements)

| Check | Result |
| --- | --- |
| `./check-challenge.sh` | Passed for the complete frozen workspace, aggregate configuration, selectors, and pins |
| `lake build` | Passed for the proof and application modules |
| `lake env lean Check.lean` | Passed for the 24 numbered results and six consumer theorems, using only the three permitted axioms |
| `./check-comparator.sh` | Passed for all 24 numbered results and 368 supporting theorem statements in one Lean kernel replay |
| `./check-comparator.sh Lemma62` | Passed with fresh Lean kernel replay |

The final frozen export also passed stock Comparator’s statement, definition, and axiom checks against the exact solution export accepted by the kernel.

The earlier Leanflow source hashes below record the first release. The comparator update factors out proof fields in `Proof/CalderonN/AngularComponentData.lean` and `Proof/CalderonN/SphereHarmonicBridge.lean` so the frozen definitions can refer to explicitly named certificates. [Current file hashes](../SHA256SUMS)

## Original release (historical)

The first release reproduced all 1,496 proof and consumer sources from Leanflow check `bc163604` byte for byte. The original global solution now lives at `Proof/Manuscript/AnisotropicUniqueness.lean`, and `Solution.lean` re-exports it. `Proof/CalderonN/CheckedLocalExtension.lean` is also byte-identical to the local solution of check `0d2e9641`. The local consumer uses that module path with the rest of its source unchanged. [Checked source hashes](provenance/checked-sources.json)

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

## Standalone manuscript checks (historical)

The Theorem 1.1 comparator was rerun successfully after the proof moved to its shared module. It still checks through `Solution.lean`.

Every numbered theorem, corollary, lemma, and proposition in the selected edition has a separate comparator command. Each was checked against its frozen statement and accepted by Lean’s default kernel under the three permitted axioms. [Statement and configuration index](../README.md#manuscript-statements)
