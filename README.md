# OpenAI Calderón formalization in Lean

**Project authors: Cătălin I. Cârstea and Lauri Oksanen.**

This package formalizes every numbered result in the September 24, 2026 edition of OpenAI’s *Smooth anisotropic uniqueness in the Calderón problem from one boundary patch*. The 24 results include two theorems, two corollaries, 12 lemmas, and eight propositions. [Selected manuscript](docs/statement/README.md)

The index links each Lean proof to its frozen statement, review guide, and individual comparator selector. The development covers boundary determination, continuation, the global uniqueness theorem, and its full-boundary and scalar consequences. [Proof guide](docs/PROOF_GUIDE.md)

## Manuscript statements

| Manuscript statement | Lean declaration | Frozen statement | Comparator selector |
| --- | --- | --- | --- |
| Theorem 1.1, Smooth anisotropic uniqueness from one patch | [`CalderonPatch.smoothAnisotropicUniqueness`](Proof/Manuscript/AnisotropicUniqueness.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Theorem11.lean#L13) · [Guide](docs/statement/REVIEW.md#theorem-11) | `Theorem11` |
| Corollary 1.2, Full-boundary uniqueness | [`CalderonPaper.corollary12`](Proof/Manuscript/Corollary12.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Corollary12.lean#L13) · [Guide](docs/statement/REVIEW.md#corollary-12) | `Corollary12` |
| Corollary 1.3, Smooth scalar uniqueness from one patch | [`CalderonPaper.corollary13`](Proof/Manuscript/Corollary13.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Corollary13.lean#L13) · [Guide](docs/statement/REVIEW.md#corollary-13) | `Corollary13` |
| Lemma 2.1, Boundary jets | [`CalderonPaper.lemma21`](Proof/Manuscript/Lemma21.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma21.lean#L20) · [Guide](docs/statement/REVIEW.md#lemma-21) | `Lemma21` |
| Proposition 2.2, Common cap and Green data | [`CalderonPaper.proposition22`](Proof/Manuscript/Proposition22.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition22.lean#L22) · [Guide](docs/statement/REVIEW.md#proposition-22) | `Proposition22` |
| Lemma 2.3, Separation and finite harmonic jets | [`CalderonPaper.lemma23`](Proof/Manuscript/Lemma23.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma23.lean#L23) · [Guide](docs/statement/REVIEW.md#lemma-23) | `Lemma23` |
| Theorem 3.1, Local metric extension | [`CalderonN.localMetricExtension`](Proof/CalderonN/CheckedLocalExtension.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Theorem31.lean#L13) · [Guide](docs/statement/REVIEW.md#theorem-31) | `Theorem31` |
| Lemma 3.2, Extension from a cross | [`CalderonPaper.lemma32`](Proof/Manuscript/Lemma32.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma32.lean#L14) · [Guide](docs/statement/REVIEW.md#lemma-32) | `Lemma32` |
| Proposition 3.3, Product extension criterion | [`CalderonPaper.proposition33`](Proof/Manuscript/Proposition33.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition33.lean#L16) · [Guide](docs/statement/REVIEW.md#proposition-33) | `Proposition33` |
| Lemma 3.4, Propagation through a compact cylinder | [`CalderonPaper.lemma34`](Proof/Manuscript/Lemma34.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma34.lean#L15) · [Guide](docs/statement/REVIEW.md#lemma-34) | `Lemma34` |
| Proposition 3.5, Fixed-separation initialization | [`CalderonPaper.proposition35`](Proof/Manuscript/Proposition35.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition35.lean#L17) · [Guide](docs/statement/REVIEW.md#proposition-35) | `Proposition35` |
| Lemma 4.1, Profile bounds | [`CalderonPaper.lemma41`](Proof/Manuscript/Lemma41.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma41.lean#L18) · [Guide](docs/statement/REVIEW.md#lemma-41) | `Lemma41` |
| Proposition 4.2, Continuation to the sphere family | [`CalderonPaper.proposition42`](Proof/Manuscript/Proposition42.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition42.lean#L19) · [Guide](docs/statement/REVIEW.md#proposition-42) | `Proposition42` |
| Proposition 4.3, The transfer density | [`CalderonPaper.proposition43`](Proof/Manuscript/Proposition43.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition43.lean#L19) · [Guide](docs/statement/REVIEW.md#proposition-43) | `Proposition43` |
| Lemma 5.1, Moving trace operators | [`CalderonPaper.lemma51`](Proof/Manuscript/Lemma51.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma51.lean#L16) · [Guide](docs/statement/REVIEW.md#lemma-51) | `Lemma51` |
| Lemma 5.2, Weighted raising estimate | [`CalderonPaper.lemma52`](Proof/Manuscript/Lemma52.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma52.lean#L15) · [Guide](docs/statement/REVIEW.md#lemma-52) | `Lemma52` |
| Proposition 5.3, Coercivity for the moving trace equation | [`CalderonN.coercivity`](Proof/CalderonN/CheckedLocalExtension.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition53.lean#L11) · [Guide](docs/statement/REVIEW.md#proposition-53) | `Proposition53` |
| Lemma 5.4, Uniform transfer density | [`CalderonPaper.lemma54`](Proof/Manuscript/Lemma54.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma54.lean#L22) · [Guide](docs/statement/REVIEW.md#lemma-54) | `Lemma54` |
| Lemma 6.1, Two-power moment bound | [`CalderonPaper.lemma61`](Proof/Manuscript/Lemma61.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma61.lean#L20) · [Guide](docs/statement/REVIEW.md#lemma-61) | `Lemma61` |
| Lemma 6.2, Finite-order interpolation | [`CalderonPaper.lemma62`](Proof/Manuscript/Lemma62.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma62.lean#L17) · [Guide](docs/statement/REVIEW.md#lemma-62) | `Lemma62` |
| Lemma 6.3, Superlinear improvement | [`CalderonPaper.lemma63`](Proof/Manuscript/Lemma63.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma63.lean#L19) · [Guide](docs/statement/REVIEW.md#lemma-63) | `Lemma63` |
| Proposition 7.1, No interior frontier | [`CalderonPaper.proposition71`](Proof/Manuscript/Proposition71.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition71.lean#L23) · [Guide](docs/statement/REVIEW.md#proposition-71) | `Proposition71` |
| Proposition 7.2, Smooth completion and the accessible gauge | [`CalderonPaper.proposition72`](Proof/Manuscript/Proposition72.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Proposition72.lean#L16) · [Guide](docs/statement/REVIEW.md#proposition-72) | `Proposition72` |
| Lemma 8.1, Conformal rigidity at a boundary patch | [`CalderonPaper.lemma81`](Proof/Manuscript/Lemma81.lean) | [Lean](ComparatorChallenges/Source/ComparatorChallenges/Lemma81.lean#L12) · [Guide](docs/statement/REVIEW.md#lemma-81) | `Lemma81` |

## Build

Install [elan](https://github.com/leanprover/elan) and Git. The package pins Lean `4.35.0-rc3`, Mathlib `f6090c7095e1e56b3464c1daba5f24631f1290d2`, and its transitive dependencies. The used Tau Ceti sources are bundled. Run from the repository root.

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

Allow at least a few hours for a first serial build and a full run of the comparator checks. Build time depends on available cores, memory, and the Mathlib cache. Use a 64-bit machine with at least 16 GiB RAM and 30 GiB free disk space. The comparator uses Linux with [bubblewrap](https://github.com/containers/bubblewrap) on `PATH` and user namespaces enabled.

## Run the comparator challenges

Prepare the Mathlib cache for the separate challenge workspace. Run the aggregate comparator from the repository root, or pass a selector from the index to check one result.

```sh
(cd ComparatorChallenges && lake exe cache get)
./check-comparator.sh
./check-comparator.sh Corollary13
```

[The frozen statement tree](ComparatorChallenges/Source) and its [checksums](docs/statement/SHA256SUMS) define the reading surface. The challenge workspace builds from that tree and pinned dependencies. The solution is built and exported separately. Lean's stock Comparator checks the selected theorem statements and their reachable definitions, then replays the solution in a fresh Lean kernel with `propext`, `Quot.sound`, and `Classical.choice` permitted. [Statement and validation details](docs/statement/README.md)

## License and citation

Original project contributions use the [BSD 3-Clause License](LICENSE). The bundled Tau Ceti and adapted conformal Poisson material retain their upstream licenses and notices. [Third-party notices](THIRD_PARTY_NOTICES.md) · [Acknowledgements](docs/ACKNOWLEDGEMENTS.md) · [Citation metadata](CITATION.cff)
