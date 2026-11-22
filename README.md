# OpenAI Calderón formalization in Lean

**Project authors: Cătălin I. Cârstea and Lauri Oksanen.**

This package formalizes every numbered result in the September 24, 2026 edition of OpenAI’s *Smooth anisotropic uniqueness in the Calderón problem from one boundary patch*. The 24 results include two theorems, two corollaries, 12 lemmas, and eight propositions. [Selected manuscript](docs/statement/README.md)

The index links each Lean proof to its frozen statement and individual comparator. The development covers boundary determination, continuation, the global uniqueness theorem, and its full-boundary and scalar consequences. [Proof guide](docs/PROOF_GUIDE.md)

## Manuscript statements

| Manuscript statement | Lean declaration | Frozen statement | Comparator configuration |
| --- | --- | --- | --- |
| Theorem 1.1, Smooth anisotropic uniqueness from one patch | [`CalderonPatch.smoothAnisotropicUniqueness`](Proof/Manuscript/AnisotropicUniqueness.lean) | [Statement](ComparatorChallenges/Theorem11.lean) | [`Theorem11.json`](ComparatorChallenges/Theorem11.json) |
| Corollary 1.2, Full-boundary uniqueness | [`CalderonPaper.corollary12`](Proof/Manuscript/Corollary12.lean) | [Statement](ComparatorChallenges/Corollary12.lean) | [`Corollary12.json`](ComparatorChallenges/Corollary12.json) |
| Corollary 1.3, Smooth scalar uniqueness from one patch | [`CalderonPaper.corollary13`](Proof/Manuscript/Corollary13.lean) | [Statement](ComparatorChallenges/Corollary13.lean) | [`Corollary13.json`](ComparatorChallenges/Corollary13.json) |
| Lemma 2.1, Boundary jets | [`CalderonPaper.lemma21`](Proof/Manuscript/Lemma21.lean) | [Statement](ComparatorChallenges/Lemma21.lean) | [`Lemma21.json`](ComparatorChallenges/Lemma21.json) |
| Proposition 2.2, Common cap and Green data | [`CalderonPaper.proposition22`](Proof/Manuscript/Proposition22.lean) | [Statement](ComparatorChallenges/Proposition22.lean) | [`Proposition22.json`](ComparatorChallenges/Proposition22.json) |
| Lemma 2.3, Separation and finite harmonic jets | [`CalderonPaper.lemma23`](Proof/Manuscript/Lemma23.lean) | [Statement](ComparatorChallenges/Lemma23.lean) | [`Lemma23.json`](ComparatorChallenges/Lemma23.json) |
| Theorem 3.1, Local metric extension | [`CalderonN.localMetricExtension`](Proof/CalderonN/CheckedLocalExtension.lean) | [Statement](ComparatorChallenges/Theorem31.lean) | [`Theorem31.json`](ComparatorChallenges/Theorem31.json) |
| Lemma 3.2, Extension from a cross | [`CalderonPaper.lemma32`](Proof/Manuscript/Lemma32.lean) | [Statement](ComparatorChallenges/Lemma32.lean) | [`Lemma32.json`](ComparatorChallenges/Lemma32.json) |
| Proposition 3.3, Product extension criterion | [`CalderonPaper.proposition33`](Proof/Manuscript/Proposition33.lean) | [Statement](ComparatorChallenges/Proposition33.lean) | [`Proposition33.json`](ComparatorChallenges/Proposition33.json) |
| Lemma 3.4, Propagation through a compact cylinder | [`CalderonPaper.lemma34`](Proof/Manuscript/Lemma34.lean) | [Statement](ComparatorChallenges/Lemma34.lean) | [`Lemma34.json`](ComparatorChallenges/Lemma34.json) |
| Proposition 3.5, Fixed-separation initialization | [`CalderonPaper.proposition35`](Proof/Manuscript/Proposition35.lean) | [Statement](ComparatorChallenges/Proposition35.lean) | [`Proposition35.json`](ComparatorChallenges/Proposition35.json) |
| Lemma 4.1, Profile bounds | [`CalderonPaper.lemma41`](Proof/Manuscript/Lemma41.lean) | [Statement](ComparatorChallenges/Lemma41.lean) | [`Lemma41.json`](ComparatorChallenges/Lemma41.json) |
| Proposition 4.2, Continuation to the sphere family | [`CalderonPaper.proposition42`](Proof/Manuscript/Proposition42.lean) | [Statement](ComparatorChallenges/Proposition42.lean) | [`Proposition42.json`](ComparatorChallenges/Proposition42.json) |
| Proposition 4.3, The transfer density | [`CalderonPaper.proposition43`](Proof/Manuscript/Proposition43.lean) | [Statement](ComparatorChallenges/Proposition43.lean) | [`Proposition43.json`](ComparatorChallenges/Proposition43.json) |
| Lemma 5.1, Moving trace operators | [`CalderonPaper.lemma51`](Proof/Manuscript/Lemma51.lean) | [Statement](ComparatorChallenges/Lemma51.lean) | [`Lemma51.json`](ComparatorChallenges/Lemma51.json) |
| Lemma 5.2, Weighted raising estimate | [`CalderonPaper.lemma52`](Proof/Manuscript/Lemma52.lean) | [Statement](ComparatorChallenges/Lemma52.lean) | [`Lemma52.json`](ComparatorChallenges/Lemma52.json) |
| Proposition 5.3, Coercivity for the moving trace equation | [`CalderonN.coercivity`](Proof/CalderonN/CheckedLocalExtension.lean) | [Statement](ComparatorChallenges/Proposition53.lean) | [`Proposition53.json`](ComparatorChallenges/Proposition53.json) |
| Lemma 5.4, Uniform transfer density | [`CalderonPaper.lemma54`](Proof/Manuscript/Lemma54.lean) | [Statement](ComparatorChallenges/Lemma54.lean) | [`Lemma54.json`](ComparatorChallenges/Lemma54.json) |
| Lemma 6.1, Two-power moment bound | [`CalderonPaper.lemma61`](Proof/Manuscript/Lemma61.lean) | [Statement](ComparatorChallenges/Lemma61.lean) | [`Lemma61.json`](ComparatorChallenges/Lemma61.json) |
| Lemma 6.2, Finite-order interpolation | [`CalderonPaper.lemma62`](Proof/Manuscript/Lemma62.lean) | [Statement](ComparatorChallenges/Lemma62.lean) | [`Lemma62.json`](ComparatorChallenges/Lemma62.json) |
| Lemma 6.3, Superlinear improvement | [`CalderonPaper.lemma63`](Proof/Manuscript/Lemma63.lean) | [Statement](ComparatorChallenges/Lemma63.lean) | [`Lemma63.json`](ComparatorChallenges/Lemma63.json) |
| Proposition 7.1, No interior frontier | [`CalderonPaper.proposition71`](Proof/Manuscript/Proposition71.lean) | [Statement](ComparatorChallenges/Proposition71.lean) | [`Proposition71.json`](ComparatorChallenges/Proposition71.json) |
| Proposition 7.2, Smooth completion and the accessible gauge | [`CalderonPaper.proposition72`](Proof/Manuscript/Proposition72.lean) | [Statement](ComparatorChallenges/Proposition72.lean) | [`Proposition72.json`](ComparatorChallenges/Proposition72.json) |
| Lemma 8.1, Conformal rigidity at a boundary patch | [`CalderonPaper.lemma81`](Proof/Manuscript/Lemma81.lean) | [Statement](ComparatorChallenges/Lemma81.lean) | [`Lemma81.json`](ComparatorChallenges/Lemma81.json) |

## Build

Install [elan](https://github.com/leanprover/elan) and Git. The package pins Lean `4.35.0-rc3`, Mathlib `f6090c7095e1e56b3464c1daba5f24631f1290d2`, and its transitive dependencies. The used Tau Ceti sources are bundled. Run from the repository root.

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

Allow at least a few hours for a first serial build and a full run of the comparator checks. Build time depends on available cores, memory, and the Mathlib cache. Use a 64-bit machine with at least 16 GiB RAM and 30 GiB free disk space. The comparator uses Linux with [bubblewrap](https://github.com/containers/bubblewrap) on `PATH` and user namespaces enabled.

## Run the comparator challenges

Choose any result in the [statement index](#manuscript-statements) and use its configuration in the comparator command.

```sh
./check-challenge.sh
lake comparator --config ComparatorChallenges/Corollary13.json
```

The comparator checks the selected theorem type against its frozen statement, including the definitions the statement uses. It then replays the solution in Lean’s kernel with `propext`, `Quot.sound`, and `Classical.choice` permitted. The challenge source contains one intentional `sorry` for the target declaration. [Validation](docs/VALIDATION.md)

## License and citation

Original project contributions use the [BSD 3-Clause License](LICENSE). The bundled Tau Ceti and adapted conformal Poisson material retain their upstream licenses and notices. [Third-party notices](THIRD_PARTY_NOTICES.md) · [Acknowledgements](docs/ACKNOWLEDGEMENTS.md) · [Citation metadata](CITATION.cff)
