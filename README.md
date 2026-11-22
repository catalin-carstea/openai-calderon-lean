# OpenAI Calderón formalization in Lean

**Project authors: Cătălin I. Cârstea and Lauri Oksanen.**

This Lean package formalizes three results from OpenAI's *Smooth anisotropic uniqueness in the Calderón problem from one boundary patch* for every dimension `n ≥ 3`. Theorem 1.1 applies Theorem 3.1 at a touching ball. Theorem 3.1 uses Proposition 5.3 in that same dimension. [Selected manuscript and translations](docs/statement/README.md)

| Result | Lean theorem and proof | Comparator |
| --- | --- | --- |
| Theorem 1.1, smooth anisotropic uniqueness | [`CalderonPatch.smoothAnisotropicUniqueness`](Solution.lean#L19) | [Statement](ComparatorChallenges/Theorem11.lean) · [Configuration](ComparatorChallenges/Theorem11.json) |
| Theorem 3.1, local metric extension | [`CalderonN.localMetricExtension`](Proof/CalderonN/CheckedLocalExtension.lean#L392) | [Statement](ComparatorChallenges/Theorem31.lean) · [Configuration](ComparatorChallenges/Theorem31.json) |
| Proposition 5.3, moving trace coercivity | [`CalderonN.coercivity`](Proof/CalderonN/CheckedLocalExtension.lean#L384) | [Statement](ComparatorChallenges/Proposition53.lean) · [Configuration](ComparatorChallenges/Proposition53.json) |

Use `import Solution` for Theorem 1.1 and `import Proof.CalderonN.CheckedLocalExtension` for the two local results.

Theorem 1.1 expresses the measured data as equality of smooth Dirichlet energies for traces supported in the open patch. It produces a smooth diffeomorphism that fixes every point of the patch and pulls back the first metric to the second. Theorem 3.1 uses the two Dirichlet Green kernels in their common harmonic chart. Proposition 5.3 controls the four-term energy of smooth sphere-mean-zero tests by the actual moving trace, uniformly over the admitted metrics and radius profiles. [Proof guide](docs/PROOF_GUIDE.md)

## Build

Install [elan](https://github.com/leanprover/elan) and Git. The package pins Lean `4.35.0-rc3`, Mathlib `f6090c7095e1e56b3464c1daba5f24631f1290d2`, and its transitive dependencies. The used Tau Ceti sources are bundled. Run from the repository root.

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

Allow at least a few hours for a first serial build and all three kernel replays. Build time depends on available cores, memory, and the Mathlib cache. Use a 64-bit machine with at least 16 GiB RAM and 30 GiB free disk space. The comparator uses Linux with [bubblewrap](https://github.com/containers/bubblewrap) on `PATH` and user namespaces enabled.

## Run the comparator challenges

```sh
./check-challenge.sh
lake comparator --config ComparatorChallenges/Theorem11.json
lake comparator --config ComparatorChallenges/Theorem31.json
lake comparator --config ComparatorChallenges/Proposition53.json
```

Each configuration checks one theorem against its frozen statement and the defining declarations it reaches. The challenge modules import their own frozen definition files under [`ComparatorChallenges/Frozen/`](ComparatorChallenges/Frozen/). Each has one intentional `sorry` at the target theorem. The ordinary proof build excludes the challenges. The comparator permits `propext`, `Quot.sound`, and `Classical.choice`, then replays the solution export in Lean's kernel. [Validation](docs/VALIDATION.md)

## License and citation

Original project contributions use the [BSD 3-Clause License](LICENSE). The bundled Tau Ceti and adapted conformal Poisson material retain their upstream licenses and notices. [Third-party notices](THIRD_PARTY_NOTICES.md) · [Acknowledgements](docs/ACKNOWLEDGEMENTS.md) · [Citation metadata](CITATION.cff)
