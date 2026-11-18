# OpenAI Calderón formalization in Lean

**Project authors: Cătălin I. Cârstea and Lauri Oksanen.**

This repository is intended to grow toward a Lean formalization of the OpenAI anisotropic Calderón result. The completed component so far is Proposition 5.3 in dimension three:

Lean sources for the shrinking-sphere estimate: the four-term weighted energy of every smooth fiberwise mean-zero field is controlled by the physical moving-trace operator. The estimate is uniform over the admitted metrics, moving frames and arbitrary radius profiles, with the original `Fin 9` smallness convention.

The theorem is `ShrinkingSpheres.coercivity`, in [`Solution.lean`](Solution.lean). Its independent statement and defining declarations are preserved in [`ComparatorChallenges/`](ComparatorChallenges/). The proof uses the same geometric definitions from [`Proof/Geometry.lean`](Proof/Geometry.lean).

```lean
theorem coercivity (Y Ω : Set X) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hcpt : IsCompact (closure Y)) (hin : closure Y ⊆ Ω) :
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
        UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C
```

## Time and system requirements

Allow several hours for a first source build. A complete clean verification of this release took about 8 hours 23 minutes on the development machine, including source compilation, dependency auditing, exact comparisons and fresh-kernel replay. Actual time depends on the machine and available dependency caches; cached builds are quicker.

| Resource | Recommendation |
| --- | --- |
| Software | Pinned Lean toolchain, Git, and network access for dependencies |
| Processor and OS | Modern 64-bit CPU supported by Lean; Linux with bubblewrap for the comparator |
| Memory | 16 GiB system RAM for a serial build; 32 GiB recommended for parallel builds |
| Free disk space | At least 50 GiB, preferably on an SSD |

The completed verification used a 9000 MiB bound per checking process. An 8 GiB system may not have enough memory for the largest modules and the operating system.

## Build and inspect the sources

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

`lean-toolchain` selects Lean **4.35.0-rc3**. Mathlib and its dependencies are locked by `lake-manifest.json`; the Mathlib revision is `f6090c7095e1e56b3464c1daba5f24631f1290d2`. The 82 used Tau Ceti source modules are bundled under `Proof/TauCeti/` and need no separate checkout.

`Check.lean` prints the theorem's type and axiom dependencies, the closed physical comparison's dependencies, and the frozen zero-output consumer's dependencies.

## Checking against the challenge

After the build, run the comparator shipped with Lake:

```sh
./check-challenge.sh
lake comparator --config ComparatorChallenges/Proposition53.json
```

It needs [bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) on `PATH`. It builds and exports the challenge and solution in a sandbox, compares `ShrinkingSpheres.coercivity` and its reachable defining declarations, permits only `propext`, `Quot.sound` and `Classical.choice`, and replays the proof through Lean's kernel. No definition holes are permitted. A plain `lake build` excludes the challenge module because its intentionally open theorem contains `sorry`.

`./check-challenge.sh` verifies the independent statement copy, selected text and dependency pins. The challenge is the approved translation of the supplied standalone Proposition 5.3, not the separate anisotropic-uniqueness challenge used by the reference repository.

## Reading the sources

- [Proof guide](docs/PROOF_GUIDE.md): principal files and the route to the theorem.
- [Selected-text crosswalk](docs/proof-map/README.md): source passages and completed Lean constructions.
- [Selected statement and edition](docs/statement/README.md): exact text, translation and conventions.
- [Mathematical working text](docs/expansion/README.md): preserved mathematical expansion.
- [Third-party attribution](THIRD_PARTY_NOTICES.md): bundled upstream code and licenses.
- [Validation](docs/VALIDATION.md): package verification and source preservation.

## Scope

This repository proves the dimension-three shrinking-sphere coercivity estimate. It does not claim the full inverse-problem uniqueness theorem. No additional analytic estimate is a parameter of the selected root.

The source package contains the proof sources, independent challenge, pinned dependencies and build instructions. Private workflow databases, chat metadata, review administration, build outputs, compiled objects and dependency caches are omitted. The 2,723 released Lean source files retain their exact contents and module paths.

## License and citation

Original project contributions use the [BSD 3-Clause License](LICENSE). Bundled Tau Ceti code retains its Apache 2.0 license and existing notices. Other upstream material retains its own terms; see [third-party notices](THIRD_PARTY_NOTICES.md).

If you use or build upon this formalization, please cite Cătălin I. Cârstea and Lauri Oksanen, *OpenAI Calderón formalization in Lean*. Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

We acknowledge the Lean and Mathlib developers and the [Tau Ceti project](https://github.com/TauCetiProject/TauCeti) and contributors. Their original code, author notices and licenses are preserved. The funding acknowledgements accompanying the supplied formalization are preserved in [the acknowledgements document](docs/ACKNOWLEDGEMENTS.md).
