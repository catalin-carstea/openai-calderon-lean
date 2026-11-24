# Selected statements and edition

The source is OpenAI's September 24, 2026 manuscript, *Smooth anisotropic uniqueness in the Calderón problem from one boundary patch*, at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. [Pinned PDF](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/paper.pdf) · [Source hashes](source-lock.json)

## Current reading surface

Begin with the [24 numbered statements](../../README.md#manuscript-statements). Their files live in [ComparatorChallenges/Source/ComparatorChallenges](../../ComparatorChallenges/Source/ComparatorChallenges), alongside a [frozen copy of their local dependency declarations](../../ComparatorChallenges/Source/Proof). The second tree retains the declaring module names so Lean's generated names match across the two builds. Every project-local import resolves inside the frozen workspace. The external dependencies are pinned in its own Lake manifest.

Some definitions contain proofs, such as the closure fields of a submodule. The [aggregate configuration](../../comparator.json) lists the 368 supporting theorem types required by those definitions after the 24 manuscript declarations. Comparator requires exact statements for all listed theorems, checks the reachable definition bodies, and replays the matching solution proofs. The `sorry` terms in the frozen workspace mark these proof obligations. `definition_names` is empty, so reachable definitions have no implementation holes.

Run `../../check-challenge.sh` from this directory to verify the files against the [statement manifest](SHA256SUMS). The [validation guide](../VALIDATION.md) describes the checks.

## Historical references

| Result | Manuscript locator | Frozen Lean reference |
| --- | --- | --- |
| Theorem 1.1 | §1, `main:patch`, `01-introduction.tex` lines 54–68 | [Global.lean](https://github.com/catalin-carstea/openai-calderon-lean/blob/0b06639c667dfd22ce6b08f24e1354538da405c2/docs/statement/frozen/Global.lean) |
| Theorem 3.1 | §3, `local:extension`, `03-product-continuation.tex` lines 12–30 | [Local.lean](https://github.com/catalin-carstea/openai-calderon-lean/blob/0b06639c667dfd22ce6b08f24e1354538da405c2/docs/statement/frozen/Local.lean) |
| Proposition 5.3 | §5, `angular:coercivity`, `05-angular-estimate.tex` lines 426–440 | [Local.lean](https://github.com/catalin-carstea/openai-calderon-lean/blob/0b06639c667dfd22ce6b08f24e1354538da405c2/docs/statement/frozen/Local.lean) |

Theorem 1.1 uses smooth metrics and a smooth diffeomorphism on Mathlib's half-space model. Its partial boundary measurements are the diagonal Dirichlet energy pairing on supported smooth data. The proof obtains the bilinear pairing by polarization and uses the canonical positive metric volumes. Theorem 3.1 binds the smooth matching side, harmonic coordinates, paired harmonic functions, and full trace-free Hessian span in the common chart. The ambient-kernel application proves the two chart Green hypotheses. Proposition 5.3 preserves the eight-jet smallness condition, arbitrary admitted radius profiles, and the quantifier order for the uniform thresholds. The theorem statements specialize to `n = 3` by supplying `3 ≤ n`.

The original GitHub revision preserves the individually reviewed reference files in its `docs/statement/frozen/` directory.
