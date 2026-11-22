# Selected statements and edition

The source is OpenAI's September 24, 2026 manuscript, *Smooth anisotropic uniqueness in the Calderón problem from one boundary patch*, at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. [Pinned PDF](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/paper.pdf) · [Source hashes](source-lock.json)

## Original release statements

| Result | Manuscript locator | Frozen Lean reference |
| --- | --- | --- |
| Theorem 1.1 | §1, `main:patch`, `01-introduction.tex` lines 54–68 | [Global.lean](frozen/Global.lean) |
| Theorem 3.1 | §3, `local:extension`, `03-product-continuation.tex` lines 12–30 | [Local.lean](frozen/Local.lean) |
| Proposition 5.3 | §5, `angular:coercivity`, `05-angular-estimate.tex` lines 426–440 | [Local.lean](frozen/Local.lean) |

Theorem 1.1 uses smooth metrics and a smooth diffeomorphism on Mathlib's half-space model. Its partial boundary measurements are the diagonal Dirichlet energy pairing on supported smooth data. The proof obtains the bilinear pairing by polarization and uses the canonical positive metric volumes. Theorem 3.1 binds the smooth matching side, harmonic coordinates, paired harmonic functions, and full trace-free Hessian span in the common chart. The ambient-kernel application proves the two chart Green hypotheses. Proposition 5.3 preserves the eight-jet smallness condition, arbitrary admitted radius profiles, and the quantifier order for the uniform thresholds. The theorem statements specialize to `n = 3` by supplying `3 ≤ n`.

The `frozen/` tree preserves the reviewed source files. The original comparator modules extract one theorem each from those files. Their imports use a separate copy of the frozen definitions with the package's challenge module paths. The theorem and definition bodies retain their original names, binders, and mathematical content. Each comparator configuration leaves `definition_names` empty to require comparison of all reachable definitions. [Challenge sources](../../ComparatorChallenges) · [Challenge checksums](SHA256SUMS)

[Complete manuscript statement index](../../README.md#manuscript-statements)
