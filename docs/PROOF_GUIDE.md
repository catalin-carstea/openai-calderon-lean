# Guide to the proof sources

The entry point is [`Solution.lean`](../Solution.lean). It obtains the complete physical principal norm comparison and applies uniform absorption to prove `ShrinkingSpheres.coercivity`. The theorem supplies the finite background order `m = 10`.

| Part | Source |
| --- | --- |
| Exact geometric definitions and uniform estimate | [`Proof/Geometry.lean`](../Proof/Geometry.lean) |
| Final theorem | [`Solution.lean`](../Solution.lean) |
| Frozen downstream application | [`Consumer.lean`](../Consumer.lean) |
| Closed physical comparison | [`Proof/PhysicalTruncatedNormComparisonClosed.lean`](../Proof/PhysicalTruncatedNormComparisonClosed.lean) |
| Common sector assembly | [`Proof/ParallelNormAssemblyUniform.lean`](../Proof/ParallelNormAssemblyUniform.lean) |
| Complete first-order self comparison | [`Proof/ParallelFirstSelf.lean`](../Proof/ParallelFirstSelf.lean) |
| Scalar/first-order cross comparison | [`Proof/ParallelScalarFirst.lean`](../Proof/ParallelScalarFirst.lean) |
| Remaining actual potential and model sectors | [`Proof/ParallelNormAssemblyReservedComplete.lean`](../Proof/ParallelNormAssemblyReservedComplete.lean) |
| Truncated comparison and physical lower bound | [`Proof/PhysicalTruncatedNormComparison.lean`](../Proof/PhysicalTruncatedNormComparison.lean) |
| Genuine Dirichlet/physical realization | [`Proof/PhysicalStrongPoissonRealization.lean`](../Proof/PhysicalStrongPoissonRealization.lean) |
| Uniform finite coercivity | [`Proof/UniformFiniteCoercivity.lean`](../Proof/UniformFiniteCoercivity.lean) |
| Finite-to-smooth energy limit | [`Proof/FullEnergyLimit.lean`](../Proof/FullEnergyLimit.lean) |
| Final absorption | [`Proof/Absorption.lean`](../Proof/Absorption.lean) |
| Bundled analytic library | [`Proof/TauCeti/`](../Proof/TauCeti/) |

The proof uses direct Sobolev/Dirichlet constructions and finite-word estimates rather than reconstructing a symbol parametrix. The whole second-metric drift and uniformly H¹-bounded complements are absorbed separately, as allowed by the selected expansion. A Hilbert-space norm-square partner appears only after the genuine physical one-sided comparison is proved; it is not asserted to be the physical formal adjoint.

Imports describe formal dependencies. Inspect the constructions and actual inference bodies rather than treating file names as proof evidence. Names such as `Parallel`, `Actual` and version tags record development history, not unfinished proofs. All solution sources are byte-identical to the released proof. The naming adapter in `Proof/FrozenDeclarationHygiene.lean` uses ordinary declaration elaboration to preserve the approved compiler-generated binder names after modularization; it does not replace mathematical definitions or the kernel.

The independent challenge has its intentional `sorry`. It is outside the default build and is never imported by the proof. The comparator checks the theorem against it using only `propext`, `Quot.sound` and `Classical.choice`, compares the reachable defining declarations and replays the exported proof in Lean's kernel.
