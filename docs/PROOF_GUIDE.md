# Guide to the Lean proof

Find every Lean statement and comparator in the [manuscript index](../README.md#manuscript-statements).

## The local-to-global proof

| Source step | Implementation |
| --- | --- |
| Proposition 5.3, physical norm estimate | [Coercivity statement and energy](../Proof/CalderonN/Coercivity.lean), [principal integrated error](../Proof/CalderonN/UniformActualPrincipalTraceError.lean), [gain and absorption](../Proof/CalderonN/ActualPerturbationCoercivity.lean), [root](../Proof/CalderonN/CheckedLocalExtension.lean#L384) |
| Theorem 3.1, shrinking-sphere transfer and local equality | [Green kernel restriction](../Proof/CalderonN/GreenRestriction.lean), [actual conformal Green transfer](../Proof/CalderonN/ConformalActualGreenTransfer.lean), [weighted moment and agreement](../Proof/CalderonN/WeightedMomentAgreement.lean), [root](../Proof/CalderonN/CheckedLocalExtension.lean#L392) |
| Theorem 1.1, boundary measurements and cap | [Energy definitions](../Proof/CalderonPatch/Energy.lean), [measured normal metric jets](../Proof/CalderonPatch/MeasuredBoundaryJets.lean), [cap construction](../Proof/CalderonPatch/MeasuredCommonCap.lean), [cap agreement](../Proof/CalderonPatch/NativeCapAgreement.lean) |
| Theorem 1.1, interior continuation and boundary gauge | [Shared cap Green kernels and source jets](../Proof/CalderonPatch/GlobalFromNativeCapSources.lean), [touching-ball application](../Proof/CalderonPatch/FrontierLocalExtension.lean#L61), [smooth extension](../Proof/CalderonPatch/OriginalFromInterior.lean), [entire measured patch](../Proof/CalderonPatch/MeasuredAccessibleGauge.lean), [root](../Proof/Manuscript/AnisotropicUniqueness.lean#L19) |

The coercivity proof generalizes the Fischer decomposition and zonal sphere projections, estimates the actual principal error in the physical energy norm, and absorbs the second-metric drift. The local extension proof calls this estimate on the cutoff transfer density produced by the actual Green kernel. The same dimension is used for the estimate, the Green kernel, and the metric equality.

The global proof uses finite boundary-layer solutions to extract normal metric jets from the measured pairing. A smooth truncation of the difference of two cap solutions gives a Green flux identity across the attachment seam. The resulting cap agreement supplies a common family of sources, their actual Green kernels, and the harmonic coordinates and Hessian witnesses needed at an interior frontier. The touching-ball call to Theorem 3.1 extends the match across the frontier. Smooth completion and measured conormal equality produce the diffeomorphism on the original manifold and fix the whole measured patch.

The [global consumer](../Consumer.lean) recovers the tangent-energy identity for every tangent vector. The [local consumers](../Applications/Local.lean) apply Proposition 5.3 to zero trace output and Theorem 3.1 to chart gluing and ambient Dirichlet Green kernels. [Source provenance](provenance/checked-sources.json)

## Corollaries

Corollary 1.2 applies Theorem 1.1 after removing a point from the boundary. A half-space chart gives density of the punctured boundary. Continuity extends the fixed-point identity, and inversion gives the pullback direction in the manuscript. [Proof](../Proof/Manuscript/Corollary12.lean)

Corollary 1.3 uses the weak quadratic Dirichlet-to-Neumann form of the scalar equation. The `EuclideanClosure` data express the induced smooth structure, inclusion, metric, and volume of the domain closure. The proof identifies the conductivity form with the energy of the conformally scaled metric, applies Theorem 1.1, and proves smooth extension of the resulting Euclidean conformal map and its inverse to apply Lemma 8.1. [Proof](../Proof/Manuscript/Corollary13.lean)
