# Review the frozen statements

Use this guide with the pinned manuscript and the frozen Lean sources. Each entry links directly to the statement and to the definitions that give its hypotheses and conclusion meaning. The selector links show the supporting theorem types that Comparator also checks. [Edition and workspace](README.md)

When inspecting a Lean file in an editor or with Lake, open `ComparatorChallenges` as the workspace. Its `Proof.*` module names resolve to frozen files under `ComparatorChallenges/Source/Proof`. The command below builds the frozen statements.

```sh
cd ComparatorChallenges
lake build ComparatorChallenges.All
```

## Uniqueness and its corollaries

### Theorem 1.1

**Smooth anisotropic uniqueness from one patch**

Read the equality of quadratic Dirichlet energies on the patch, then the two conditions on the diffeomorphism. The diffeomorphism pulls the first metric back to the second.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/01-introduction.tex#L54-L68) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Theorem11.lean#L13) · [`Theorem11` selector](../../ComparatorChallenges/targets.json#L903)

Definitions to read first include [`IsMetricVolume`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L43), [`PatchEnergyEqual`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L62), [`FixesPatch`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L69), [`PullbackMetric`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L73).

### Corollary 1.2

**Full-boundary uniqueness**

The patch argument is the entire boundary. Check the order of the metric arguments in the pullback and the pointwise boundary condition.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/01-introduction.tex#L84-L89) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Corollary12.lean#L13) · [`Corollary12` selector](../../ComparatorChallenges/targets.json#L2)

Definitions to read first include [`PatchEnergyEqual`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L62), [`FixesPatch`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L69), [`PullbackMetric`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L73).

### Corollary 1.3

**Smooth scalar uniqueness from one patch**

The smooth manifold structure is on the Euclidean closure, and the measurement patch is on its Euclidean frontier. The conclusion is equality of the two conductivities on the closure.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/01-introduction.tex#L115-L125) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Corollary13.lean#L13) · [`Corollary13` selector](../../ComparatorChallenges/targets.json#L16)

Definitions to read first include [`EuclideanClosure`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarConductivityDefs.lean#L22), [`SmoothThrough`](../../ComparatorChallenges/Source/Proof/Manuscript/Lemma81Defs.lean#L16), [`ScalarPatchEnergyEqual`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarConductivityDefs.lean#L76).

## Boundary and Green data

### Lemma 2.1

**Boundary jets**

The paired boundary box identifies the tangential coordinates. The statement compares all metric components after an arbitrary word of coordinate derivatives, evaluated on the normal face.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/02-boundary-data.tex#L44-L51) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma21.lean#L20) · [`Lemma21` selector](../../ComparatorChallenges/targets.json#L32)

Definitions to read first include [`PairedNativeBoundaryBox`](../../ComparatorChallenges/Source/Proof/CalderonPatch/PairedNativeBoundaryBox.lean#L34), [`chartDerivativeWord`](../../ComparatorChallenges/Source/Proof/CalderonN/ChartSchwarzWords.lean#L237), [`PatchEnergyEqual`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L62).

### Proposition 2.2

**Common cap and Green data**

Follow the witnesses in order. The common cap determines the old boundary that becomes interior, then the metric volumes and kernels, then the agreement of inverse solutions for matched sources.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/02-boundary-data.tex#L173-L184) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition22.lean#L22) · [`Proposition22` selector](../../ComparatorChallenges/targets.json#L523)

Definitions to read first include [`MeasuredCommonCap`](../../ComparatorChallenges/Source/Proof/CalderonPatch/MeasuredCommonCap.lean#L149), [`IsDirichletGreenKernel`](../../ComparatorChallenges/Source/Proof/CalderonN/GreenRestriction.lean#L32), [`RepresentsNativeInverse`](../../ComparatorChallenges/Source/Proof/CalderonPatch/NativeCapSourceFamily.lean#L291).

### Lemma 2.3

**Separation and finite harmonic jets**

The four conclusions concern the zero boundary trace, nonvanishing, separation of points, and the range of the second jet. In the last clause the chart is centered at zero and the range equals the kernel of the Laplacian on jets.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/02-boundary-data.tex#L305-L320) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma23.lean#L23) · [`Lemma23` selector](../../ComparatorChallenges/targets.json#L64)

Definitions to read first include [`smoothSourceSubmodule`](../../ComparatorChallenges/Source/Proof/CalderonPatch/GreenInversePairing.lean#L36), [`smoothInverse`](../../ComparatorChallenges/Source/Proof/CalderonPatch/GreenInversePairing.lean#L88), [`smoothSecondJet`](../../ComparatorChallenges/Source/Proof/CalderonPatch/CompactSecondJet.lean#L41), [`laplaceOnSecondJet`](../../ComparatorChallenges/Source/Proof/CalderonPatch/HarmonicJets.lean#L49).

## Product continuation

### Theorem 3.1

**Local metric extension**

Check the common harmonic chart and the equalities on the given side. The finite paired harmonic functions supply the Hessian span used to extend metric agreement to a ball about zero.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/03-product-continuation.tex#L12-L30) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Theorem31.lean#L13) · [`Theorem31` selector](../../ComparatorChallenges/targets.json#L917)

Definitions to read first include [`ContainsSmoothSide`](../../ComparatorChallenges/Source/Proof/CalderonN/Chart.lean#L45), [`GreenGerm`](../../ComparatorChallenges/Source/Proof/CalderonN/Chart.lean#L36), [`HessianSpanning`](../../ComparatorChallenges/Source/Proof/CalderonN/Chart.lean#L55).

### Lemma 3.2

**Extension from a cross**

The interpolation exponents must sum to more than one. Read the fixed-operator extension first, then the uniform estimate with a positive margin and finitely many controlled coefficient derivatives.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/03-product-continuation.tex#L82-L105) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma32.lean#L14) · [`Lemma32` selector](../../ComparatorChallenges/targets.json#L184)

Definitions to read first include [`ScalarElliptic`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarElliptic.lean#L21), [`CrossData`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarElliptic.lean#L79), [`CrossExtension`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarElliptic.lean#L87).

### Proposition 3.3

**Product extension criterion**

Check the strict Hessian condition at the base point. The neighborhood and compact arms are selected before the smoothly perturbed families, and the derivative estimate uses those same arms.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/03-product-continuation.tex#L260-L280) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition33.lean#L16) · [`Proposition33` selector](../../ComparatorChallenges/targets.json#L669)

Definitions to read first include [`ScalarElliptic`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarElliptic.lean#L21), [`ProductStrictHessianAt`](../../ComparatorChallenges/Source/Proof/CalderonN/ProductMetricHessian.lean#L47).

### Lemma 3.4

**Propagation through a compact cylinder**

The cylinder starts with its top and lateral boundary in the seeded region. The phase selects the portion above each level, and the conclusion gives continuation with compact data drawn from the initial region.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/03-product-continuation.tex#L406-L421) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma34.lean#L15) · [`Lemma34` selector](../../ComparatorChallenges/targets.json#L194)

Definitions to read first include [`ScalarElliptic`](../../ComparatorChallenges/Source/Proof/Manuscript/ScalarElliptic.lean#L21), [`ProductStrictHessianAt`](../../ComparatorChallenges/Source/Proof/CalderonN/ProductMetricHessian.lean#L47).

### Proposition 3.5

**Fixed-separation initialization**

Fix the separation, the scale, and the derivative order before taking small positive dilations. The continuation satisfies both dilated equations and agrees with the prescribed kernels on the seeded regions.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/03-product-continuation.tex#L486-L499) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition35.lean#L17) · [`Proposition35` selector](../../ComparatorChallenges/targets.json#L681)

Definitions to read first include [`ContainsAlignedSide`](../../ComparatorChallenges/Source/Proof/CalderonN/ChartNormalization.lean#L28), [`fixedSeparationSet`](../../ComparatorChallenges/Source/Proof/CalderonN/FixedTube/Initialization.lean#L108), [`ProductSolutionOn`](../../ComparatorChallenges/Source/Proof/CalderonN/GreenCross.lean#L30).

## Shrinking spheres

### Lemma 4.1

**Profile bounds**

The choice of depth precedes the radius parameters. Follow the logarithmic derivative estimates, the smallness of the radius times the squared profile parameter, and the regularity of the radius family.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/04-shrinking-balls.tex#L116-L134) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma41.lean#L18) · [`Lemma41` selector](../../ComparatorChallenges/targets.json#L206)

Definitions to read first include [`conformalDepth`](../../ComparatorChallenges/Source/Proof/CalderonN/ConformalDepth.lean#L40), [`shrinkingRadius`](../../ComparatorChallenges/Source/Proof/CalderonN/Radius.lean#L27), [`beta`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L70).

### Proposition 4.2

**Continuation to the sphere family**

The normal-coordinate family and its cutoffs come first. The same continued kernel provides both product equations and the matching conditions on the lower and fixed-separation seeds.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/04-shrinking-balls.tex#L224-L239) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition42.lean#L19) · [`Proposition42` selector](../../ComparatorChallenges/targets.json#L691)

Definitions to read first include [`NormalCoordinates`](../../ComparatorChallenges/Source/Proof/CalderonN/MovingTrace.lean#L33), [`lowerNormalSeed`](../../ComparatorChallenges/Source/Proof/CalderonN/MovingSphere/RadiusSeed.lean#L181), [`ProductSolutionOn`](../../ComparatorChallenges/Source/Proof/CalderonN/GreenCross.lean#L30).

### Proposition 4.3

**The transfer density**

The assumption supplies a single continued kernel for each pair of parameters. Follow its conormal flux into the transfer operator, then check harmonicity, reproduction, and the angular bounds.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/04-shrinking-balls.tex#L364-L387) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition43.lean#L19) · [`Proposition43` selector](../../ComparatorChallenges/targets.json#L704)

Definitions to read first include [`densityValue`](../../ComparatorChallenges/Source/Proof/Manuscript/TransferDensity.lean#L21), [`normalSphereGreenFlux`](../../ComparatorChallenges/Source/Proof/CalderonN/NormalGreenFlux.lean#L93), [`angularBaseJetBound`](../../ComparatorChallenges/Source/Proof/Manuscript/TransferDensity.lean#L30).

## Angular estimates

### Lemma 5.1

**Moving trace operators**

The index ranges over both the metric parameter and the admitted radii at that parameter. Read the trace-adjoint expansion and the vanishing trace on the Green-flux density with this same radius.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/05-angular-estimate.tex#L64-L97) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma51.lean#L16) · [`Lemma51` selector](../../ComparatorChallenges/targets.json#L216)

Definitions to read first include [`AdmittedTraceRadius`](../../ComparatorChallenges/Source/Proof/Manuscript/MovingTraceSymbols.lean#L314), [`actualMovingTraceAdjoint`](../../ComparatorChallenges/Source/Proof/CalderonN/ActualMovingTraceAdjoint.lean#L76), [`movingTrace`](../../ComparatorChallenges/Source/Proof/CalderonN/MovingTrace.lean#L91).

### Lemma 5.2

**Weighted raising estimate**

The floor and positive estimate constant are chosen before the metric, frame, radius, and test field. The resulting harmonic expansion and angular model supply the raising and lowering squares.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/05-angular-estimate.tex#L253-L263) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma52.lean#L15) · [`Lemma52` selector](../../ComparatorChallenges/targets.json#L251)

Definitions to read first include [`Profile`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L74), [`HarmonicTestExpansion`](../../ComparatorChallenges/Source/Proof/CalderonN/HarmonicTestExpansion.lean#L59), [`AngularModelData`](../../ComparatorChallenges/Source/Proof/CalderonN/PhysicalAngularModelData.lean#L67).

### Proposition 5.3

**Coercivity for the moving trace equation**

The single theorem binder gives the dimension bound. Open the frozen `Coercivity` predicate to read the remaining hypotheses, the uniform threshold order, and the moving-trace estimate.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/05-angular-estimate.tex#L426-L441) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition53.lean#L11) · [`Proposition53` selector](../../ComparatorChallenges/targets.json#L733)

Definitions to read first include [`Coercivity`](../../ComparatorChallenges/Source/Proof/CalderonN/Coercivity.lean#L107), [`Profile`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L74), [`movingTrace`](../../ComparatorChallenges/Source/Proof/CalderonN/MovingTrace.lean#L91).

### Lemma 5.4

**Uniform transfer density**

The constant bounds the flux after multiplication by the base cutoff. Check that the bound is uniform for sufficiently small positive dilations and all admitted shrinkage parameters.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/05-angular-estimate.tex#L606-L616) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma54.lean#L22) · [`Lemma54` selector](../../ComparatorChallenges/targets.json#L417)

Definitions to read first include [`UniformCylinderScaledGreenDataJets`](../../ComparatorChallenges/Source/Proof/CalderonN/ConformalScaledGreenDataJets.lean#L218), [`movingGreenFluxDensity`](../../ComparatorChallenges/Source/Proof/CalderonN/MovingGreenFluxDensity.lean#L36), [`Small`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L93).

## Bootstrap

### Lemma 6.1

**Two-power moment bound**

Read the moment bound for the difference of each renormalized harmonic pair divided by the square of the radius. The same bound works for the whole paired family.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/06-bootstrap.tex#L36-L44) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma61.lean#L20) · [`Lemma61` selector](../../ComparatorChallenges/targets.json#L455)

Definitions to read first include [`renormalizedHarmonic`](../../ComparatorChallenges/Source/Proof/CalderonN/DilationHarmonic.lean#L28), [`shrinkingRadius`](../../ComparatorChallenges/Source/Proof/CalderonN/Radius.lean#L27), [`Small`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L93).

### Lemma 6.2

**Finite-order interpolation**

The order-`m` derivative is bounded on the closed ball. For `j < m`, the conclusion combines the local `L²` norm on the open ball with the highest-order bound, using the explicit powers of the radius.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/06-bootstrap.tex#L108-L117) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma62.lean#L17) · [`Lemma62` selector](../../ComparatorChallenges/targets.json#L482)

Definitions to read first include [`X`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L23).

### Lemma 6.3

**Superlinear improvement**

The smallness hypothesis controls the radius and the order-eight jet. On the cylinder core, sufficiently small radius gives the improved exponent `3 / 2`.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/06-bootstrap.tex#L142-L151) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma63.lean#L19) · [`Lemma63` selector](../../ComparatorChallenges/targets.json#L488)

Definitions to read first include [`Small`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L93), [`smallJet`](../../ComparatorChallenges/Source/Proof/CalderonN/Coordinates.lean#L88), [`cylinderCore`](../../ComparatorChallenges/Source/Proof/CalderonN/CylinderCutoff.lean#L23).

## Globalization

### Proposition 7.1

**No interior frontier**

The cap map runs from the second manifold to the first. Check the support conditions on both sources and their agreement after transport, then read the conclusion for the same evaluations on the extended interiors.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/07-globalization.tex#L30-L36) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition71.lean#L23) · [`Proposition71` selector](../../ComparatorChallenges/targets.json#L748)

Definitions to read first include [`DirichletData`](../../ComparatorChallenges/Source/Proof/CalderonPatch/DirichletHilbert.lean#L69), [`IsLocalMetricIsometry`](../../ComparatorChallenges/Source/Proof/CalderonPatch/MatchedCoordinates.lean#L27), [`smoothSourceSubmodule`](../../ComparatorChallenges/Source/Proof/CalderonPatch/GreenInversePairing.lean#L36), [`smoothInverse`](../../ComparatorChallenges/Source/Proof/CalderonPatch/GreenInversePairing.lean#L88).

### Proposition 7.2

**Smooth completion and the accessible gauge**

Track the interior isometry, its completion, and the induced map of the original copies. The commuting identity with the two embeddings fixes the relation between those maps.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/07-globalization.tex#L164-L172) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Proposition72.lean#L16) · [`Proposition72` selector](../../ComparatorChallenges/targets.json#L847)

Definitions to read first include [`MeasuredCommonCap`](../../ComparatorChallenges/Source/Proof/CalderonPatch/MeasuredCommonCap.lean#L149), [`IsLocalMetricIsometry`](../../ComparatorChallenges/Source/Proof/CalderonPatch/MatchedCoordinates.lean#L27), [`FixesPatch`](../../ComparatorChallenges/Source/Proof/CalderonPatch/Energy.lean#L69).

## Conformal rigidity

### Lemma 8.1

**Conformal rigidity at a boundary patch**

The conformal factor is written logarithmically. The conclusion gives identity of the diffeomorphism and zero conformal factor on the closure from the pointwise boundary condition.

[Manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/08-scalar-consequence.tex#L10-L21) · [Frozen Lean statement](../../ComparatorChallenges/Source/ComparatorChallenges/Lemma81.lean#L12) · [`Lemma81` selector](../../ComparatorChallenges/targets.json#L515)

Definitions to read first include [`HasSmoothEuclideanBoundary`](../../ComparatorChallenges/Source/Proof/Manuscript/Lemma81Defs.lean#L22), [`IsClosureDiffeomorphism`](../../ComparatorChallenges/Source/Proof/Manuscript/Lemma81Defs.lean#L29), [`EuclideanConformalOn`](../../ComparatorChallenges/Source/Proof/Manuscript/Lemma81Defs.lean#L36).
