# Third-party code and attribution

The supplied formalization identifies Cătălin I. Cârstea and Lauri Oksanen as its project authors and BSD copyright holders. This credit does not attribute upstream analytic library code to them.

## Tau Ceti

The 82 Lean files under `Proof/TauCeti/` come from the Tau Ceti edition bundled in the selected supplied archive. The corresponding upstream edition is identified in the reference project's notices as revision `d87e7f1676050bccc88913a473d5aae77156313c` of [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

Their copyright and author notices are preserved. They retain the [Apache License, Version 2.0](Proof/TauCeti/LICENSE). Import paths have been rewritten from `TauCeti.*` to `Proof.TauCeti.*` for this proof's module layout; one file also has a cosmetic blank-line cleanup. No mathematical proof body was changed by this packaging. Per-file supplied and included hashes are listed in [the source provenance map](docs/SOURCE_PROVENANCE.json).

## Other dependencies and source material

Lean, Mathlib and its transitive packages are developed by their respective contributors. Their revisions are locked in `lean-toolchain` and `lake-manifest.json`; dependency sources and licenses are supplied by those packages.

The selected mathematical text is [Proposition 5.3 in dimension three](docs/statement/proposition-5-3-n3.tex), supplied with the proof source archive identified in the [edition note](docs/statement/README.md). Adapted source modules under `Proof/Archive/` retain their supplied provenance notices. The included proof also contains original local development, including AI-assisted authoring. All existing copyright and license notices remain in force.

The public layout and comparator command follow [catalin-carstea/anisotropic-calderon-lean](https://github.com/catalin-carstea/anisotropic-calderon-lean), at commit `0f09786282d0f2d3865fa0f175b63c35969d25f7`. This package proves the shrinking-sphere coercivity estimate, not that repository's full anisotropic uniqueness theorem.

Original project contributions use the [BSD 3-Clause License](LICENSE). Upstream material retains its existing terms.

## Bundled Tau Ceti files

- [`Proof/TauCeti/Analysis/Calculus/BumpFunction/Average.lean`](Proof/TauCeti/Analysis/Calculus/BumpFunction/Average.lean)
- [`Proof/TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean`](Proof/TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean)
- [`Proof/TauCeti/Analysis/Calculus/BumpFunction/FiniteDimension.lean`](Proof/TauCeti/Analysis/Calculus/BumpFunction/FiniteDimension.lean)
- [`Proof/TauCeti/Analysis/Calculus/ContinuousMap.lean`](Proof/TauCeti/Analysis/Calculus/ContinuousMap.lean)
- [`Proof/TauCeti/Analysis/Calculus/Gradient.lean`](Proof/TauCeti/Analysis/Calculus/Gradient.lean)
- [`Proof/TauCeti/Analysis/Calculus/IteratedGradient.lean`](Proof/TauCeti/Analysis/Calculus/IteratedGradient.lean)
- [`Proof/TauCeti/Analysis/Calculus/SegmentIncrement.lean`](Proof/TauCeti/Analysis/Calculus/SegmentIncrement.lean)
- [`Proof/TauCeti/Analysis/Distribution/TestFunction/Translation.lean`](Proof/TauCeti/Analysis/Distribution/TestFunction/Translation.lean)
- [`Proof/TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`](Proof/TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean)
- [`Proof/TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean`](Proof/TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean)
- [`Proof/TauCeti/Analysis/Normed/Group/Prod.lean`](Proof/TauCeti/Analysis/Normed/Group/Prod.lean)
- [`Proof/TauCeti/Analysis/Normed/Lp/ProdLp.lean`](Proof/TauCeti/Analysis/Normed/Lp/ProdLp.lean)
- [`Proof/TauCeti/Analysis/ODE/GlobalSolution.lean`](Proof/TauCeti/Analysis/ODE/GlobalSolution.lean)
- [`Proof/TauCeti/Analysis/ODE/InitialCondition.lean`](Proof/TauCeti/Analysis/ODE/InitialCondition.lean)
- [`Proof/TauCeti/Analysis/ODE/SmoothParameter.lean`](Proof/TauCeti/Analysis/ODE/SmoothParameter.lean)
- [`Proof/TauCeti/Analysis/PDE/DirichletProblem.lean`](Proof/TauCeti/Analysis/PDE/DirichletProblem.lean)
- [`Proof/TauCeti/Analysis/PDE/Ellipticity/Basic.lean`](Proof/TauCeti/Analysis/PDE/Ellipticity/Basic.lean)
- [`Proof/TauCeti/Analysis/PDE/Ellipticity/Energy.lean`](Proof/TauCeti/Analysis/PDE/Ellipticity/Energy.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Basic.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Basic.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Continuity.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Continuity.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Integrability.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Integrability.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Integrated/Basic.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Integrated/Basic.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Integrated/Symmetry.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Integrated/Symmetry.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Linearity.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Linearity.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Measurability.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Measurability.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyForm/VariableLp.lean`](Proof/TauCeti/Analysis/PDE/EnergyForm/VariableLp.lean)
- [`Proof/TauCeti/Analysis/PDE/EnergyLowerBounds.lean`](Proof/TauCeti/Analysis/PDE/EnergyLowerBounds.lean)
- [`Proof/TauCeti/Analysis/PDE/LowerOrder.lean`](Proof/TauCeti/Analysis/PDE/LowerOrder.lean)
- [`Proof/TauCeti/Analysis/PDE/Regularity/Basic.lean`](Proof/TauCeti/Analysis/PDE/Regularity/Basic.lean)
- [`Proof/TauCeti/Analysis/PDE/SymmetricEnergy.lean`](Proof/TauCeti/Analysis/PDE/SymmetricEnergy.lean)
- [`Proof/TauCeti/Analysis/Sobolev/CompactSupport.lean`](Proof/TauCeti/Analysis/Sobolev/CompactSupport.lean)
- [`Proof/TauCeti/Analysis/Sobolev/DifferenceQuotient.lean`](Proof/TauCeti/Analysis/Sobolev/DifferenceQuotient.lean)
- [`Proof/TauCeti/Analysis/Sobolev/GraphStep.lean`](Proof/TauCeti/Analysis/Sobolev/GraphStep.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Leibniz.lean`](Proof/TauCeti/Analysis/Sobolev/Leibniz.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Mollification/Basic.lean`](Proof/TauCeti/Analysis/Sobolev/Mollification/Basic.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Mollification/Interior.lean`](Proof/TauCeti/Analysis/Sobolev/Mollification/Interior.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Poincare/Slab.lean`](Proof/TauCeti/Analysis/Sobolev/Poincare/Slab.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean`](Proof/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean)
- [`Proof/TauCeti/Analysis/Sobolev/TestFunctionLp.lean`](Proof/TauCeti/Analysis/Sobolev/TestFunctionLp.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Translation.lean`](Proof/TauCeti/Analysis/Sobolev/Translation.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Basic.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Basic.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/ChainRule.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/ChainRule.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/CompactSupport.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/CompactSupport.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Density.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Density.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/DifferenceQuotient.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/DifferenceQuotient.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Extension.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Extension.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/LevelSet.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/LevelSet.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/MeyersSerrin.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/MeyersSerrin.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Mollification.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Mollification.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Multiplication.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Multiplication.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Restriction.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Restriction.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Translation.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Translation.lean)
- [`Proof/TauCeti/Analysis/Sobolev/W1p/Zero.lean`](Proof/TauCeti/Analysis/Sobolev/W1p/Zero.lean)
- [`Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean`](Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean)
- [`Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Limit.lean`](Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Limit.lean)
- [`Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Local.lean`](Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Local.lean)
- [`Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Translation.lean`](Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Translation.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Approximation.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Approximation.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Basic.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Basic.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Classical.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Classical.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/LocalApproximation.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/LocalApproximation.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Mollification.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Mollification.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Restriction.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Restriction.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/SecondOrder.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/SecondOrder.lean)
- [`Proof/TauCeti/Analysis/Sobolev/Wkp/Zero.lean`](Proof/TauCeti/Analysis/Sobolev/Wkp/Zero.lean)
- [`Proof/TauCeti/LinearAlgebra/Matrix/ToQuadraticForm.lean`](Proof/TauCeti/LinearAlgebra/Matrix/ToQuadraticForm.lean)
- [`Proof/TauCeti/MeasureTheory/Function/LocallyIntegrable.lean`](Proof/TauCeti/MeasureTheory/Function/LocallyIntegrable.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/BilinearForm.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/BilinearForm.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/DominatedConvergence.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/DominatedConvergence.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/ExtendByZero.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/ExtendByZero.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/L1Convergence.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/L1Convergence.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/LocalApproximateIdentity.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/LocalApproximateIdentity.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/MollificationBridge.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/MollificationBridge.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/Norm.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/Norm.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/Restriction.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/Restriction.lean)
- [`Proof/TauCeti/MeasureTheory/Function/Lp/Translation.lean`](Proof/TauCeti/MeasureTheory/Function/Lp/Translation.lean)
- [`Proof/TauCeti/MeasureTheory/Integral/Cosh.lean`](Proof/TauCeti/MeasureTheory/Integral/Cosh.lean)
- [`Proof/TauCeti/Topology/Instances/ENNReal.lean`](Proof/TauCeti/Topology/Instances/ENNReal.lean)
