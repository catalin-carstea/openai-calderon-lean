import Proof.PoissonSmoothMultiplierIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

def halfRadialMultiplierCommutatorL (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fixedHalfOutwardTraceL.comp (strongPoissonMultiplierDefectL F ha Q)+
    nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace Q

/-- A genuine order-zero boundary commutator: the bounded half-order map
agrees with the actual high radial Dirichlet response commutator. -/
theorem halfRadialMultiplierCommutatorL_high (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    halfRadialMultiplierCommutatorL F ha Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      fixedHalfOutwardTraceL (strongPoissonL F (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q f))-
      nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        fixedUnitBallValueTrace (smoothMultiplierLowerJets Q) (fixedHalfOutwardTraceL (strongPoissonL F f)) := by
  let P := strongPoissonL F
  let V := strongPoissonMultiplierDefectL F ha Q
  let O := fixedHalfOutwardTraceL
  let I0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let M1 := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let Nq := nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  have hBulk : P (M3 f)-coefficientMultiplier fixedSobolevCalculus 2 Q (P f) = V (I0 f) :=
    strongPoisson_smooth_multiplier_difference F ha hc hInv Q f
  have hTrace : fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (P f)) = I0 f := fixedHalfValueTrace_strongPoisson F f
  have hProduct : O (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = M1 (O (P f))+Nq (I0 f) := by
    have h := nativeHalfOutwardTraceL_smooth_multiplier fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace Q (P f)
    change O (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = M1 (O (P f))+
      Nq (fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (P f))) at h
    exact h.trans (congrArg (fun u => M1 (O (P f))+Nq u) hTrace)
  have hOut : O (P (M3 f))-O (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = O (V (I0 f)) :=
    (O.map_sub _ _).symm.trans (congrArg O hBulk)
  change O (V (I0 f))+Nq (I0 f) = O (P (M3 f))-M1 (O (P f))
  rw [← hOut,hProduct]
  abel

/-- The gained boundary commutator has the explicit native inverse,
forcing, weak Poisson and normal-derivative multiplier norm budget. -/
theorem norm_halfRadialMultiplierCommutatorL_le (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    ‖halfRadialMultiplierCommutatorL F ha Q‖ ≤
      ‖fixedHalfOutwardTraceL‖*‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
      ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖*
      ‖nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner‖+
      ‖nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q‖ := by
  let Nq := nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  calc
    _ ≤ ‖fixedHalfOutwardTraceL.comp (strongPoissonMultiplierDefectL F ha Q)‖+‖Nq‖ := norm_add_le _ _
    _ ≤ ‖fixedHalfOutwardTraceL‖*‖strongPoissonMultiplierDefectL F ha Q‖+‖Nq‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl
    _ ≤ ‖fixedHalfOutwardTraceL‖*(‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
        ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖*
        ‖nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner‖)+‖Nq‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_strongPoissonMultiplierDefectL_le F ha Q)
        (norm_nonneg fixedHalfOutwardTraceL)) (le_rfl : ‖Nq‖ ≤ ‖Nq‖)
    _ = _ := by ring

end ShrinkingSpheres
