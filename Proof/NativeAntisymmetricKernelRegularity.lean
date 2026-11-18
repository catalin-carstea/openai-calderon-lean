import Proof.NativeAntisymmetricTaylorGraph
import Proof.NativeClosedMovingMultiplierSmoothness
import Proof.CompletedNormalCoefficientFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance antiRegularityCompleteNegative : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace
lemma NativeRelativeHorizontalTaylorData.contDiffOn_antisymmetricTaylorKernel
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CR : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (R : RelativeNormalScalarRemainderFamily d y CR) (Q : SmoothCoefficientJets 2)
    (V : s.response.SymmetricAdjointDomain) (W : Set NormalFrameRelativeParameter)
    (hWV : W ⊆ V.domain)
    (hInv : ∀ p ∈ W,(closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
      (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p) W := by
  intro p hp
  have hEll := s.coefficients.covectorSmooth.contDiffAt
    (s.coefficients.domainOpen.mem_nhds (s.response.sub (V.sub (hWV hp))))
  have hScalarR := (contDiff_commonSupportClosedCoefficientFamily 3 R.scalar R.smooth R.support R.compact R.supported).contDiffAt (x:=p)
  have hLinear := (linearScalarClosedCoefficientL Q).contDiff.contDiffAt.comp p hEll
  have hQn : ContDiffAt ℝ ∞ (R.normalCoefficient Q) p :=
    (contDiffAt_const.add (hLinear.const_smul (d.radius y))).add hScalarR
  have hM := closedThreeJetNegativeScalarMultiplierL.contDiff.contDiffAt.comp p hQn
  have hMI := (hInv p hp).contDiffAt_map_inverse.comp p hM
  have hWeak : (commonSupportZeroWeakEnergy s.coefficients.a s.coefficients.smooth p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (V.coercive p (hWV hp))
  have hK : ContDiffAt ℝ ∞ (fun p => s.coefficients.scalarMultiplierKernel F0 (R.normalCoefficient Q p) p) p :=
    contDiffAt_commonSupportNativeClosedMovingMultiplierKernel s.coefficients.a s.coefficients.a1
      s.coefficients.smooth s.coefficients.firstSmooth s.coefficients.support s.coefficients.support
      s.coefficients.compact s.coefficients.compact s.coefficients.supported s.coefficients.firstSupported
      F0 (d.radius y) p (V.strong p (hWV hp)) hWeak (R.normalCoefficient Q) hQn
  let Adj := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) ≃ₗᵢ[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap
  have hKa := Adj.contDiff.contDiffAt.comp p hK
  have hDegree := (closedNegativeDegreeScalarCommutatorL F0 ha0).contDiff.contDiffAt.comp p hQn
  have hB := radialCorrectionNegativeAdjointMapL.contDiff.contDiffAt.comp p hEll
  have hComm : ContDiffAt ℝ ∞
      (fun p => s.response.fullAdjointScalarCommutator F0 ha0 (R.normalCoefficient Q p) p) p :=
    (hKa.neg.add hDegree).add (((hB.clm_comp hM).sub (hM.clm_comp hB)).const_smul (d.radius y))
  have hFirst := (closedNegativeDegreeScalarCommutatorL F0 ha0).contDiff.contDiffAt.comp p hLinear
  exact (((hMI.clm_comp hComm).neg).add (hFirst.const_smul (d.radius y))).contDiffWithinAt
end ShrinkingSpheres
