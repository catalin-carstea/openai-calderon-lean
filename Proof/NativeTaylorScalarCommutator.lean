import Proof.NativeClosedMultiplierSmoothIdentity
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.NativeRelativeTrueAdjointDomain
import Proof.MidpointRadialMultiplierGain
import Proof.AdjointMultiplierGainGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
def NormalFrameRelativeCoefficientJetFamily.scalarMultiplierKernel
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C)
    (F0 : SmoothCoefficientMatrix 2) (Q : ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
    q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p Q

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}

lemma forwardTaylor_scalar_commutator_graph
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (Q : SmoothCoefficientJets 3)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((q.scalarMultiplierKernel F0 (smoothCoefficientClosureInclusionL 3 Q) p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
    (t.forwardTaylor p).comp (oneBoundaryCoefficientMulL
      (smoothMultiplierLowerJets Q))-
      (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData
        Q))).comp (t.forwardTaylor p) := by
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported
  have hMem (x : NormalFrameRelativeParameter) : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (F x) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact commonSupportEnergyMemLp q.a q.smooth x
  have hMem1 (x : NormalFrameRelativeParameter) : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (F1 x) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact commonSupportEnergyMemLp q.a1 q.firstSmooth x
  have hMem0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun k => (contDiff_coefficientValue 2 (F0 i k)).continuous)))
      continuous_const continuous_const
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hK : q.scalarMultiplierKernel F0 (smoothCoefficientClosureInclusionL 3 Q) p =
      radialTaylorMultiplierCommutatorL (F p) F0 (F1 p) (hMem p) hMem0 (hMem1 p) Q (d.radius y) := by
    unfold NormalFrameRelativeCoefficientJetFamily.scalarMultiplierKernel
    rw [commonSupportNativeClosedMultiplierKernel_on_smooth]
    exact (congrFun (commonSupport_moving_multiplier_commutator_eq_curried_kernel q.a q.a1 q.smooth q.firstSmooth
      q.support q.support q.compact q.compact q.supported q.firstSupported F0 hFlat hMem hMem1 hMem0
      (fun _ => Q) (d.radius y)) p).symm
  have hFirst (z : X) (hz : z ∈ (ballOpens:Set X)) (i k : I) : coefficientValue 2 (F1 p i k) z =
      normalFrameRelativeFirstCovector d.γ d.g₁ p z*(1:Mat) i k := by
    change coefficientMatrixField 2 (F1 p) z i k = _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact congrArg (fun A : Mat => A i k) (q.firstScalar p (t.sub (V.sub hp)) z
      (Metric.closedBall_subset_closedBall hZ (unitBall_subset_closedBall_two hz)))
  have hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible := by
    simpa only [one_smul] using strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus
      fixedDirichletRegularity 0 ((1:ℝ) • F0) (uniformlyEllipticOn_flat_coefficientMatrix F0 1 (by norm_num) hFlat)
  have hGraph := midpoint_radial_taylor_multiplier_gain_graph (F p) F0 (F1 p) (hMem p) hMem0 (hMem1 p)
    (V.coercive p hp) hFlat (normalFrameRelativeFirstCovector d.γ d.g₁ p) hFirst (V.strong p hp) hInv0
    (t.response p) (t.highRestriction p (V.sub hp)).symm Q (d.radius y)
  have hB : coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p) =
      radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p) := by
    simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ p)
  rw [hK]
  simpa only [forwardTaylor,hB] using hGraph

lemma adjointTaylor_scalar_commutator_graph
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (Q : SmoothCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      ((t.adjointTaylor p).comp (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
      (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp (t.adjointTaylor p)) =
      (-(q.scalarMultiplierKernel F0 (smoothCoefficientClosureInclusionL 3 Q) p).adjoint).comp
        (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) :=
  adjoint_multiplier_gain_graph (t.forwardTaylor p) (t.adjointTaylor p)
    (q.scalarMultiplierKernel F0 (smoothCoefficientClosureInclusionL 3 Q) p) Q (V.taylorPair p hp)
    (t.forwardTaylor_scalar_commutator_graph V hZ F0 hF0 Q p hp)
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
