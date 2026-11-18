import Proof.NativeTaylorGeneratorCoarseEndpoints
import Proof.RadialScalarBoundedEndpoints
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME higher scalar commutator and genuine balanced pair determine
the negative-output scalar commutator by density; the kernel keeps Hhalf. -/
lemma balanced_low_scalar_commutator
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (Q : ClosedCoefficientJets 3)
    (hPair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi=
      Lo.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hHigh : Hi.comp (closedThreeJetHigherScalarMultiplierL Q)-(closedThreeJetHalfBoundaryScalarMultiplierL Q).comp Hi=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    Lo.comp (closedThreeJetHalfBoundaryScalarMultiplierL Q)-(closedThreeJetNegativeScalarMultiplierL Q).comp Lo=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp C := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hP (v : SphereSobolev (3/2:ℝ)) : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (Hi v)=
      Lo (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) := DFunLike.congr_fun hPair v
  have hC := congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) (DFunLike.congr_fun hHigh u)
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub,closedThreeJet_half_negative_scalar_multiplier] at hC
  change Lo (closedThreeJetHalfBoundaryScalarMultiplierL Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))-
    closedThreeJetNegativeScalarMultiplierL Q (Lo (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=_
  rw [← closedThreeJet_higher_scalar_multiplier_half,← hP (closedThreeJetHigherScalarMultiplierL Q u),← hP u]
  exact hC

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
lemma generator_low_scalar_commutator (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (a : TaylorGeneratorIndex) (Q : ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp (closedThreeJetHalfBoundaryScalarMultiplierL Q)-
      (closedThreeJetNegativeScalarMultiplierL Q).comp (taylorGeneratorLow (s.response.adjointHalfTaylor p) a)=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (taylorGeneratorScalarCommutator A.scalar F0 ha0 a Q) :=
  balanced_low_scalar_commutator _ _ _ Q
    (balanced_endpoint_pair_of_coarse _ _ _ (A.generator_coarse_endpoints hF0 a).1 (A.generator_coarse_endpoints hF0 a).2)
    (A.scalar_commutator_graph ha0 hFlat hInv0 a Q)
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
