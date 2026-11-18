import Proof.NativeScalarBoundedEndpointData
import Proof.FlatRaisingRightScalarForm
import Proof.TaylorScalarCoefficientCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The leading flat raising coefficient as a SAME-generator scalar packet.
Its scale is one and its bounded remainders vanish at both endpoints. -/
def NativeTaylorGeneratorBounds.flat_raising_scalar_packet
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (T : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    NativeScalarBoundedEndpointData T (flatHalfRaisingL i) (flatThreeHalfRaisingL i)
      (4*firstErrorScalarFixedBudget Q0) 0 1 := by
  have hF := T.flat_raising_scalar_endpoints hF0 Q0 hQ0 i
  refine {
    coefficient := flatRaisingScalarCoefficients Q0 i
    boundedHalf := 0
    boundedNegative := 0
    low_form := ?_
    high_form := ?_
    bounded_pair := ?_
    coefficient_bound := ?_
    bounded_bounds := ?_ }
  · simpa only [rightScalarCombinationL_apply,ContinuousLinearMap.zero_comp,add_zero] using hF.1.symm
  · simpa only [rightScalarCombinationL_apply,ContinuousLinearMap.zero_comp,add_zero] using hF.2.symm
  · simp only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · simpa only [mul_one] using flatRaisingScalarCoefficients_weighted_bound Q0 i (d.radius y)
  · simp only [norm_zero,zero_mul,le_refl,and_self]
end ShrinkingSpheres
