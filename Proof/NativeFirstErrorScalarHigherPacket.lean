import Proof.NativeScalarBoundedHigherData
import Proof.NativeFirstErrorScalarEndpoints
import Proof.NativeFirstErrorRadialBounds
import Proof.NativeFirstErrorRadialHigherBounds
import Proof.ActualFirstErrorAngularCoefficients
import Proof.CompatibleEndpointUniqueness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def firstErrorScalarPacketBudget (Q0 : SmoothCoefficientJets 2) (K M0 CC : ℝ) : ℝ :=
  firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)

def firstErrorScalarPacketBoundedBudget (Q0 : SmoothCoefficientJets 2) (CQ K M0 CC : ℝ) : ℝ :=
  |radialScalarEndpointBudget CQ*firstErrorScalarPacketBudget Q0 K M0 CC|+
    |radialScalarHigherCommonBudget*CQ*firstErrorScalarPacketBudget Q0 K M0 CC|

lemma firstErrorScalarPacketBoundedBudget_bounds (Q0 : SmoothCoefficientJets 2) (CQ K M0 CC : ℝ) :
    0 ≤ firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC ∧
    radialScalarEndpointBudget CQ*firstErrorScalarPacketBudget Q0 K M0 CC ≤
      firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC ∧
    radialScalarHigherCommonBudget*CQ*firstErrorScalarPacketBudget Q0 K M0 CC ≤
      firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC := by
  unfold firstErrorScalarPacketBoundedBudget
  exact ⟨add_nonneg (abs_nonneg _) (abs_nonneg _),
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)),
    (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))⟩

/-- Both genuinely compatible endpoints and every angular/higher witness
of the SAME actual native first-error packet, with one shared scale. -/
structure NativeFirstErrorScalarHigherPacket
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (T : NativeTaylorGeneratorBounds s h hK CG)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q0 : SmoothCoefficientJets 2) (M0 CC CR scale : ℝ) where
  base : NativeScalarBoundedEndpointData T L H
    (firstErrorScalarPacketBudget Q0 K M0 CC) (firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC) scale
  higher : NativeScalarBoundedHigherData base (firstErrorScalarAngularCommonBudget Q0 K M0 CC CR)

lemma NativeTaylorGeneratorBounds.first_error_scalar_higher_packet
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (T : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hAngular : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (s.firstAdjointErrorFamily C ((y,frameVectorLinear d.frame y),0))=
        L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hH : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
      (s.firstAdjointErrorFamily C ((y,frameVectorLinear d.frame y),0)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    Nonempty (NativeFirstErrorScalarHigherPacket T L H Q0 (M 0) CC CR (‖a‖*d.radius y)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 C
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let V := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
  let C1 := firstErrorScalarPacketBudget Q0 K (M 0) CC
  let CZ := firstErrorScalarPacketBoundedBudget Q0 CQ K (M 0) CC
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hScale : 0 ≤ ‖a‖*d.radius y := mul_nonneg (norm_nonneg _) hr.le
  have hForms := s.first_error_scalar_endpoint_realization T C hF0 Q0 hQ0 hr
  have hLowEq : L=s.firstAdjointHalfErrorFamily C p :=
    half_endpoint_unique_of_coarse _ _ _ hL
      (s.firstAdjointHalfErrorFamily_coarse_compatible C T.domain hF0 p T.domain.pointMem)
  have hLF := hLowEq.trans hForms.1
  have hHF := higher_endpoint_unique_of_coarse _ _ _ hH hForms.2
  have hZBounds := firstErrorScalarPacketBoundedBudget_bounds Q0 CQ K (M 0) CC
  have hRadial := s.first_error_radial_endpoint_linear_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC a C
  have hRadialHigher := s.first_error_radial_higher_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC a C
  have hEndHalf : ‖radialScalarBoundedHalfL ell V‖ ≤
      (radialScalarEndpointBudget CQ*C1)*(‖a‖*d.radius y) := by
    simpa only [C1,firstErrorScalarPacketBudget,mul_assoc] using hRadial.1
  have hEndNegative : ‖radialScalarBoundedNegativeL ell V‖ ≤
      (radialScalarEndpointBudget CQ*C1)*(‖a‖*d.radius y) := by
    simpa only [C1,firstErrorScalarPacketBudget,mul_assoc] using hRadial.2
  have hHighForward : ‖radialScalarBoundedHigherL ell V‖ ≤
      (radialScalarHigherCommonBudget*CQ*C1)*(‖a‖*d.radius y) := by
    simpa only [C1,firstErrorScalarPacketBudget,mul_assoc] using hRadialHigher.1
  have hHighAdjoint : ‖radialScalarBoundedAdjointHigherL ell V‖ ≤
      (radialScalarHigherCommonBudget*CQ*C1)*(‖a‖*d.radius y) := by
    simpa only [C1,firstErrorScalarPacketBudget,mul_assoc] using hRadialHigher.2
  let B : NativeScalarBoundedEndpointData T L H C1 CZ (‖a‖*d.radius y) := {
    coefficient := Q
    boundedHalf := radialScalarBoundedHalfL ell V
    boundedNegative := radialScalarBoundedNegativeL ell V
    low_form := hLF
    high_form := hHF
    bounded_pair := radialScalarBounded_half_negative_compatible ell V
    coefficient_bound := by
      simpa only [Q,C1,actualFirstErrorGeneratorCoefficients,firstErrorScalarPacketBudget,mul_assoc] using hd.first_error_scalar_coefficient_bound
        hK1 hf hε hε1 hy hr1 Q0 hCC a C
    bounded_bounds := by
      constructor
      · exact hEndHalf.trans (mul_le_mul_of_nonneg_right hZBounds.2.1 hScale)
      · exact hEndNegative.trans (mul_le_mul_of_nonneg_right hZBounds.2.1 hScale) }
  have hHigher : NativeScalarBoundedHigherData B (firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR) := by
    refine { angular := fun b ij => actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b
             angular_half := ?_
             augmented_bound := ?_
             boundedHigher := radialScalarBoundedHigherL ell V
             boundedAdjointHigher := radialScalarBoundedAdjointHigherL ell V
             boundedHigher_pair := radialScalarBoundedHigherL_compatible ell V
             boundedAdjointHigher_pair := radialScalarBoundedAdjointHigherL_compatible ell V
             higher_bounds := ?_ }
    · intro b i j
      apply actualFirstErrorAngularCoefficients_half Q0 hQ0 C
      intro i j
      simpa only [frameVectorLinear_apply,frameVector_axis] using
        hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
    · simpa only [mul_assoc] using hd.first_error_augmented_coefficient_bound
        hK1 hf hε hε1 hy hr1 Q0 hCC a C CR hCR hAngular
    · constructor
      · exact hHighForward.trans (mul_le_mul_of_nonneg_right hZBounds.2.2 hScale)
      · exact hHighAdjoint.trans (mul_le_mul_of_nonneg_right hZBounds.2.2 hScale)
  exact ⟨{base := B,higher := hHigher}⟩
end ShrinkingSpheres
