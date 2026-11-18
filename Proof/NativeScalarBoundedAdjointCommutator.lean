import Proof.NativeScalarBoundedAdjointNorm
import Proof.TaylorScalarCoefficientCombinationBound
import Proof.GradedLinearRemainderCommutator
import Proof.TaylorScalarLowNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared mixed adjoint commutator of two scalar-plus-bounded operator packets.
The packets use one native generator family and retain SEPARATE scales.
This common estimate serves full/full and leading/full coefficient callers. -/
theorem NativeScalarBoundedEndpointData.adjoint_commutator
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scaleA scaleB : ℝ}
    {La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {Ha0 Hb0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    (A : NativeScalarBoundedEndpointData T La Ha0 CQB CZB scaleA)
    (B : NativeScalarBoundedEndpointData T Lb Hb0 CQB CZB scaleB)
    (hCQB : 0 ≤ CQB) (hScaleA : 0 ≤ scaleA) (hScaleB : 0 ≤ scaleB)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (La).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CK CQ CI CW CQB CZB
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (La).adjoint (Lb) Ha (Hb0)
      ((3*C0^3*CQB^2+6*CP^2)*scaleA*scaleB) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CK CQ CI CW CQB CZB
  let Qa := signedTaylorScalarCoefficients (A.coefficient)
  let Qb := B.coefficient
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ a,(taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp (closedThreeJetHigherScalarMultiplierL (Q a))
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Rp := A.adjointRemainderHalfL ha0 KN
  let Rn := A.adjointRemainderNegativeL ha0 KN
  let Zp := B.boundedHalf
  let Zn := B.boundedNegative
  obtain ⟨hCP1,hLC,hRPC,hRNC,hZC⟩ := nativeScalarBoundedAdjointBudget_bounds F0 ha0 CG CK CQ CI CW CQB CZB
  have hCP : 0 ≤ CP := zero_le_one.trans hCP1
  have hCB : 0 ≤ CB := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hC0 : 0 ≤ C0 := add_nonneg hCB (norm_nonneg _)
  have hQa : (∑ a,taylorGeneratorWeight (d.radius y) a*‖Qa a‖) ≤ CQB*scaleA := by
    rw [show Qa=signedTaylorScalarCoefficients (A.coefficient) from rfl,signedTaylorScalarCoefficients_weighted_sum]
    exact A.coefficient_bound
  have hQb := B.coefficient_bound
  have hLow (scale : ℝ) (hScale : 0 ≤ scale) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
      (hQ : (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) ≤ CQB*scale) : ‖low Q‖ ≤ CP*scale := by
    calc
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) := T.scalar_low_combination_norm ha0 Q
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(CQB*scale) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hCB (norm_nonneg _))
      _ = (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB)*scale := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLC hScale
  have hR := A.norm_adjoint_remainders hF0 ha0 hCQ hCI hCW hr hr1 KN CK hCK hKN
  have hRp : ‖Rp‖ ≤ CP*scaleA := hR.1.trans (mul_le_mul_of_nonneg_right hRPC hScaleA)
  have hRn : ‖Rn‖ ≤ CP*scaleA := hR.2.trans (mul_le_mul_of_nonneg_right hRNC hScaleA)
  have hZp : ‖Zp‖ ≤ CP*scaleB := (B.bounded_bounds).1.trans (mul_le_mul_of_nonneg_right hZC hScaleB)
  have hZn : ‖Zn‖ ≤ CP*scaleB := (B.bounded_bounds).2.trans (mul_le_mul_of_nonneg_right hZC hScaleB)
  have hSource := T.scalar_combination_commutes hF0 he ha0 hFlat s.point.flatStrong Qa Qb
  have hQb0 : 0 ≤ ∑ a,taylorGeneratorWeight (d.radius y) a*‖Qb a‖ :=
    taylor_scalar_weighted_sum_nonneg _ _
  have hPair := mul_le_mul hQa hQb hQb0 (mul_nonneg hCQB hScaleA)
  have hGen := (hSource.mono (show
      3*C0^3*(∑ a,taylorGeneratorWeight (d.radius y) a*‖Qa a‖)*(∑ a,taylorGeneratorWeight (d.radius y) a*‖Qb a‖) ≤
      (3*C0^3*CQB^2)*scaleA*scaleB from by
    calc
      _ = 3*C0^3*((∑ a,taylorGeneratorWeight (d.radius y) a*‖Qa a‖)*(∑ a,taylorGeneratorWeight (d.radius y) a*‖Qb a‖)) := by ring
      _ ≤ 3*C0^3*((CQB*scaleA)*(CQB*scaleB)) := mul_le_mul_of_nonneg_left hPair (by positivity)
      _ = _ := by ring)).graded_bound
  have hFull := hGen.add_bounded_linear I0 Rp Zp Rn Zn
    (T.scalar_combination_balanced_pair hF0 Qa) (T.scalar_combination_balanced_pair hF0 Qb)
    CP scaleA scaleB 1 hCP hScaleA hScaleB zero_le_one (norm_sphereSobolevInclusionL_le _ _ _)
    (by simpa only [mul_one] using hLow scaleA hScaleA Qa hQa) (by simpa only [mul_one] using hLow scaleB hScaleB Qb hQb)
    (by simpa only [mul_one] using hRp) (by simpa only [mul_one] using hZp)
    (by simpa only [mul_one] using hRn) (by simpa only [mul_one] using hZn)
  have hFull' := hFull.mono (le_of_eq (by ring :
    (3*C0^3*CQB^2)*scaleA*scaleB+6*CP^2*scaleA*scaleB*1^2=(3*C0^3*CQB^2+6*CP^2)*scaleA*scaleB))
  have hLa := A.adjoint_normal_form hF0 ha0 hFlat KN hP
  have hHA := A.adjoint_balanced_pair hF0 ha0 hFlat KN hP
  have hHAeq : Ha=high Qa+Rp.comp I1 := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    exact DFunLike.congr_fun (hHa.trans hHA.symm) u
  exact hFull'.congr hLa.symm (B.low_form).symm hHAeq.symm (B.high_form).symm
end ShrinkingSpheres
