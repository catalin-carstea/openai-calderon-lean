import Proof.NativeHigherScalarCombinationBound
import Proof.NativeScalarBoundedHigherData
import Proof.NativeScalarBoundedAdjointNorm
import Proof.TaylorScalarHighNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared higher mixed-adjoint commutator for two scalar-plus-bounded
packets. The additional angular/higher witnesses remain explicit and the
numeric budgets are independent of the two packet scales. -/
theorem NativeScalarBoundedHigherData.higher_adjoint_commutator
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG CK CJ BS BG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {G : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB CAug scaleA scaleB : ℝ}
    {La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {Ha0 Hb0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    {A : NativeScalarBoundedEndpointData G La Ha0 CQB CZB scaleA}
    {B : NativeScalarBoundedEndpointData G Lb Hb0 CQB CZB scaleB}
    (DA : NativeScalarBoundedHigherData A CAug) (DB : NativeScalarBoundedHigherData B CAug)
    (N : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData N ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG)
    (hΩ : IsOpen Ω) (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hCAug : 0 ≤ CAug) (hScaleA : 0 ≤ scaleA) (hScaleB : 0 ≤ scaleB) (hBS : 0 ≤ BS)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CKN : ℝ) (hCKN : 0 ≤ CKN) (hKN : ‖KN‖ ≤ CKN*(d.radius y)^2)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (BKH : ℝ) (hBKH : 0 ≤ BKH) (hKH : ‖KH‖ ≤ BKH*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (hKern : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hCPG : ((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB ≤ CP)
    (hCPR : ((‖closedThreeJetHigherScalarMultiplierL‖*BKH+BS)*CAug+CZB) ≤ CP)
    (hCPHalf : ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CKN+taylorGeneratorFixedBudget F0 ha0 CG)*CQB+CZB) ≤ CP)
    (hCPZ : CZB ≤ CP)
    (Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      La.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      La.adjoint Lb Ha Hb0 ((3*C^3*CAug^2+6*CP^2)*scaleA*scaleB) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let Qa := signedTaylorScalarCoefficients A.coefficient
  let Qb := B.coefficient
  let AQa := fun ij => signedTaylorScalarCoefficients (fun k => DA.angular k ij)
  let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Rp := A.adjointRemainderHalfL ha0 KN
  let Rn := A.adjointRemainderNegativeL ha0 KN
  let Rh := DA.adjointRemainderHigher N ha0 KH
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hAQa (a : TaylorGeneratorIndex) (i j : I) :
      closedThreeJetHalfBoundaryScalarMultiplierL (AQa (i,j) a)=closedCoefficientAngularHalfL i j (Qa a) := by
    simpa only [AQa,Qa,signedTaylorScalarCoefficients,map_smul] using
      congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => a.adjointSign • T)
        (DA.angular_half a i j)
  have hAugA : (∑ a,taylorGeneratorWeight (d.radius y) a*(‖Qa a‖+∑ ij : I × I,‖AQa ij a‖)) ≤ CAug*scaleA := by
    simpa only [Qa,AQa,norm_signedTaylorScalarCoefficients] using DA.augmented_bound
  have hGen := N.higher_scalar_combination_bound G ha0 HS HG hΩ hF0 he Qa Qb
    (fun a ij => AQa ij a) DB.angular hAQa DB.angular_half CAug scaleA scaleB hCAug hScaleA hScaleB
    hAugA DB.augmented_bound
  have hHigh (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) (scale : ℝ) (hScale : 0 ≤ scale)
      (hQ : (∑ k,taylorGeneratorWeight (d.radius y) k*‖Q k‖) ≤ CQB*scale) : ‖high Q‖ ≤ CP*scale := by
    have hGN : 0 ≤ (taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖ := by
      have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
      positivity
    calc
      _ ≤ ((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*
        (∑ k,taylorGeneratorWeight (d.radius y) k*‖Q k‖) := G.scalar_high_combination_norm ha0 Q
      _ ≤ ((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*(CQB*scale) :=
        mul_le_mul_of_nonneg_left hQ hGN
      _ = (((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB)*scale := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCPG hScale
  have hQaBound : (∑ k,taylorGeneratorWeight (d.radius y) k*‖Qa k‖) ≤ CQB*scaleA := by
    rw [show Qa=signedTaylorScalarCoefficients A.coefficient from rfl,signedTaylorScalarCoefficients_weighted_sum]
    exact A.coefficient_bound
  have hRp := (A.norm_adjoint_remainders hF0 ha0 hCQ hCI hCW hr hr1 KN CKN hCKN hKN).1.trans
    (mul_le_mul_of_nonneg_right hCPHalf hScaleA)
  have hRh := (DA.norm_adjointRemainderHigher_le N ha0 HS hBS KH BKH hBKH hKH).trans
    (mul_le_mul_of_nonneg_right hCPR hScaleA)
  have hZp := B.bounded_bounds.1.trans (mul_le_mul_of_nonneg_right hCPZ hScaleB)
  have hZh := DB.higher_bounds.1.trans (mul_le_mul_of_nonneg_right hCPZ hScaleB)
  have hFull := hGen.add_bounded_linear I1 Rp B.boundedHalf Rn B.boundedNegative Rh DB.boundedHigher
    (G.scalar_combination_balanced_pair hF0 Qa) (G.scalar_combination_balanced_pair hF0 Qb)
    (A.adjoint_remainder_compatible hF0 ha0 hFlat KN hP) B.bounded_pair
    (DA.adjointRemainderHigher_compatible N ha0 HS KH KN hKern) DB.boundedHigher_pair
    CP scaleA scaleB 1 hCP hScaleA hScaleB zero_le_one (norm_sphereSobolevInclusionL_le _ _ _)
    (by simpa only [mul_one] using hHigh Qa scaleA hScaleA hQaBound)
    (by simpa only [mul_one] using hHigh Qb scaleB hScaleB B.coefficient_bound)
    (by simpa only [mul_one] using hRh) (by simpa only [mul_one] using hZh)
    (by simpa only [mul_one] using hRp) (by simpa only [mul_one] using hZp)
  have hFull' := hFull.mono (le_of_eq (by ring :
    (3*C^3*CAug^2)*scaleA*scaleB+6*CP^2*scaleA*scaleB*1^2=
      (3*C^3*CAug^2+6*CP^2)*scaleA*scaleB))
  have hLa := A.adjoint_normal_form hF0 ha0 hFlat KN hP
  have hHA := A.adjoint_balanced_pair hF0 ha0 hFlat KN hP
  have hHAeq : Ha=high Qa+Rp.comp I1 := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    exact DFunLike.congr_fun (hHa.trans hHA.symm) u
  exact hFull'.congr hLa.symm B.low_form.symm hHAeq.symm B.high_form.symm
end ShrinkingSpheres
