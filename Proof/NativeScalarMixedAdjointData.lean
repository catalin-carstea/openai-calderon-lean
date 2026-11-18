import Proof.NativeHigherAdjointCommonBudget
import Proof.GradedBalancedCommutatorBound
import Proof.NativeScalarBoundedAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Common low/high mixed-adjoint commutator budget, before either scale. -/
def nativeScalarMixedAdjointBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CKN BKH BS BG CQ CI CW CQB CZB CAug : ℝ) : ℝ :=
  let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CKN CQ CI CW CQB CZB
  let C1 := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let CH := nativeHigherAdjointCommonBudget F0 ha0 CG CKN BKH BS CQB CZB CAug
  (3*C0^3*CQB^2+6*CP^2)+(3*C1^3*CAug^2+6*CH^2)

lemma nativeScalarMixedAdjointBudget_nonneg (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CKN BKH BS BG CQ CI CW CQB CZB CAug : ℝ) :
    0 ≤ nativeScalarMixedAdjointBudget F0 ha0 CG CKN BKH BS BG CQ CI CW CQB CZB CAug := by
  have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  unfold nativeScalarMixedAdjointBudget
  positivity

/-- Closed mixed-adjoint point data for ANY two packets with their genuine
angular and bounded-higher witnesses. The resulting low/high commutator
maps commute with the actual inclusion and preserve separate scales. -/
theorem NativeScalarBoundedHigherData.mixed_adjoint_data
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
    (hCQB0 : 0 ≤ CQB) (hCAug : 0 ≤ CAug) (hScaleA : 0 ≤ scaleA) (hScaleB : 0 ≤ scaleB) (hBS : 0 ≤ BS)
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
    (Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      La.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    Nonempty (GradedBalancedCommutatorBound
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      La.adjoint Lb Ha Hb0
      (nativeScalarMixedAdjointBudget F0 ha0 CG CKN BKH BS BG CQ CI CW CQB CZB CAug*scaleA*scaleB)) := by
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CKN CQ CI CW CQB CZB
  let C1 := CB+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let CH := nativeHigherAdjointCommonBudget F0 ha0 CG CKN BKH BS CQB CZB CAug
  let BL := 3*C0^3*CQB^2+6*CP^2
  let BH := 3*C1^3*CAug^2+6*CH^2
  have hCB : 1 ≤ CB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hBL : 0 ≤ BL := by dsimp only [BL,C0];positivity
  have hBH : 0 ≤ BH := by dsimp only [BH,C1];positivity
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  obtain ⟨hCH1,hCHG,hCHR,hCHHalf,hCHZ⟩ :=
    nativeHigherAdjointCommonBudget_bounds F0 ha0 CG CKN BKH BS CQB CZB CAug
  have hLow := A.adjoint_commutator B hCQB0 hScaleA hScaleB hF0 he ha0 hFlat hCQ hCI hCW
    hr hr1 KN CKN hCKN hKN hP Ha hHa
  have hHigh := DA.higher_adjoint_commutator DB N ha0 HS HG hΩ hF0 he hCQ hCI hCW hr hr1
    hCAug hScaleA hScaleB hBS KN CKN hCKN hKN KH BKH hBKH hKH hP hKern
    CH (zero_le_one.trans hCH1) hCHG hCHR hCHHalf hCHZ Ha hHa
  apply gradedBalancedCommutatorBound_of_low_high hLow hHigh
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hBH) hScaleA) hScaleB
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hBL) hScaleA) hScaleB
end ShrinkingSpheres
