import Proof.NativeHigherAntisymmetricKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def scalarHigherCommutatorRest
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q Qr : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rr : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.higherScalarGeneratorFromRotationData ha0 .taylor Q R p+
    A.higherScalarGeneratorFromRotationData ha0 .degree Qr Rr p+
    d.radius y • ((radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (closedThreeJetHigherScalarMultiplierL (Q p)-ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)))-
    (closedThreeJetHigherScalarMultiplierL (Q p)-ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))).comp
      (radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p)))

lemma fullAdjointScalarHigherFromRotationData_normal_expansion
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (Q Qell Qr : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rell Rr : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter)
    (hQ : Q p=closedUnitCoefficient Q0+d.radius y • Qell p+Qr p)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) p)=closedCoefficientAngularHalfL i j (Q p))
    (hRell : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rell (i,j) p)=closedCoefficientAngularHalfL i j (Qell p))
    (hRr : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rr (i,j) p)=closedCoefficientAngularHalfL i j (Qr p)) :
    A.fullAdjointScalarHigherFromRotationData ha0 Q R p=
      d.radius y • A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p+
        A.scalarHigherCommutatorRest ha0 Q Qr R Rr p := by
  have hD := closedHigherDegreeScalarFromRotationData_unit_add_smul F0 ha0 hFlat s.point.flatStrong
    Q0 hQ0 (Q p) (Qell p) (Qr p) (fun ij => R ij p) (fun ij => Rell ij p) (fun ij => Rr ij p)
      (d.radius y) hQ hR hRell hRr
  have hEq := scalar_expansion_algebra
    (-A.higherScalarGeneratorFromRotationData ha0 .taylor Q R p)
    (A.higherScalarGeneratorFromRotationData ha0 .degree Q R p)
    (A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p)
    (A.higherScalarGeneratorFromRotationData ha0 .degree Qr Rr p)
    (radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p))
    (closedThreeJetHigherScalarMultiplierL (Q p)) (d.radius y) hD
  simpa only [neg_neg,fullAdjointScalarHigherFromRotationData,scalarHigherCommutatorRest] using hEq

lemma scalarHigherCommutatorRest_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hBS : 0 ≤ BS)
    (Q Qr : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rr : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (BQ BR BB BM : ℝ) (hr : 0 ≤ d.radius y) (hBB : 0 ≤ BB)
    (hQ : ‖Q ((y,frameVectorLinear d.frame y),0)‖+
      ∑ ij : I × I,‖R ij ((y,frameVectorLinear d.frame y),0)‖ ≤ BQ)
    (hR : ‖Qr ((y,frameVectorLinear d.frame y),0)‖+
      ∑ ij : I × I,‖Rr ij ((y,frameVectorLinear d.frame y),0)‖ ≤ BR*(d.radius y)^2)
    (hB : ‖radialCorrectionAdjointSobolevL (3/2:ℝ)
      (normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0))‖ ≤ BB)
    (hM : ‖closedThreeJetHigherScalarMultiplierL (Q ((y,frameVectorLinear d.frame y),0))-
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))‖ ≤ BM*d.radius y) :
    ‖A.scalarHigherCommutatorRest ha0 Q Qr R Rr ((y,frameVectorLinear d.frame y),0)‖ ≤
      (BS*BQ+BS*BR+2*BB*BM)*(d.radius y)^2 := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let T := A.higherScalarGeneratorFromRotationData ha0 .taylor Q R p
  let D := A.higherScalarGeneratorFromRotationData ha0 .degree Qr Rr p
  let B := radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p)
  let M := closedThreeJetHigherScalarMultiplierL (Q p)-ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))
  have hT : ‖T‖ ≤ BS*BQ*(d.radius y)^2 := by
    have hh := A.higherScalarGeneratorFromRotationData_norm_le ha0 H Q R .taylor
    dsimp only [taylorGeneratorWeight] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (sq_nonneg _)) hBS).trans_eq (by ring))
  have hD : ‖D‖ ≤ BS*BR*(d.radius y)^2 := by
    have hh := A.higherScalarGeneratorFromRotationData_norm_le ha0 H Qr Rr .degree
    simp only [taylorGeneratorWeight,one_mul] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hR hBS).trans_eq (by ring))
  have hComm : ‖B.comp M-M.comp B‖ ≤ 2*BB*BM*d.radius y := by
    have hOne : ‖B.comp M‖ ≤ BB*(BM*d.radius y) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hB hM (norm_nonneg _) hBB)
    have hTwo : ‖M.comp B‖ ≤ BB*(BM*d.radius y) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hM hB (norm_nonneg _) (by nlinarith only [norm_nonneg M,hM])).trans_eq (mul_comm _ _))
    exact (norm_sub_le _ _).trans ((add_le_add hOne hTwo).trans_eq (by ring))
  have hScaled : ‖d.radius y • (B.comp M-M.comp B)‖ ≤ 2*BB*BM*(d.radius y)^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hComm hr).trans_eq (by ring)
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le T D).trans (add_le_add hT hD)) hScaled)).trans_eq (by ring)
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
