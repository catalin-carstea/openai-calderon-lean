import Proof.NativeHigherNormalExpansion
import Proof.NormalCoefficientAugmentedBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def nativeNormalAntisymmetricHigherBudget (Q : SmoothCoefficientJets 2) (CQ CR CG BS : ℝ) : ℝ :=
  let BL := linearScalarAngularNormBudget Q*CQ
  let BQ := ‖closedUnitCoefficient Q‖+BL+(1+9*CG)*CR
  let BR := (1+9*CG)*CR
  let BB := 6*radialDriftSobolevBound (-(3/2:ℝ))*CQ
  let BM := ‖closedThreeJetHigherScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  2*(BM*(BS*BL)+(BS*BQ+BS*BR+2*BB*BM))

lemma nativeNormalAntisymmetricHigherBudget_nonneg (Q : SmoothCoefficientJets 2)
    (CQ CR CG BS : ℝ) (hCQ : 0 ≤ CQ) (hCR : 0 ≤ CR) (hCG : 0 ≤ CG) (hBS : 0 ≤ BS) :
    0 ≤ nativeNormalAntisymmetricHigherBudget Q CQ CR CG BS := by
  have hL := linearScalarAngularNormBudget_nonneg Q
  have hRad : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  dsimp only [nativeNormalAntisymmetricHigherBudget]
  positivity

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ BS CR : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def actualNormalAntisymmetricHigher
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 2)
    (R : RelativeNormalScalarRemainderFamily d y CR) (p : NormalFrameRelativeParameter) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.antisymmetricTaylorHigherFromRotationData ha0 (R.normalCoefficient Q)
    (fun x => linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ x))
    (fun ij => R.normalAngularCoefficient Q ij.1 ij.2)
    (fun ij x => linearScalarClosedCoefficientL Q
      (rotationCovector (normalFrameRelativeFirstCovector d.γ d.g₁ x) ij.1 ij.2)) p

lemma actualNormalAntisymmetricHigher_half_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    {CG : ℝ} (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (R : RelativeNormalScalarRemainderFamily d y CR)
    (hPos : ((y,frameVectorLinear d.frame y),0) ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (hM : (closedThreeJetHigherScalarMultiplierL
      (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hMN : (closedThreeJetNegativeScalarMultiplierL
      (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hSkew : let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      let KN := s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))=
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let KN := s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
      (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.actualNormalAntisymmetricHigher ha0 Q R p)=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact A.antisymmetricTaylorHigherFromRotationData_half_compatible G ha0 H hF0
    (R.normalCoefficient Q)
    (fun x => linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ x))
    (fun ij => R.normalAngularCoefficient Q ij.1 ij.2)
    (fun ij x => linearScalarClosedCoefficientL Q (rotationCovector (normalFrameRelativeFirstCovector d.γ d.g₁ x) ij.1 ij.2))
    (fun i j => R.normalAngularCoefficient_half Q hQ h hK _ R.point hPos he i j)
    (fun i j => linearScalarClosedCoefficient_angular_half Q hQ _ i j) hM hMN hSkew

lemma actualNormalAntisymmetricHigher_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (R : RelativeNormalScalarRemainderFamily d y CR) (CG : ℝ)
    (hCQ : 0 ≤ CQ) (hCR : 0 ≤ CR) (hCG : 0 ≤ CG) (hBS : 0 ≤ BS)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : ‖normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0)‖ ≤ CQ)
    (hAngular : ∀ ij : I × I,‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CG*(CR*(d.radius y)^2))
    (hPos : ((y,frameVectorLinear d.frame y),0) ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (hM : (closedThreeJetHigherScalarMultiplierL
      (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hInv : ‖(closedThreeJetHigherScalarMultiplierL
      (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))).inverse‖ ≤ 2) :
    ‖A.actualNormalAntisymmetricHigher ha0 Q R ((y,frameVectorLinear d.frame y),0)‖ ≤
      nativeNormalAntisymmetricHigherBudget Q CQ CR CG BS*(d.radius y)^2 := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Qn := R.normalCoefficient Q
  let Qell := fun x => linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ x)
  let Rn := fun ij : I × I => R.normalAngularCoefficient Q ij.1 ij.2
  let Rell := fun (ij : I × I) x => linearScalarClosedCoefficientL Q
    (rotationCovector (normalFrameRelativeFirstCovector d.γ d.g₁ x) ij.1 ij.2)
  let Rr := fun ij : I × I => normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2
  let BL := linearScalarAngularNormBudget Q*CQ
  let BQ := ‖closedUnitCoefficient Q‖+BL+(1+9*CG)*CR
  let BR := (1+9*CG)*CR
  let BB := 6*radialDriftSobolevBound (-(3/2:ℝ))*CQ
  let BM := ‖closedThreeJetHigherScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  have hBM : 0 ≤ BM := by dsimp only [BM];positivity
  have hBB : 0 ≤ BB := by
    have hh : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
    dsimp only [BB];positivity
  have hB : ‖radialCorrectionAdjointSobolevL (3/2:ℝ) ell‖ ≤ BB := by
    have hh := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      (3/2:ℝ) (radialCorrectionVector ell)
    have hCoords := (radialCorrectionVector_coordinate_sum_le ell).trans
      (mul_le_mul_of_nonneg_left hEll (by norm_num : (0:ℝ) ≤ 3))
    have hRad : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
    exact hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoords (by norm_num : (0:ℝ) ≤ 2)) hRad).trans_eq (by ring))
  have hRn : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rn (i,j) p)=closedCoefficientAngularHalfL i j (Qn p) :=
    fun i j => R.normalAngularCoefficient_half Q hQ h hK p R.point hPos he i j
  have hRell : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rell (i,j) p)=closedCoefficientAngularHalfL i j (Qell p) :=
    fun i j => linearScalarClosedCoefficient_angular_half Q hQ ell i j
  have hRr : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rr (i,j) p)=closedCoefficientAngularHalfL i j (R.closed p) :=
    fun i j => R.angular_half h hK p R.point hPos he i j
  have hExpand := A.fullAdjointScalarHigherFromRotationData_normal_expansion ha0
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) Q hQ Qn Qell R.closed Rn Rell Rr p rfl hRn hRell hRr
  have hSmall := R.normalCoefficient_higher_deviation_norm_le Q hQ CQ hCR hr hr1 hEll
  have hRest := A.scalarHigherCommutatorRest_norm_le ha0 H hBS Qn R.closed Rn Rr BQ BR BB BM hr hBB
    (R.normalCoefficient_augmented_norm_le Q CQ CG hCQ hCR hCG hr hr1 hEll hAngular)
    (R.remainder_augmented_norm_le CG hAngular) hB hSmall
  have hL := (linearScalar_augmented_norm_le Q ell).trans
    (mul_le_mul_of_nonneg_left hEll (linearScalarAngularNormBudget_nonneg Q))
  have hD : ‖A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p‖ ≤ BS*BL := by
    have hh := A.higherScalarGeneratorFromRotationData_norm_le ha0 H Qell Rell .degree
    simp only [taylorGeneratorWeight,one_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hL hBS)
  have hh := A.antisymmetricTaylorHigherFromRotationData_norm_of_expansion ha0 Qn Qell Rn Rell p 2 BM
    (BS*BQ+BS*BR+2*BB*BM) hM hr (by norm_num) hInv hSmall
    (A.scalarHigherCommutatorRest ha0 Qn R.closed Rn Rr p) hExpand hRest
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hD hBM) le_rfl) (by norm_num : (0:ℝ) ≤ 2))
    (sq_nonneg _)).trans_eq (by dsimp only [nativeNormalAntisymmetricHigherBudget,BL,BQ,BR,BB,BM]))
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
