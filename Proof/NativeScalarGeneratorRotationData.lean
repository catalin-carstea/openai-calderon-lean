import Proof.FixedHigherScalarJets
import Proof.NativeScalarHigherIdentification
import Proof.ScalarRotationDataHigherJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def higherScalarGeneratorFromRotationData (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (a : TaylorGeneratorIndex) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  match a with
  | .taylor => A.scalarHigherFamilyFromRotationData Q R p
  | .degree => closedHigherDegreeScalarFromRotationData F0 ha0 (Q p) (fun ij => R ij p)
  | .rotation i j => closedThreeJetHigherScalarMultiplierL (R (i,j) p)

lemma higherScalarGeneratorFromRotationData_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (a : TaylorGeneratorIndex) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.higherScalarGeneratorFromRotationData ha0 a Q R p)=
    (taylorGeneratorScalarCommutator G.scalar F0 ha0 a (Q p)).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  cases a with
  | taylor => exact A.scalarHigherFamilyFromRotationData_selected_compatible G hΩ hF0 he Q R hR
  | degree =>
    simpa only [higherScalarGeneratorFromRotationData,taylorGeneratorScalarCommutator] using
      closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0
        (Q ((y,frameVectorLinear d.frame y),0))
        (fun ij => R ij ((y,frameVectorLinear d.frame y),0)) hR
  | rotation i j =>
    dsimp only [higherScalarGeneratorFromRotationData,taylorGeneratorScalarCommutator]
    apply ContinuousLinearMap.ext
    intro u
    change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (closedThreeJetHigherScalarMultiplierL (R (i,j) _) u)=_
    rw [closedThreeJet_higher_scalar_multiplier_half,hR i j]
    rfl

lemma higherScalarGeneratorFromRotationData_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (a : TaylorGeneratorIndex) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    (Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q p))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q p)).comp (Gh a)=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.higherScalarGeneratorFromRotationData ha0 a Q R p) :=
  (G.scalar_commutator_graph ha0 hFlat hInv0 a _).trans
    (A.higherScalarGeneratorFromRotationData_compatible G hΩ hF0 he ha0 hFlat hInv0 a Q R hR).symm

lemma higherScalarGeneratorFromRotationData_jets
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hCJ : 0 ≤ CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (CG : ℝ) (hCG : 0 ≤ CG)
    (hAngular : ∀ i j,SmoothFiniteJetBound
      (normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j)
      ((y,frameVectorLinear d.frame y),0) 2 (CG*(CJ*(d.radius y)^2)))
    (B : ℝ)
    (hTB : (19+9*Real.sqrt 2)*4*CJ*(1+CG) ≤ B)
    (hDB : (19+9*Real.sqrt 2)*‖closedHalfRadialScalarCommutatorL F0 ha0‖ ≤ B)
    (hRB : ‖closedThreeJetHigherScalarMultiplierL‖ ≤ B)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3) (BQ BR : ℝ)
    (hQ : SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 2 BQ)
    (hR : ∀ ij,SmoothFiniteJetBound (R ij) ((y,frameVectorLinear d.frame y),0) 2 BR)
    (a : TaylorGeneratorIndex) :
    SmoothFiniteJetBound (A.higherScalarGeneratorFromRotationData ha0 a Q R)
      ((y,frameVectorLinear d.frame y),0) 2 (B*(taylorGeneratorWeight (d.radius y) a*(BQ+BR))) := by
  have hBR : 0 ≤ BR := (hR (0,0)).nonneg
  have hQB : 0 ≤ BQ+BR := add_nonneg hQ.nonneg hBR
  cases a with
  | taylor =>
    have hh := A.scalarHigherFamilyFromRotationData_two_jets hCJ Q R BQ BR hQ hR CG hCG hAngular
    apply hh.weaken
    have hC : 0 ≤ (19+9*Real.sqrt 2)*4*CJ := by positivity
    have hCoeff : (19+9*Real.sqrt 2)*(4*CJ*((1+CG)*BQ+BR)) ≤ B*(BQ+BR) := by
      calc
        _ ≤ ((19+9*Real.sqrt 2)*4*CJ)*((1+CG)*(BQ+BR)) := by
          nlinarith only [mul_nonneg hC (mul_nonneg hCG hBR)]
        _ = ((19+9*Real.sqrt 2)*4*CJ*(1+CG))*(BQ+BR) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hTB hQB
    exact (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)).trans_eq (by
      simp only [taylorGeneratorWeight];ring)
  | degree =>
    exact (closedHigherDegreeScalarFromRotationData_jets F0 ha0 Q R _ 2 BQ BR hQ hR).weaken
      (by simpa only [taylorGeneratorWeight,one_mul] using mul_le_mul_of_nonneg_right hDB hQB)
  | rotation i j =>
    exact ((hR (i,j)).clm closedThreeJetHigherScalarMultiplierL).weaken (by
      calc
        _ ≤ B*BR := mul_le_mul_of_nonneg_right hRB hBR
        _ ≤ B*(BQ+BR) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hQ.nonneg)
          ((norm_nonneg closedThreeJetHigherScalarMultiplierL).trans hRB)
        _ = _ := by simp only [taylorGeneratorWeight,one_mul])
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
