import Proof.NativeScalarBoundedAdjointForm
import Proof.NativeHigherScalarAdjointRemainderData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Additional actual angular and bounded-higher witnesses needed to
upgrade a scalar-plus-bounded packet to higher mixed commutators. These
are substantive premises, not consequences of phantom Sobolev type equality. -/
structure NativeScalarBoundedHigherData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale : ℝ}
    {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    (B : NativeScalarBoundedEndpointData T L H CQB CZB scale) (CAug : ℝ) where
  angular : TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3
  angular_half : ∀ a i j,closedThreeJetHalfBoundaryScalarMultiplierL (angular a (i,j))=
    closedCoefficientAngularHalfL i j (B.coefficient a)
  augmented_bound : (∑ a,taylorGeneratorWeight (d.radius y) a*(‖B.coefficient a‖+
    ∑ ij : I × I,‖angular a ij‖)) ≤ CAug*scale
  boundedHigher : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)
  boundedAdjointHigher : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)
  boundedHigher_pair : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp boundedHigher=
    B.boundedHalf.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  boundedAdjointHigher_pair : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp boundedAdjointHigher=
    B.boundedNegative.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  higher_bounds : ‖boundedHigher‖ ≤ CZB*scale ∧ ‖boundedAdjointHigher‖ ≤ CZB*scale

namespace NativeScalarBoundedHigherData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG CK CJ BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
  {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale CAug : ℝ}
  {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
  {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
  {B : NativeScalarBoundedEndpointData T L H CQB CZB scale}

def adjointRemainderHigher (D : NativeScalarBoundedHigherData B CAug)
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.scalarAdjointRemainderHigher ha0 KH B.coefficient D.angular+D.boundedAdjointHigher

lemma adjointRemainderHigher_compatible (D : NativeScalarBoundedHigherData B CAug)
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hKern : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (D.adjointRemainderHigher A ha0 KH)=
      (B.adjointRemainderHalfL ha0 KN).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hS := A.scalarAdjointRemainderHigher_compatible T ha0 HS KH KN B.coefficient D.angular D.angular_half hKern
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => U+V)
      hS D.boundedAdjointHigher_pair).trans (ContinuousLinearMap.add_comp _ _ _).symm)

lemma norm_adjointRemainderHigher_le (D : NativeScalarBoundedHigherData B CAug)
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (hBS : 0 ≤ BS)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (BK : ℝ) (hBK : 0 ≤ BK) (hKH : ‖KH‖ ≤ BK*(d.radius y)^2) :
    ‖D.adjointRemainderHigher A ha0 KH‖ ≤
      ((‖closedThreeJetHigherScalarMultiplierL‖*BK+BS)*CAug+CZB)*scale := by
  have hS := A.scalarAdjointRemainderHigher_norm_le ha0 HS KH BK hBK hKH B.coefficient D.angular
  have hRaw := hS.trans (mul_le_mul_of_nonneg_left D.augmented_bound
    (add_nonneg (mul_nonneg (norm_nonneg _) hBK) hBS))
  exact (norm_add_le _ _).trans ((add_le_add hRaw D.higher_bounds.2).trans_eq (by ring))
end NativeScalarBoundedHigherData
end ShrinkingSpheres
