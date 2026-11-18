import Proof.ConormalAdjointTaylorBound
import Proof.FirstRadialAdjointCorrectionIdentity
import Proof.ConormalRadialRealization
import Proof.ConormalOneData
import Proof.OrderOneNormalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual H1 conormal and normal-inverse Taylor data control the radial
    adjoint remainder after its bounded L2 first correction. -/
theorem conormalRadialAdjoint_remainder_bound {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r K P CB CN2 CI CM1 CM2 CDI CRI CT : ℝ)
    (hc : 0 < c) (hcK : c ≤ K) (hciK : c⁻¹ ≤ K) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hCB : 0 ≤ CB) (hCN2 : 0 ≤ CN2) (hCI : 0 ≤ CI)
    (hCM1 : 0 ≤ CM1) (hCRI : 0 ≤ CRI) (hCT : 0 ≤ CT) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hV1 : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hD1 : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P)
    (hB : ‖coarseFirstRadialVariationL c ell‖ ≤ CB)
    (hOne : OneBoundaryTaylorData F F0 F1 c r CI CM1 CM2 CDI CRI CT)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hN : ConormalOneData a ha F1 c r ell N CN2) :
    ‖conormalRadialAdjointL F N-sphereSobolevDegreeL-
      r • (coarseFirstRadialVariationL c ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
      ((2*K+(K*CB+72*P)+CN2)*CRI+((K*CB+72*P)+CN2)*(K^2*CM1)+CN2*K+
        (boundaryTangentialAdjointBudget*CT)*CI)*r^2 := by
  let B := coarseFirstRadialVariationL c ell
  let N1 := firstConormalOneL F1 c ell
  let M1 := oneBoundaryCoefficientMulL (normalCoefficientJet F1)
  let M0 := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))
  let H := (oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse
  let Td := adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  have hN1 : ‖N1‖ ≤ K*CB+72*P := norm_firstConormalOneL_le F1 c K P CB ell hc.le hcK hP hCB hB hV1 hD1
  have hFirst : c⁻¹ • (N1-sphereSobolevDegreeL.comp M1) =
      B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
    first_radial_adjoint_correction_scaled F0 F1 c hc ell hF0 hF1 ha1 hInv0
  have hTd : ‖Td‖ ≤ (boundaryTangentialAdjointBudget*CT)*r^2 :=
    (norm_adjointBoundaryTangentialL_le (fun j => tangentCoefficientJet F j) (CT*r^2)
      (mul_nonneg hCT (sq_nonneg _)) hOne.tangent_bound).trans_eq (by ring)
  exact norm_conormal_radial_adjoint_taylor_le N N1 Td H M1 B c r K (K*CB+72*P) CN2 CI CRI CM1
    (boundaryTangentialAdjointBudget*CT) hc hcK hciK hr hr1 hK (by positivity) hCN2 hCI hCRI hCM1
    (mul_nonneg boundaryTangentialAdjointBudget_nonneg hCT) hN1 hOne.first_normal_bound hOne.normal_inverse_bound
    hN.remainder_bound hOne.inverse_remainder_bound hTd hFirst

end ShrinkingSpheres
