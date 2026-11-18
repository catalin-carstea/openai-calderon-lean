import Proof.CommonSupportOneBoundaryAffine
import Proof.CommonSupportOneBoundaryDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

structure CommonSupportOneBoundaryTaylorDerivativeBounds
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r q : ℝ) : Prop where
  coarseNormal : ‖fderiv ℝ (fun t =>
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))))-
    ContinuousLinearMap.id ℝ (SphereSobolev 0)-
    r • coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (normalCoefficientJet (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t))))) 0‖ ≤ 36*q
  oneNormal : ‖fderiv ℝ (fun t =>
    oneBoundaryCoefficientMulL (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))-
    ContinuousLinearMap.id ℝ (SphereSobolev 1)-
    r • oneBoundaryCoefficientMulL (normalCoefficientJet (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t))) 0‖ ≤ (73*36)*q
  tangent : ‖fderiv ℝ (fun t => coarseBoundaryTangentialL
    (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t) j)) 0‖ ≤
      boundaryTangentialCoarseBudget*(78*q)
  adjointTangent : ‖fderiv ℝ (fun t => adjointBoundaryTangentialL
    (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t) j)) 0‖ ≤
      boundaryTangentialAdjointBudget*((73*78)*q)

/-- The scalar first model cancels the entire tangential family. The same
    compact residual controls both coarse and H1 normal Taylor derivatives. -/
theorem commonSupport_one_boundary_taylor_derivatives
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r q : ℝ)
    (hField : ∀ p,aD p = a p-r • a1 p)
    (V : Set ℝ) (hV : IsOpen V) (h0V : (0:ℝ) ∈ V) (s : ℝ → X → ℝ)
    (hScalar : ∀ t ∈ V,∀ w : UnitSphere,a1 (t,w.val) = s t w.val • (1:Mat))
    (hND : CommonSupportOneBoundaryDerivativeBounds aD haD SD hSD hzD q) :
    CommonSupportOneBoundaryTaylorDerivativeBounds a a1 ha ha1 S S1 hS hS1 hz hz1 r q := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hOps := commonSupport_coarse_one_sub_smul_families a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
  have hZero (t : ℝ) (ht : t ∈ V) := boundaryTangential_scalar_zero (F1 t) (s t) (by
    intro w
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hScalar t ht w)
  refine ⟨?_,?_,?_,?_⟩
  · have hFun : (fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F t))))-
        ContinuousLinearMap.id ℝ (SphereSobolev 0)-
        r • coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F1 t))))) =
        fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (FD t))))-
          ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
      funext t
      rw [← hOps.1 t]
      module
    rw [hFun,fderiv_sub_const]
    exact hND.coarseNormal
  · have hFun : (fun t => oneBoundaryCoefficientMulL (normalCoefficientJet (F t))-
        ContinuousLinearMap.id ℝ (SphereSobolev 1)-r • oneBoundaryCoefficientMulL (normalCoefficientJet (F1 t))) =
        fun t => oneBoundaryCoefficientMulL (normalCoefficientJet (FD t))-ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
      funext t
      rw [← hOps.2.1 t]
      module
    rw [hFun,fderiv_sub_const]
    exact hND.oneNormal
  · have hNear : (fun t => coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)) =ᶠ[𝓝 (0:ℝ)]
        fun t => coarseBoundaryTangentialL (fun j => tangentCoefficientJet (FD t) j) := by
      filter_upwards [hV.mem_nhds h0V] with t ht
      have h := hOps.2.2.1 t
      rw [(hZero t ht).1,smul_zero,sub_zero] at h
      exact h
    exact (congrArg norm hNear.fderiv_eq).le.trans hND.tangent
  · have hNear : (fun t => adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)) =ᶠ[𝓝 (0:ℝ)]
        fun t => adjointBoundaryTangentialL (fun j => tangentCoefficientJet (FD t) j) := by
      filter_upwards [hV.mem_nhds h0V] with t ht
      have h := hOps.2.2.2 t
      rw [(hZero t ht).2,smul_zero,sub_zero] at h
      exact h
    exact (congrArg norm hNear.fderiv_eq).le.trans hND.adjointTangent

end ShrinkingSpheres
