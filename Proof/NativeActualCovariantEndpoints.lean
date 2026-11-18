import Proof.NativeCovariantErrorEndpoints
import Proof.NativeActualFirstErrorCovariant
import Proof.CoarseCovariantJetFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- The native endpoint derivatives realize the SAME actual covariant error
    jet, including any globally chosen coarse jet with its physical graph. -/
lemma actual_covariant_error_endpoints
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAS : ContDiffOn ℝ ∞ A Y) (hGS : ContDiffOn ℝ ∞ G Y)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (b : X) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) S) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let v := normalFrameRelativeHorizontalField d.γ d.radius b p
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 hK) p v)=
      S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  dsimp only
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  have hGraph := s.actual_first_error_covariant_graph C Vt hY hΩ hSub hd hK hy
    R A G hAS hGS hR hA hG b
  have hEq := coarseCovariantRotationGraph_unique hS hGraph
  have hCompat := s.first_adjoint_error_derivative_endpoints C Vt Vc hY hΩ hd.1.1 hK
    hd.2.2.2.2.1 hF0 p v (s.centerDegreeDomain_pointMem Vt) (s.centerDegreeDomain_pointMem Vc)
  constructor
  · exact (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T) hEq).trans hCompat.1
  · exact hCompat.2.trans (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hEq.symm)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
