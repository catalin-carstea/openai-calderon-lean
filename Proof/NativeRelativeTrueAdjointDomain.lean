import Proof.NativeRelativeSymmetricAdjointDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}
  {t : NormalFrameRelativeResponsePacket q}

theorem SymmetricAdjointDomain.fullPair (V : SymmetricAdjointDomain t)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    ∀ u v : SphereSobolev 1,
    ⟪(t.response p+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        radialAdjointFromResponseL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
          (t.response p+sphereSobolevDegreeL) v⟫_ℝ := by
  exact midpoint_radialAdjointFromResponse_pairing_of_one_inverse
    (commonSupportEnergyMemLp q.a q.smooth p) (V.coercive p hp) (V.coefficientSymmetric p hp)
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
    (fun z _ => congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p) z)
    (V.strong p hp) (V.normal p hp) (t.oneInvertible p (V.sub hp))
    (t.response p) (t.highRestriction p (V.sub hp))

theorem SymmetricAdjointDomain.taylorPair (V : SymmetricAdjointDomain t)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (u v : SphereSobolev 1) :
    ⟪t.forwardTaylor p u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,t.adjointTaylor p v⟫_ℝ := by
  let B := radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)
  let Da := radialAdjointFromResponseL
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
    (t.response p+sphereSobolevDegreeL)
  have hTaylor := radial_taylor_true_adjoint_pairing (t.response p) Da B (d.radius y) (V.fullPair p hp)
  have hFirst : coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p) = B := by
    simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ p)
  have hValue := congrArg (fun L : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    ⟪(t.response p-d.radius y • L.comp (sphereSobolevInclusionL 1 0 (by norm_num))) u,
      sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ) hFirst
  exact hValue.trans (hTaylor u v)

end ShrinkingSpheres.NormalFrameRelativeResponsePacket
