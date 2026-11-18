import Proof.NativeRelativeAdjointRotationCovariance
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
lemma NormalFrameRelativeResponsePacket.fullAdjoint_normalization
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    t.fullAdjoint (normalFrameRelativeNormalization d.γ p)=t.fullAdjoint p := by
  have hpN := V.normalizationStable p hp
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  have hCoef := radialAdjointFromResponseL_congr_sphere (F (normalFrameRelativeNormalization d.γ p)) (F p)
    (t.response p+sphereSobolevDegreeL)
    (fun w => q.matrix_normalization h hK p (t.sub (V.sub hp)) (t.sub (V.sub hpN)) w.val
      (Metric.closedBall_subset_closedBall hZ (Metric.closedBall_subset_closedBall (by norm_num)
        (Metric.sphere_subset_closedBall w.property))))
  change radialAdjointFromResponseL _ (t.response (normalFrameRelativeNormalization d.γ p)+sphereSobolevDegreeL) = _
  rw [t.response_normalization hZ h hK p (V.sub hp) (V.sub hpN)]
  exact hCoef
end ShrinkingSpheres
