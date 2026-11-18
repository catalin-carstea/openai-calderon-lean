import Proof.NormalFrameRelativeCoefficientJetFamily
import Proof.CommonSupportNativeJointJetBounds
import Proof.BoundaryMatrixMultiplierLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {Y Ω : Set X} {g g₁ : MetricField} {E : X × X → X} {y : X} {L : X →L[ℝ] X}
  {r : ℝ} {N : ℕ} {Z C : ℝ}

namespace NormalFrameRelativeCoefficientJetFamily

def affineCoefficient (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C) :
    NormalFrameRelativeParameter × X → Mat := fun p => q.a p-r • q.a1 p

theorem affineSmooth (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C) :
    ContDiff ℝ ∞ q.affineCoefficient := q.smooth.sub (q.firstSmooth.const_smul r)

theorem affineSupported (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C) :
    ∀ p z,z ∉ q.support → q.affineCoefficient (p,z) = 0 := by
  intro p z hz
  simp only [affineCoefficient,q.supported p z hz,q.firstSupported p z hz,smul_zero,sub_zero]

theorem coefficientMixedJets (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C)
    (x : X) (hx : ‖x‖ ≤ Z) (n k : ℕ) (hnk : n+k ≤ N) (i j : I) :
    ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k (fun z => q.a (t,z) i j) x) ((y,L),0)‖ ≤ C :=
  (norm_iteratedFDeriv_parameter_spatial_matrix_entry_le q.a q.smooth ((y,L),0) x n k i j).trans
    (q.coefficientJets x hx (n+k) hnk)

theorem firstMixedJets (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C)
    (x : X) (hx : ‖x‖ ≤ Z) (n k : ℕ) (hnk : n+k ≤ N) (i j : I) :
    ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k (fun z => q.a1 (t,z) i j) x) ((y,L),0)‖ ≤ C :=
  (norm_iteratedFDeriv_parameter_spatial_matrix_entry_le q.a1 q.firstSmooth ((y,L),0) x n k i j).trans
    (q.firstJets x hx (n+k) hnk)

theorem remainderMixedJets (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C)
    (x : X) (hx : ‖x‖ ≤ Z) (n k : ℕ) (hnk : n+k ≤ N) (i j : I) :
    ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k
      (fun z => (q.affineCoefficient (t,z)-(1:Mat)) i j) x) ((y,L),0)‖ ≤ C*r^2 := by
  let D : NormalFrameRelativeParameter × X → Mat := fun p => q.affineCoefficient p-(1:Mat)
  have hD : ContDiff ℝ ∞ D := q.affineSmooth.sub contDiff_const
  have hEq : D = fun p => q.a p-(1:Mat)-r • q.a1 p := by
    funext p
    dsimp only [D,affineCoefficient]
    abel
  exact (norm_iteratedFDeriv_parameter_spatial_matrix_entry_le D hD ((y,L),0) x n k i j).trans
    (by rw [hEq];exact q.remainderJets x hx (n+k) hnk)

theorem firstTangentialGerm (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r N Z C)
    (hZ : 1 ≤ Z) (j : I) :
    (fun t => boundaryMatrixMultiplier (some j)
      (commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported t)) =ᶠ[𝓝 ((y,L),0)]
        (fun _ => 0) := by
  filter_upwards [q.domainOpen.mem_nhds q.pointMem] with t ht
  apply negativeTangentCoefficient_scalar_zero _ (normalFrameRelativeFirstCovector g g₁ t)
  intro w
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  apply q.firstScalar t ht
  have hw : ‖w.val‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  simpa only [Metric.mem_closedBall,dist_zero_right,hw] using hZ

end NormalFrameRelativeCoefficientJetFamily
end ShrinkingSpheres
