import Proof.FlatLoweringSectionCalculus
import Proof.ContractedCovectorAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME variable-frame divergence and lowering tensor-index
connection cancel exactly after contraction. No frame jet is estimated. -/
theorem contracted_flat_lowering_covariant_pair {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (V : X → SphereSobolev 2) {y : X} (hy : y ∈ Y) (hV : DifferentiableAt ℝ V y)
    (u : SphereSobolev 0) :
    (∑ i : I,(metricDensity d.γ y*⟪u,oneSectionCovariantDerivative d
        (fun x => flatLoweringSobolevL 2 i (V x)) y (d.frame y i)⟫_ℝ+
      weightedDivergence (metricDensity d.γ) (fun x => d.frame x i) y*
        ⟪u,sphereSobolevInclusionL 1 0 (by norm_num) (flatLoweringSobolevL 2 i (V y))⟫_ℝ))=
      metricDensity d.γ y*∑ i : I,⟪u,flatOneLoweringL i
        (highSectionCovariantDerivative d V y (d.frame y i))⟫_ℝ := by
  have hSkew (a : X) (p q : I) := frameConnection_skew hY hg hK d.frame he hFrame hy a p q
  have hD (i : I) := oneSectionCovariantDerivative_flatLowering d V y (d.frame y i) hV (hSkew (d.frame y i)) i
  have hCancel := frame_connection_trace_cancellation
    (fun v i j => frameConnectionCoefficient d.γ d.frame y (d.frame y v) i j)
    (fun v i j => hSkew (d.frame y v) i j)
    (fun i => ⟪u,flatOneLoweringL i (sphereSobolevInclusionL 2 1 (by norm_num) (V y))⟫_ℝ)
  simp only [hD,flatLoweringSobolevL_two_coarse,weightedDivergence_frame hY hg hK d.frame he hy (hFrame y hy),
    inner_add_right,inner_sum,real_inner_smul_right,Fin.sum_univ_three] at ⊢
  simp only [Fin.sum_univ_three] at hCancel
  linear_combination metricDensity d.γ y*hCancel

end ShrinkingSpheres
