import Proof.CovariantRotationGraphOperations
import Proof.FrameCoframeCovariantDerivative
import Proof.FrameErrorMatrixRaisingCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma skew_weighted_operator_pair_cancel {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Γ : I → I → ℝ) (hΓ : ∀ i k,Γ i k= -Γ k i) (c : I → ℝ) (F : I → W) :
    (∑ i : I,c i • (∑ k : I,Γ i k • F k))+
      (∑ i : I,(∑ k : I,Γ i k*c k) • F i)=0 := by
  simp only [Finset.smul_sum,Finset.sum_smul,smul_smul]
  have hh : (∑ i : I,∑ k : I,(c i*Γ i k) • F k)=
      -(∑ i : I,∑ k : I,(Γ i k*c k) • F i) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [hΓ i k]
    simp only [mul_neg,neg_smul,mul_comm]
  rw [hh,neg_add_cancel]

/-- Coframe contraction cancels both unrestricted tensor-index frame
    connections. Only the actual connection of the fixed physical direction
    and the given tensor jet remain. -/
theorem coframeWeighted_covariant_graph {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Y) (a b : X)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (T : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hFD : ∀ i,DifferentiableAt ℝ (F i) y)
    (hGraph : ∀ i,CoarseCovariantRotationGraph d y a (F i)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • F k y)+T i)) :
    CoarseCovariantRotationGraph d y a
      (fun x => ∑ i : I,frameCoordinateLinear d.γ d.frame x i b • F i x)
      ((∑ i : I,frameCoordinateLinear d.γ d.frame y i b • T i)+
        (∑ i : I,frameCoordinateLinear d.γ d.frame y i (connection d.γ y a b) • F i y)) := by
  let c := fun (i : I) (x : X) => frameCoordinateLinear d.γ d.frame x i b
  let Γ := frameConnectionCoefficient d.γ d.frame y a
  let cΓ := fun i => frameCoordinateLinear d.γ d.frame y i (connection d.γ y a b)
  have hΓ : ∀ i k,Γ i k= -Γ k i := frameConnection_skew hY hg hK d.frame he hFrame hy a
  have hCD (i : I) : DifferentiableAt ℝ (c i) y := by
    have hh := hg.contDiffOn_metricPair (fun _ => b) (fun x => d.frame x i) contDiffOn_const (he i)
    have hEq : c i=(fun x => metricPair d.γ x b (d.frame x i)) := by
      funext x
      exact frameCoordinateLinear_apply d.γ d.frame x b i
    rw [hEq]
    exact (hh.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hD (i : I) : fderiv ℝ (c i) y a=(∑ k : I,Γ i k*c k y)+cΓ i := by
    have hh := frameCoordinateLinear_covariant_derivative hY hg hK d.frame he hy (hFrame y hy) a b i
    change fderiv ℝ (c i) y a-(∑ k : I,Γ i k*c k y)=cΓ i at hh
    exact (sub_eq_iff_eq_add).mp hh |>.trans (add_comm _ _)
  have hSum := CoarseCovariantRotationGraph.sum_three
    (fun i x => c i x • F i x)
    (fun i => c i y • ((∑ k : I,Γ i k • F k y)+T i)+fderiv ℝ (c i) y a • F i y)
    (fun i => (hGraph i).smul (c i) (hCD i) (hFD i))
    (fun i => (hCD i).smul (hFD i))
  have hEq : (∑ i : I,(c i y • ((∑ k : I,Γ i k • F k y)+T i)+fderiv ℝ (c i) y a • F i y))=
      (∑ i : I,c i y • T i)+(∑ i : I,cΓ i • F i y) := by
    simp only [hD,smul_add,add_smul,Finset.sum_add_distrib]
    have hh := skew_weighted_operator_pair_cancel Γ hΓ (fun i => c i y) (fun i => F i y)
    exact (show _ = ((∑ i : I,c i y • (∑ k : I,Γ i k • F k y))+
      (∑ i : I,(∑ k : I,Γ i k*c k y) • F i y))+
      ((∑ i : I,c i y • T i)+(∑ i : I,cΓ i • F i y)) by abel).trans (by rw [hh,zero_add])
  exact hEq ▸ hSum

lemma norm_coframe_covariant_tensor_jet_le (d : Data) (y a b : X)
    (F T : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    {C CΓ CF CT : ℝ} (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ)
    (hc : ∀ i,|frameCoordinateLinear d.γ d.frame y i b| ≤ C)
    (hcΓ : ∀ i,|frameCoordinateLinear d.γ d.frame y i (connection d.γ y a b)| ≤ CΓ)
    (hF : ∀ i,‖F i‖ ≤ CF) (hT : ∀ i,‖T i‖ ≤ CT) :
    ‖(∑ i : I,frameCoordinateLinear d.γ d.frame y i b • T i)+
      (∑ i : I,frameCoordinateLinear d.γ d.frame y i (connection d.γ y a b) • F i)‖ ≤
        3*C*CT+3*CΓ*CF := by
  exact (norm_add_le _ _).trans (add_le_add
    (norm_weighted_sum_three_le _ T C CT hC hc hT)
    (norm_weighted_sum_three_le _ F CΓ CF hCΓ hcΓ hF))
end ShrinkingSpheres
