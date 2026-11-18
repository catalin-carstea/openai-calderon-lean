import Proof.FrameTensorOperatorCombination
import Proof.CovariantRotationGraphOperations
import Proof.ActualFrameFirstAdjointError
import Proof.MovingFrameSecond
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The physical tensor derivative of a frame-weighted operator family:
    its coordinate-index connection is kept explicit and uses frame values. -/
def frameWeightedCovariantTensorJet (d : Data)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) (y b : X) (i : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  frameTensorOperatorCombination d y b i (fun a => F a y) (fun a => S a y b)

lemma frameWeighted_covariant_graph (d : Data)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) (y b : X) (i : I)
    (hFS : ∀ a,DifferentiableAt ℝ (F a) y)
    (he : DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hFrame : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l)=if k=l then 1 else 0)
    (hS : ∀ a,CoarseCovariantRotationGraph d y b (F a) (S a y b)) :
    CoarseCovariantRotationGraph d y b (fun x => ∑ a : I,d.frame x i a • F a x)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y b i k •
        (∑ a : I,d.frame y k a • F a y))+frameWeightedCovariantTensorJet d F S y b i) := by
  have hDe (a : I) : DifferentiableAt ℝ (fun x => d.frame x i a) y :=
    (EuclideanSpace.proj (𝕜:=ℝ) a).differentiableAt.comp y he
  have hD (a : I) : fderiv ℝ (fun x => d.frame x i a) y b=
      (fderiv ℝ (fun x => d.frame x i) y b) a := by
    have hh := DFunLike.congr_fun ((EuclideanSpace.proj (𝕜:=ℝ) a).hasFDerivAt.comp y he.hasFDerivAt).fderiv b
    exact hh
  have hReconstruct := frame_connection_reconstruct d.γ d.frame y b hFrame i
  have hCoeff (a : I) : fderiv ℝ (fun x => d.frame x i a) y b=
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y b i k*d.frame y k a)-
        (connection d.γ y b (d.frame y i)) a := by
    have hh := congrArg (fun v : X => v a) hReconstruct
    simp only [covariantFrameVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul] at hh
    rw [hD]
    linarith only [hh]
  have hGraph := CoarseCovariantRotationGraph.sum_three
    (fun a x => d.frame x i a • F a x)
    (fun a => d.frame y i a • S a y b+fderiv ℝ (fun x => d.frame x i a) y b • F a y)
    (fun a => (hS a).smul (fun x => d.frame x i a) (hDe a) (hFS a))
    (fun a => (hDe a).smul (hFS a))
  have hEq : (∑ a : I,(d.frame y i a • S a y b+fderiv ℝ (fun x => d.frame x i a) y b • F a y))=
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y b i k •
        (∑ a : I,d.frame y k a • F a y))+frameWeightedCovariantTensorJet d F S y b i := by
    simp only [hCoeff,frameWeightedCovariantTensorJet,frameTensorOperatorCombination,Fin.sum_univ_three]
    module
  exact hEq ▸ hGraph

lemma norm_frameWeightedCovariantTensorJet_le (d : Data)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) (y b : X) (i : I)
    {K CΓ C0 C1 : ℝ} (hK : 0 ≤ K) (hΓ : 0 ≤ CΓ)
    (he : ∀ a,|d.frame y i a| ≤ K)
    (hc : ∀ a,|(connection d.γ y b (d.frame y i)) a| ≤ CΓ)
    (hF : ∀ a,‖F a y‖ ≤ C0) (hS : ∀ a,‖S a y b‖ ≤ C1) :
    ‖frameWeightedCovariantTensorJet d F S y b i‖ ≤ 3*K*C1+3*CΓ*C0 := by
  exact norm_frameTensorOperatorCombination_le d y b i
    (fun a => F a y) (fun a => S a y b) hK hΓ he hc hF hS

lemma contDiffOn_frameWeightedCovariantTensorJet {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (hF : ∀ a,ContDiffOn ℝ ∞ (F a) Y) (hS : ∀ a,ContDiffOn ℝ ∞ (S a) Y)
    (V : X → X) (hV : ContDiffOn ℝ ∞ V Y) (i : I) :
    ContDiffOn ℝ ∞ (fun y => frameWeightedCovariantTensorJet d F S y (V y) i) Y := by
  have hConn := h.contDiffOn_connection hY hK V (fun x => d.frame x i) hV (he i)
  exact (ContDiffOn.sum (fun a _ =>
    (contDiffOn_vector_component _ (he i) a).smul ((hS a).clm_apply hV))).sub
      (ContDiffOn.sum (fun a _ => (contDiffOn_vector_component _ hConn a).smul (hF a)))

end ShrinkingSpheres
