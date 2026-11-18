import Proof.HighSectionCovariantHessianLinear
import Proof.PrincipalAdjointBudgetDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma continuousBilinear_axis_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : X →L[ℝ] X →L[ℝ] E) (a b : X) :
    T a b=∑ i : I,∑ j : I,(a i*b j) • T (axis i) (axis j) := by
  calc
    _ = T (∑ i : I,a i • axis i) (∑ j : I,b j • axis j) := by rw [axis_expansion,axis_expansion]
    _ = _ := by
      simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]

/-- The actual moving-frame trace contracts to the SAME coordinate tensor
and the genuine covariant Hessian, with no frame derivatives left over. -/
theorem highSectionCovariantHessian_coordinate_contraction (d : Data) (U : X → SphereSobolev 2)
    (y : X) (Q : Mat)
    (hFrame : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l)=if k=l then 1 else 0)
    (hL : DifferentiableAt ℝ (highSectionCovariantDerivativeLinear d U) y)
    (he : ∀ j,DifferentiableAt ℝ (fun x => d.frame x j) y) :
    (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y Q i j • highSectionCovariantHessian d U y i j)=
      ∑ a : I,∑ b : I,Q a b • highSectionCovariantHessianLinear d U y (axis a) (axis b) := by
  calc
    _ = ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y Q i j •
        highSectionCovariantHessianLinear d U y (d.frame y i) (d.frame y j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [highSectionCovariantHessian_eq_bilinear d U y i j hFrame hL (he j)]
    _ = ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y Q i j •
        (∑ a : I,∑ b : I,(d.frame y i a*d.frame y j b) •
          highSectionCovariantHessianLinear d U y (axis a) (axis b)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => frameTensorMatrix d.γ d.frame y Q i j • v)
        (continuousBilinear_axis_expansion (highSectionCovariantHessianLinear d U y) (d.frame y i) (d.frame y j))
    _ = _ := (frameTensorMatrix_contraction d.γ d.frame y hFrame Q
      (fun a b => highSectionCovariantHessianLinear d U y (axis a) (axis b))).symm

lemma principal_highSectionCovariantHessian_coordinate (d : Data) (U : X → SphereSobolev 2) (y : X)
    (hFrame : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l)=if k=l then 1 else 0)
    (hL : DifferentiableAt ℝ (highSectionCovariantDerivativeLinear d U) y)
    (he : ∀ j,DifferentiableAt ℝ (fun x => d.frame x j) y) :
    d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
      highSectionCovariantHessian d U y i j)=
      ∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
        highSectionCovariantHessianLinear d U y (axis a) (axis b) := by
  rw [highSectionCovariantHessian_coordinate_contraction d U y _ hFrame hL he]
  simp only [Finset.smul_sum,smul_smul,scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul]

end ShrinkingSpheres
