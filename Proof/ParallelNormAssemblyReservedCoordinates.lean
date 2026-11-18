import Proof.PhysicalPotentialWordMatrix
import Proof.FrameTensorMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

lemma frame_tensor_covector_double (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (Q : Mat) (l : X →L[ℝ] ℝ) :
    (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y Q i j*l (d.frame y i)*l (d.frame y j))=
      ∑ a : I,∑ b : I,Q a b*l (axis a)*l (axis b) := by
  have hF (i : I) : l (d.frame y i)=∑ a : I,d.frame y i a*l (axis a) :=
    linear_axis_expansion l (d.frame y i)
  conv_rhs => simp only [← frameTensorMatrix_reconstruct d.γ d.frame y he Q]
  simp only [hF,Fin.sum_univ_three]
  ring

lemma frame_tensor_covector_left (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (Q : Mat) (l : X →L[ℝ] ℝ) (a : I) :
    (∑ i : I,(∑ j : I,frameTensorMatrix d.γ d.frame y Q i j*l (d.frame y j))*d.frame y i a)=
      ∑ b : I,Q a b*l (axis b) := by
  have hF (i : I) : l (d.frame y i)=∑ a : I,d.frame y i a*l (axis a) :=
    linear_axis_expansion l (d.frame y i)
  conv_rhs => simp only [← frameTensorMatrix_reconstruct d.γ d.frame y he Q]
  simp only [hF,Fin.sum_univ_three]
  ring

lemma frame_tensor_covector_right (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (Q : Mat) (l : X →L[ℝ] ℝ) (b : I) :
    (∑ j : I,(∑ i : I,frameTensorMatrix d.γ d.frame y Q i j*l (d.frame y i))*d.frame y j b)=
      ∑ a : I,Q a b*l (axis a) := by
  have hF (i : I) : l (d.frame y i)=∑ a : I,d.frame y i a*l (axis a) :=
    linear_axis_expansion l (d.frame y i)
  conv_rhs => simp only [← frameTensorMatrix_reconstruct d.γ d.frame y he Q]
  simp only [hF,Fin.sum_univ_three]
  ring

/-- Express frame generators through the genuine fixed-coordinate
coframe raising/error generators. Values alone enter this matrix. -/
def potentialFrameToCoordinate (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inl _,.inl _ => 1
  | .inr (.inl i),.inr (.inl a) => d.frame y i a
  | .inr (.inr i),.inr (.inr a) => d.frame y i a
  | _,_ => 0

/-- The complete potential word coefficients in a fixed-coordinate
coframe realization. No moving-frame derivative occurs in these bodies. -/
def potentialCoordinateWordCoefficient (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inl _,.inl _ => d.radius y*∑ a : I,∑ b : I,principal d.γ d.g₂ y a b*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (axis a)*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (axis b)
  | .inl _,.inr (.inl _) => 0
  | .inl _,.inr (.inr b) => d.radius y*∑ a : I,principal d.γ d.g₂ y a b*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (axis a)
  | .inr (.inl a),.inl _ => 2*∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (axis b)
  | .inr (.inl a),.inr (.inl b) => (principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y
  | .inr (.inl a),.inr (.inr b) => principal d.γ d.g₂ y a b
  | .inr (.inr a),.inl _ => d.radius y*∑ b : I,principal d.γ d.g₂ y a b*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (axis b)
  | .inr (.inr a),.inr (.inl b) => principal d.γ d.g₂ y a b
  | .inr (.inr a),.inr (.inr b) => d.radius y*principal d.γ d.g₂ y a b

/-- Exact transformation of EVERY quadratic-potential coefficient.
This is the cancellation that must precede covariant coefficient estimates
for arbitrary smooth orthonormal frames. -/
theorem potential_coordinate_coefficients_exact (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (a b : PhysicalPotentialGeneratorIndex) :
    (∑ i : PhysicalPotentialGeneratorIndex,∑ j : PhysicalPotentialGeneratorIndex,
      PhysicalPrincipalData.potentialWordCoefficient d y i j*
        potentialFrameToCoordinate d y i a*potentialFrameToCoordinate d y j b)=
      potentialCoordinateWordCoefficient d y a b := by
  let l := fderiv ℝ (fun x => Real.log (d.radius x)) y
  have hDD := frame_tensor_covector_double d y he (principal d.γ d.g₂ y) l
  have hL (a : I) := frame_tensor_covector_left d y he (principal d.γ d.g₂ y) l a
  have hR (b : I) := frame_tensor_covector_right d y he (principal d.γ d.g₂ y) l b
  have hGap (a : I) := frame_tensor_covector_left d y he (principal d.γ d.g₂ y-(d.γ y)⁻¹) l a
  have hQ (a b : I) := frameTensorMatrix_reconstruct d.γ d.frame y he (principal d.γ d.g₂ y) a b
  have hQG (a b : I) := frameTensorMatrix_reconstruct d.γ d.frame y he (principal d.γ d.g₂ y-(d.γ y)⁻¹) a b
  have hG (i j : I) : frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)=
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j := by
    rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y he]
  rcases a with u | (a | a) <;> rcases b with v | (b | b)
  all_goals simp only [potentialCoordinateWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique,
    potentialFrameToCoordinate,PhysicalPrincipalData.potentialWordCoefficient,
    zero_mul,mul_zero,one_mul,mul_one,Finset.sum_const_zero,add_zero,zero_add,scaledFrameLogRadius,hG]
  · simp only [Fin.sum_univ_three,l] at hDD ⊢
    linear_combination d.radius y*hDD
  · simp only [Fin.sum_univ_three,l] at hR ⊢
    linear_combination d.radius y*hR b
  · simp only [Fin.sum_univ_three,l] at hGap ⊢
    linear_combination 2*hGap a
  · simp only [Fin.sum_univ_three] at hQG ⊢
    linear_combination (d.radius y)⁻¹*hQG a b
  · exact hQ a b
  · simp only [Fin.sum_univ_three,l] at hL ⊢
    linear_combination d.radius y*hL a
  · exact hQ a b
  · simp only [Fin.sum_univ_three] at hQ ⊢
    linear_combination d.radius y*hQ a b

end ShrinkingSpheres.ParallelEnergy
