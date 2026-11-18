import Proof.RelativeNormalScalarRemainderFamily
import Proof.NormalFrameRelativeActualCoefficientGerms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

def matrixNormalContraction (A : Mat) (z : X) : ℝ := ∑ i : I,∑ j : I,A i j*z i*z j

lemma matrixNormalContraction_sub (A B : Mat) (z : X) :
    matrixNormalContraction (A-B) z=matrixNormalContraction A z-matrixNormalContraction B z := by
  simp only [matrixNormalContraction,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma matrixNormalContraction_smul (A : Mat) (c : ℝ) (z : X) :
    matrixNormalContraction (c • A) z=c*matrixNormalContraction A z := by
  simp only [matrixNormalContraction,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma matrixNormalContraction_one (w : UnitSphere) : matrixNormalContraction (1:Mat) w.val=1 := by
  have hFun : matrixNormalContraction (1:Mat) w.val=∑ i : I,(w.val i)^2 := by
    simp only [matrixNormalContraction,Matrix.one_apply,ite_mul,one_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact Finset.sum_congr rfl (fun i _ => (pow_two _).symm)
  exact hFun.trans (unitSphere_sum_sq w)

lemma matrixNormalContraction_normal_data (F : SmoothCoefficientMatrix 2) (z : X) :
    matrixNormalContraction (coefficientMatrixField 2 F z) z=(boundaryNormalCoefficientData F).1 z := by
  change (∑ i : I,∑ j : I,coefficientValue 2 (F i j) z*z i*z j)=
    ∑ i : I,∑ j : I,z i*coefficientValue 2 (F i j) z*z j
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change coefficientValue 2 (F i j) z*z i*z j=z i*coefficientValue 2 (F i j) z*z j
  ring

lemma RelativeNormalScalarRemainderFamily.point_scalar_expansion
    {d : Data} {y : X} {C : ℝ} (R : RelativeNormalScalarRemainderFamily d y C)
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val)
    (w : UnitSphere) :
    (boundaryNormalCoefficientData F).1 w.val =
      1+d.radius y*firstDensityLogCovector d y w.val+R.scalar (((y,frameVectorLinear d.frame y),0),w.val) := by
  have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
    (Metric.sphere_subset_closedBall w.property)
  have hR := (R.actual _ R.point w.val hw).eq_of_nhds
  change R.scalar (((y,frameVectorLinear d.frame y),0),w.val)=
    matrixNormalContraction (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y)
      (((y,frameVectorLinear d.frame y),0),w.val)-(1:Mat)-
      d.radius y • normalFrameRelativeFirstModel d.γ d.g₁ (((y,frameVectorLinear d.frame y),0),w.val)) w.val at hR
  rw [h.normalFrameRelativeCoefficient_actual_zero hy,normalFrameRelativeFirstModel_scalar,
    h.normalFrameRelativeFirstCovector_actual_zero hΩ hK hy,← hF w,
    matrixNormalContraction_sub,matrixNormalContraction_sub,matrixNormalContraction_normal_data,
    matrixNormalContraction_one,matrixNormalContraction_smul,matrixNormalContraction_smul,
    matrixNormalContraction_one,mul_one] at hR
  linarith only [hR]
end ShrinkingSpheres
