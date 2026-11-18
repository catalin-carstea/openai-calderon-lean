import Proof.PrincipalModelFirstDerivative
import Proof.ModelPotentialRadiusBudget
import Proof.FiniteMatrixNormBound
import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine balanced realization of the entire zero-base model potential. -/
def principalModelPotentialHalfL (d : Data) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let DI := (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  let DD := (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))
  (∑ i : I,∑ j : I,q i j •
    ((d.radius y*hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)) • DI+
      (d.radius y*f i*f j) • DD))+
    (2:ℝ) • (∑ i : I,∑ j : I,((q i j-(if i=j then 1 else 0))*f j) •
      (flatHalfRaisingL i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ)))

lemma principalModelPotentialHalfL_actual (d : Data) (y : X) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (principalModelPotentialL d y u)=
      principalModelPotentialHalfL d y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  simp only [principalModelPotentialL,principalModelPotentialHalfL,
    _root_.add_apply,_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sum,map_smul,sphereSobolevDegreeL_half,flatOneRaisingL_half,
    sphereSobolevShiftedDegreeL_threehalf_high,sphereSobolevInclusionL_trans_apply,
    Finset.smul_sum,smul_add,smul_smul]
  simp only [Fin.sum_univ_three]
  module

lemma Admissible.norm_principalModelPotentialHalfL_small {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖principalModelPotentialHalfL d y‖ ≤
      (81*(K+1)*K^2*(2*|Cj 2|+8)+3240*K^2*radialDriftSobolevBound (-(1/2:ℝ)))*ε := by
  let B := 9*(K+1)*K^2
  let N := 10*radialDriftSobolevBound (-(1/2:ℝ))
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let H := fun i j => hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)
  let DI := (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  let DD := (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hN : 0 ≤ N := mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
  have hDI : ‖DI‖ ≤ 2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_sphereSobolevShiftedDegreeL_le_two _) (norm_sphereSobolevInclusionL_le _ _ _)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (mul_one _))
  have hDD : ‖DD‖ ≤ 4 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_sphereSobolevShiftedDegreeL_le_two _) (norm_sphereSobolevShiftedDegreeL_le_two _)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by norm_num))
  have hCoeff (i j : I) :
      ‖(d.radius y*H i j) • DI+(d.radius y*f i*f j) • DD‖ ≤ (2*|Cj 2|+8)*ε := by
    have hOne : ‖(d.radius y*H i j) • DI‖ ≤ ((|Cj 2|+2)*ε)*2 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hd.radius_frame_logRadius_hessian_small hY hy i j) hDI (norm_nonneg _) (by positivity)
    have hTwo : ‖(d.radius y*f i*f j) • DD‖ ≤ ε*4 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hd.radius_frame_logRadius_product_small hy i j) hDD (norm_nonneg _) hε
    exact (norm_add_le _ _).trans ((add_le_add hOne hTwo).trans_eq (by ring))
  have hQ (i j : I) : |q i j| ≤ B := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1
  have hMain : ‖∑ i : I,∑ j : I,q i j •
      ((d.radius y*H i j) • DI+(d.radius y*f i*f j) • DD)‖ ≤ 9*B*((2*|Cj 2|+8)*ε) :=
    norm_weighted_matrix_three_le q _ B _ hB hQ hCoeff
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrβ : d.radius y*beta d.γ d.radius y ≤ 1 := ((radius_bounds (d.radius y) (beta d.γ d.radius y)
    floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.1).trans
      ((div_le_self hε hf).trans hε1)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hMixed (i j : I) : |(q i j-(if i=j then 1 else 0))*f j| ≤ 9*K^2*ε := by
    rw [abs_mul]
    calc
      _ ≤ (9*K^2*ε*d.radius y)*beta d.γ d.radius y :=
        mul_le_mul (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).1
          (frame_logRadius_component_bound d.γ d.frame d.radius y hFrame j) (abs_nonneg _) (by positivity)
      _ = (9*K^2*ε)*(d.radius y*beta d.γ d.radius y) := by ring
      _ ≤ (9*K^2*ε)*1 := mul_le_mul_of_nonneg_left hrβ (by positivity)
      _ = _ := mul_one _
  have hRaise (i j : I) : ‖(flatHalfRaisingL i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))‖ ≤ 2*N :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_flatHalfRaisingL_le i) (norm_sphereSobolevShiftedDegreeL_le_two _)
        (norm_nonneg _) hN).trans_eq (by ring))
  have hRest : ‖(2:ℝ) • (∑ i : I,∑ j : I,((q i j-(if i=j then 1 else 0))*f j) •
      (flatHalfRaisingL i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ)))‖ ≤ 36*(9*K^2*ε)*N := by
    have h := norm_weighted_matrix_three_le (fun i j => (q i j-(if i=j then 1 else 0))*f j)
      (fun i _j => (flatHalfRaisingL i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))) (9*K^2*ε) (2*N)
      (by positivity) hMixed hRaise
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  exact (norm_add_le _ _).trans ((add_le_add hMain hRest).trans_eq (by dsimp only [B,N];ring))
end ShrinkingSpheres
