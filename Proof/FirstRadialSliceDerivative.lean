import Proof.ParallelFirstModelDerivativeBounds
import Proof.RadialCorrectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Background.parallelFirstCoefficientCovector_zero {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) :
    parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) 0 = firstDensityLogCovector d y := by
  rw [h.firstDensityLogCovector_eq_differential hK hΩ hy]
  simp only [parallelFirstCoefficientCovector,zero_smul,add_zero,affineParallelFrame_zero]

/-- The genuine parallel first correction has the already controlled
    covariant-Hessian derivative, without any arbitrary frame jet budget. -/
theorem Background.parallel_first_correction_derivative_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X) :
    ‖fderiv ℝ (fun t => radialCorrectionCovectorL
      (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t)) 0‖ ≤
      (6*parallelFirstModelDerivativeBudget hm K M)*‖a‖ := by
  let T := firstDensityCovariantLinearL d y a
  let C := K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
    (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hT : ‖T‖ ≤ C*‖a‖ := h.norm_firstDensityCovariantLinearL_le hΩ hK hm hy a
  have hEll := (h.firstDensityLogDifferential_smooth hKpos hΩ).contDiffAt (hΩ.mem_nhds hy)
  have hCurve := hasDerivAt_parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) hEll
  rw [h.firstDensityLogCovariantDerivative_frame_eq hΩ hKpos hy a] at hCurve
  have hB := radialCorrectionCovectorL.hasFDerivAt.comp_hasDerivAt (0:ℝ) hCurve
  change HasDerivAt (fun t => radialCorrectionCovectorL
    (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t))
    (radialCorrectionCovectorL T) 0 at hB
  have hN : ‖radialCorrectionCovectorL T‖ ≤ (6*parallelFirstModelDerivativeBudget hm K M)*‖a‖ := by
    calc
      _ ≤ 6*(C*‖a‖) := (norm_radialCorrectionCovectorL_apply_le T).trans (by gcongr)
      _ ≤ (6*parallelFirstModelDerivativeBudget hm K M)*‖a‖ := by
        dsimp only [parallelFirstModelDerivativeBudget,C] at *
        nlinarith only [mul_nonneg hC (norm_nonneg a)]
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold parallelFirstModelDerivativeBudget;positivity)
  intro t
  rw [fderiv_eq_smul_deriv,hB.deriv]
  exact (norm_smul_le t _).trans ((mul_le_mul_of_nonneg_left hN (norm_nonneg t)).trans_eq (by ring))

theorem relative_radius_first_correction_derivative_bound (ell : X →L[ℝ] ℝ) (P : ℝ)
    (hP : 0 ≤ P) (hEll : ‖ell‖ ≤ P) :
    ‖fderiv ℝ (fun t : ℝ => radialCorrectionCovectorL ((1+t) • ell)) 0‖ ≤ 6*P := by
  have hCurve : HasDerivAt (fun t : ℝ => (1+t) • ell) ell 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_add 1).smul_const ell using 1 <;> simp
  have hB := radialCorrectionCovectorL.hasFDerivAt.comp_hasDerivAt (0:ℝ) hCurve
  change HasDerivAt (fun t : ℝ => radialCorrectionCovectorL ((1+t) • ell))
    (radialCorrectionCovectorL ell) 0 at hB
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro t
  rw [fderiv_eq_smul_deriv,hB.deriv]
  have hN : ‖radialCorrectionCovectorL ell‖ ≤ 6*P :=
    (norm_radialCorrectionCovectorL_apply_le ell).trans (mul_le_mul_of_nonneg_left hEll (by norm_num))
  exact (norm_smul_le t _).trans ((mul_le_mul_of_nonneg_left hN (norm_nonneg t)).trans_eq (by ring))

end ShrinkingSpheres
