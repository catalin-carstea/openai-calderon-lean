module

public import Proof.Manuscript.MovingTraceSymbols
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public section

noncomputable section
set_option maxHeartbeats 1900000

open MeasureTheory Set Filter Real Complex FourierTransform
open scoped ContDiff SchwartzMap InnerProductSpace FourierTransform

namespace CalderonPaper

variable {d : ℕ}

@[expose] def compactSmoothSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) : 𝓢(E, ℂ) where
  toFun := f
  smooth' := hf
  decay' := by
    intro k n
    have hC : Continuous (fun x => ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖) :=
      (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by simp)).norm
    obtain ⟨A,hA⟩ := hK.isCompact.exists_bound_of_continuousOn hC.continuousOn
    refine ⟨max A 0,fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · exact ((le_abs_self _).trans (hA x hx)).trans (le_max_left _ _)
    · have hZ : iteratedFDeriv ℝ n f x = 0 := by
        by_contra h
        exact hx (support_iteratedFDeriv_subset n h)
      simp [hZ]

@[simp]
theorem compactSmoothSchwartz_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) (x : E) :
    compactSmoothSchwartz hf hK x = f x := rfl

theorem angularFourierPhase_norm (x ξ : AngularCoordinates d) : ‖angularFourierPhase x ξ‖ = 1 := by
  unfold angularFourierPhase
  rw [Complex.norm_exp]
  simp

theorem angularFourierTransform_eq (f : AngularCoordinates d → ℂ) :
    angularFourierTransform f = 𝓕 f := by
  funext ξ
  rw [Real.fourier_eq']
  unfold angularFourierTransform
  apply integral_congr_ae
  filter_upwards with x
  simp only [angularFourierPhase,inner_neg_left, smul_eq_mul,Complex.ofReal_neg,neg_mul,mul_neg]

theorem angularFourierInverse_eq (f : AngularCoordinates d → ℂ) (x : AngularCoordinates d) :
    (∫ ξ, angularFourierPhase x ξ * f ξ) = 𝓕⁻ f x := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [angularFourierPhase,smul_eq_mul,real_inner_comm x ξ]

theorem angularFourierTransform_integrable_norm_weight (f : AngularCoordinates d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) (k : ℕ) :
    Integrable (fun ξ => ‖ξ‖^k * ‖angularFourierTransform f ξ‖) := by
  rw [angularFourierTransform_eq]
  let F := compactSmoothSchwartz hf hK
  have hEq : ((𝓕 F : 𝓢(AngularCoordinates d, ℂ)) : AngularCoordinates d → ℂ) = 𝓕 f :=
    SchwartzMap.fourier_coe F
  rw [← hEq]
  exact (𝓕 F).integrable_pow_mul volume k

theorem angularFourierTransform_continuous (f : AngularCoordinates d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) :
    Continuous (angularFourierTransform f) := by
  rw [angularFourierTransform_eq]
  let F := compactSmoothSchwartz hf hK
  exact (𝓕 F).continuous

theorem angularFourier_inversion (f : AngularCoordinates d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) (x : AngularCoordinates d) :
    Integrable f ∧
      Integrable (fun ξ => angularFourierPhase x ξ * angularFourierTransform f ξ) ∧
      (∫ ξ, angularFourierPhase x ξ * angularFourierTransform f ξ) = f x := by
  rw [angularFourierInverse_eq,angularFourierTransform_eq]
  let F := compactSmoothSchwartz hf hK
  have hInt : Integrable (𝓕 f) := (𝓕 F).integrable
  refine ⟨F.integrable,hInt.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_),?_⟩
  · exact ((show Continuous (fun ξ => angularFourierPhase x ξ) by unfold angularFourierPhase; fun_prop).mul
      (𝓕 F).continuous).aestronglyMeasurable
  · rw [norm_mul,angularFourierPhase_norm,one_mul]
  · exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable hInt) x

end CalderonPaper
