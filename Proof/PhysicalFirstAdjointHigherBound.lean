import Proof.PhysicalFirstAdjointHigherFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma norm_firstDerivativeAdjointHigherFamily_small {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (AE : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    {CR CA : ℝ} (hCR : 0 ≤ CR) (hCA : 0 ≤ CA)
    {y : X} (hy : y ∈ Y) (hAR : ∀ i,‖AR i‖ ≤ CR)
    (hAE : ∀ i,‖AE i y‖ ≤ CA*d.radius y) (j : I) :
    ‖P.firstDerivativeAdjointHigherFamily AR AE y j‖ ≤
      (108*(K+1)*K^2+54*K^2*CR+
        54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CA))*ε/beta d.γ d.radius y := by
  let B := 9*(K+1)*K^2
  let F := firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)
  let β := beta d.γ d.radius y
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hF : 0 ≤ F := firstCorrectionGradeBound_nonneg _ _ _
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hrB := radius_bounds (d.radius y) β floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hr1 : d.radius y ≤ 1 := hrB.2.2.trans hε1
  have hrβ : d.radius y*β ≤ ε := hrB.2.1.trans (div_le_self hε hf)
  have hrβ1 : d.radius y*β ≤ 1 := hrβ.trans hε1
  have hQ (i k : I) : |q i k| ≤ B := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i k).2.1
  have hQS (i : I) : |q i j+q j i| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add (hQ i j) (hQ j i)).trans_eq (by ring))
  have hT (i : I) : |(q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y| ≤ 2*B*(ε/β) := by
    rw [abs_mul]
    exact mul_le_mul (hQS i) (hd.scaled_frame_logRadius_beta_small hf hy i) (abs_nonneg _) (by positivity)
  have hD : ‖∑ i : I,((q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y) • degreeHigherL‖ ≤ 12*B*ε/β := by
    exact (norm_weighted_sum_three_le _ (fun _ : I => degreeHigherL) (2*B*(ε/β)) 2
      (by positivity) hT (fun _ => norm_degreeHigherL_le_two)).trans_eq (by ring)
  have hDiff (i : I) : |q i j-(if i=j then 1 else 0)| ≤ 9*K^2*ε/β := by
    apply (le_div_iff₀ hβ).2
    calc
      _ ≤ (9*K^2*ε*d.radius y)*β := mul_le_mul_of_nonneg_right
        (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).1 hβ.le
      _ = (9*K^2*ε)*(d.radius y*β) := by ring
      _ ≤ (9*K^2*ε)*1 := mul_le_mul_of_nonneg_left hrβ1 (by positivity)
      _ = _ := mul_one _
  have hR : ‖(2:ℝ) • (∑ i : I,(q i j-(if i=j then 1 else 0)) • AR i)‖ ≤ 54*K^2*CR*ε/β := by
    have h := norm_weighted_sum_three_le _ AR (9*K^2*ε/β) CR (by positivity) hDiff hAR
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hC (i : I) : ‖firstFrameCorrectionAdjointHigherL d y i+AE i y‖ ≤ F+CA := by
    apply (norm_add_le _ _).trans
    exact add_le_add ((norm_firstFrameCorrectionAdjointHigherL_le _ _ _).trans
      (hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 _ hy i))
      ((hAE i).trans ((mul_le_mul_of_nonneg_left hr1 hCA).trans_eq (mul_one _)))
  have hE : ‖d.radius y • (∑ i : I,(q i j+q j i) •
      (firstFrameCorrectionAdjointHigherL d y i+AE i y))‖ ≤ 6*B*(F+CA)*ε/β := by
    have h := norm_weighted_sum_three_le _ _ (2*B) (F+CA) (by positivity) hQS hC
    have hN : ‖d.radius y • (∑ i : I,(q i j+q j i) •
        (firstFrameCorrectionAdjointHigherL d y i+AE i y))‖ ≤ 6*B*(F+CA)*d.radius y := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left h hr.le).trans_eq (by ring)
    apply (le_div_iff₀ hβ).2
    calc
      _ ≤ (6*B*(F+CA)*d.radius y)*β := mul_le_mul_of_nonneg_right hN hβ.le
      _ = (6*B*(F+CA))*(d.radius y*β) := by ring
      _ ≤ (6*B*(F+CA))*ε := mul_le_mul_of_nonneg_left hrβ (by positivity)
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add hD hR)) hE).trans_eq
    (by dsimp only [B,F];ring))
end PhysicalPrincipalData
end ShrinkingSpheres
