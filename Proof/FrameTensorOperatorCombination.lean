import Proof.FrameAdjointLinearity
import Proof.MovingFrameSecond
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The same frame tensor combination at every genuine operator endpoint. -/
def frameTensorOperatorCombination (d : Data) (y b : X) (j : I)
    (F S : I → V →L[ℝ] W) : V →L[ℝ] W :=
  (∑ a : I,d.frame y j a • S a)-
    ∑ a : I,(connection d.γ y b (d.frame y j)) a • F a

lemma norm_frameTensorOperatorCombination_le (d : Data) (y b : X) (j : I)
    (F S : I → V →L[ℝ] W) {K CΓ C0 C1 : ℝ} (hK : 0 ≤ K) (hΓ : 0 ≤ CΓ)
    (he : ∀ a,|d.frame y j a| ≤ K)
    (hc : ∀ a,|(connection d.γ y b (d.frame y j)) a| ≤ CΓ)
    (hF : ∀ a,‖F a‖ ≤ C0) (hS : ∀ a,‖S a‖ ≤ C1) :
    ‖frameTensorOperatorCombination d y b j F S‖ ≤ 3*K*C1+3*CΓ*C0 := by
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_weighted_sum_three_le _ _ K C1 hK he hS)
    (norm_weighted_sum_three_le _ _ CΓ C0 hΓ hc hF))

/-- Shared radius-beta count for both the old coarse tensor estimate and
    the genuine low/high endpoint callers. -/
lemma frame_tensor_radius_beta_budget (K CΓ C0 C1 r β : ℝ)
    (hΓ : 0 ≤ CΓ) (hC0 : 0 ≤ C0) (hr : 0 ≤ r) (hβ : 1 ≤ β) :
    3*K*(C1*K*r*β)+3*(CΓ*K^2)*(C0*r) ≤
      (3*K^2*C1+3*CΓ*K^2*C0)*r*β := by
  have hGain : 3*(CΓ*K^2)*(C0*r) ≤ 3*(CΓ*K^2)*(C0*r)*β :=
    le_mul_of_one_le_right (by positivity) hβ
  exact (add_le_add le_rfl hGain).trans_eq (by ring)

variable {V0 V1 W0 W1 : Type*}
  [NormedAddCommGroup V0] [NormedSpace ℝ V0] [NormedAddCommGroup V1] [NormedSpace ℝ V1]
  [NormedAddCommGroup W0] [NormedSpace ℝ W0] [NormedAddCommGroup W1] [NormedSpace ℝ W1]

/-- Fixed genuine inclusion squares pass through the frame tensor formula. -/
lemma frameTensorOperatorCombination_compatible (d : Data) (y b : X) (j : I)
    (F0 S0 : I → V0 →L[ℝ] W0) (F1 S1 : I → V1 →L[ℝ] W1)
    (Iout : W0 →L[ℝ] W1) (Iin : V0 →L[ℝ] V1)
    (hF : ∀ a,Iout.comp (F0 a)=(F1 a).comp Iin)
    (hS : ∀ a,Iout.comp (S0 a)=(S1 a).comp Iin) :
    Iout.comp (frameTensorOperatorCombination d y b j F0 S0)=
      (frameTensorOperatorCombination d y b j F1 S1).comp Iin := by
  apply DFunLike.ext
  intro u
  simp only [frameTensorOperatorCombination,ContinuousLinearMap.comp_apply,
    _root_.sub_apply,_root_.sum_apply,_root_.smul_apply,map_sub,map_sum,map_smul]
  apply congrArg₂ (fun x z : W1 => x-z)
  · apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun z : W1 => d.frame y j a • z)
      (DFunLike.congr_fun (hS a) u)
  · apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun z : W1 => (connection d.γ y b (d.frame y j)) a • z)
      (DFunLike.congr_fun (hF a) u)
end ShrinkingSpheres
