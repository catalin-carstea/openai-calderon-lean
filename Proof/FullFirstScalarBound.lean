import Proof.FullFirstScalarForm
import Proof.PrincipalModelScalarBound
import Proof.TaylorScalarCoefficientCombinationBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def fullFirstScalarBudget (Q0 : SmoothCoefficientJets 2) (K M0 CC : ℝ) : ℝ :=
  (54*(K+1)*K^2+216*K^2)*firstErrorScalarFixedBudget Q0+
    18*(9*(K+1)*K^2)*K*(firstErrorScalarFixedBudget Q0*(27* |M0| *K+3*K+15*CC))

lemma fullFirstScalarBudget_nonneg (Q0 : SmoothCoefficientJets 2) (K M0 CC : ℝ)
    (hK : 1 ≤ K) (hCC : 0 ≤ CC) : 0 ≤ fullFirstScalarBudget Q0 K M0 CC := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ : 0 ≤ firstErrorScalarFixedBudget Q0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  unfold fullFirstScalarBudget
  positivity

lemma Admissible.native_frame_first_scalar_weighted_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Q0 : SmoothCoefficientJets 2) {y : X} (hy : y ∈ Y)
    {CC CH : ℝ} (hCC : 0 ≤ CC)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    (∑ k,taylorGeneratorWeight (d.radius y) k*‖nativeFrameFirstScalarCoefficients Q0 C i k‖) ≤
      (3*K*(firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)))*(d.radius y) := by
  let r := d.radius y
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr1 : r ≤ 1 := ((radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hQ (a : I) : (∑ k,taylorGeneratorWeight r k*‖actualFirstErrorGeneratorCoefficients Q0 (C a) k‖) ≤ C1*r := by
    simpa only [actualFirstErrorGeneratorCoefficients,C1,r,norm_axis,mul_one] using
      hd.first_error_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC (axis a) (C a)
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hCoeff (a : I) : |d.frame y i a| ≤ K :=
    hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hy) he i a
  exact (weighted_three_taylor_scalar_combination r (fun a => actualFirstErrorGeneratorCoefficients Q0 (C a))
    (fun a => d.frame y i a) K (C1*r) (zero_le_one.trans hK) hCoeff hQ).trans_eq (by ring)

/-- The complete first-base scalar coefficient family has uniform
epsilon/beta weight, including all SAME frame trace-error coefficients. -/
lemma Admissible.full_first_scalar_weighted_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Q0 : SmoothCoefficientJets 2) {y : X} (hy : y ∈ Y)
    {CC CH : ℝ} (hCC : 0 ≤ CC)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    (∑ a,taylorGeneratorWeight (d.radius y) a*‖fullFirstScalarCoefficients Q0 C j a‖) ≤
      fullFirstScalarBudget Q0 K (M 0) CC*ε/beta d.γ d.radius y := by
  let r := d.radius y
  let β := beta d.γ d.radius y
  let W := fun Q : TaylorGeneratorIndex → ClosedCoefficientJets 3 => ∑ a,taylorGeneratorWeight r a*‖Q a‖
  let B := 9*(K+1)*K^2
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CP := 18*B*K*C1
  let c := fun i : I => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i
  let Qs := ∑ i : I,c i • nativeFrameFirstScalarCoefficients Q0 C i
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hRad := radius_bounds r β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hRad.2.2.trans hε1
  have hrβ : r*β ≤ ε := hRad.2.1.trans (div_le_self hε hf)
  have hr2β : r^2*β ≤ ε := by nlinarith [mul_le_mul_of_nonneg_right hr1 (mul_nonneg hr.le hβ.le)]
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCoeff (i : I) : |c i| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add
      (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1
      (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy j i).2.1).trans_eq (by ring))
  have hFrame (i : I) : W (nativeFrameFirstScalarCoefficients Q0 C i) ≤ 3*K*C1*r :=
    hd.native_frame_first_scalar_weighted_bound hK hf hε hε1 Q0 hy hCC C i
  have hQs : W Qs ≤ CP*r :=
    (weighted_three_taylor_scalar_combination r (nativeFrameFirstScalarCoefficients Q0 C) c
      (2*B) (3*K*C1*r) (by positivity) hCoeff hFrame).trans_eq (by dsimp only [CP];ring)
  have hScaled0 : W (r • Qs) ≤ CP*r^2 := by
    have hSmul : W (r • Qs)=r*W Qs := by
      simpa only [W,Pi.smul_apply,abs_of_pos hr] using taylor_scalar_weighted_sum_smul r r Qs
    rw [hSmul]
    exact (mul_le_mul_of_nonneg_left hQs hr.le).trans_eq (by ring)
  have hScaled : W (r • Qs) ≤ CP*ε/β := by
    apply (le_div_iff₀ hβ).2
    calc
      _ ≤ (CP*r^2)*β := mul_le_mul_of_nonneg_right hScaled0 hβ.le
      _ = CP*(r^2*β) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr2β hCP
  have hAdd := taylor_scalar_weighted_sum_add_le r (principalModelScalarCoefficients Q0 d y j) (r • Qs)
  have hModel := hd.principal_model_scalar_weighted_bound hK hf hε hε1 Q0 hy j
  exact hAdd.trans ((add_le_add hModel hScaled).trans_eq (by dsimp only [fullFirstScalarBudget,CP,B,C1];ring))
end ShrinkingSpheres
