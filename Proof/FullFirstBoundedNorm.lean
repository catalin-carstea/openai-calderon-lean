import Proof.FullFirstScalarForm
import Proof.RadialScalarEndpointBounds
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

lemma norm_radius_weighted_sum_three_small {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r ε β B F H : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hβ : 0 < β)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hH : 0 ≤ H) (hrβ : r*β ≤ ε)
    (c : I → ℝ) (A Z : I → E) (hc : ∀ i,|c i| ≤ B)
    (hA : ∀ i,‖A i‖ ≤ F) (hZ : ∀ i,‖Z i‖ ≤ H*r^2) :
    ‖r • (∑ i : I,c i • (A i+Z i))‖ ≤ 3*B*(F+H)*ε/β := by
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hEach (i : I) : ‖A i+Z i‖ ≤ F+H :=
    (norm_add_le _ _).trans (add_le_add (hA i)
      ((hZ i).trans ((mul_le_mul_of_nonneg_left hr2 hH).trans_eq (mul_one _))))
  have hSum := norm_weighted_sum_three_le c (fun i => A i+Z i) B (F+H) hB hc hEach
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  apply (le_div_iff₀ hβ).2
  calc
    _ ≤ (r*(3*B*(F+H)))*β := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSum hr) hβ.le
    _ = (3*B*(F+H))*(r*β) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrβ (by positivity)

def fullFirstBoundedBudget (Q0 : SmoothCoefficientJets 2) (CQ K M0 M1 CC : ℝ) : ℝ :=
  6*(9*(K+1)*K^2)*
    ((firstCorrectionGradeBound (-(1/2:ℝ)) K M1+firstCorrectionGradeBound (1/2:ℝ) K M1)+
      3*K*radialScalarEndpointBudget CQ*(firstErrorScalarFixedBudget Q0*(27* |M0| *K+3*K+15*CC)))

lemma fullFirstBoundedBudget_nonneg (Q0 : SmoothCoefficientJets 2) (CQ K M0 M1 CC : ℝ)
    (hK : 1 ≤ K) (hCC : 0 ≤ CC) : 0 ≤ fullFirstBoundedBudget Q0 CQ K M0 M1 CC := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ : 0 ≤ firstErrorScalarFixedBudget Q0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hFm := firstCorrectionGradeBound_nonneg (-(1/2:ℝ)) K M1
  have hFp := firstCorrectionGradeBound_nonneg (1/2:ℝ) K M1
  have hCZ := (radialScalarEndpointBudget_pos CQ).le
  unfold fullFirstBoundedBudget
  positivity

lemma NativeRelativeHorizontalTaylorData.norm_native_frame_first_bounded
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCQ : 0 ≤ CQ)
    (Q0 : SmoothCoefficientJets 2) (hy : y ∈ Y) {CC CH : ℝ} (hCC : 0 ≤ CC)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    ‖nativeFrameFirstBoundedHalfL Q0 C i‖ ≤ (3*K*radialScalarEndpointBudget CQ*C1)*(d.radius y)^2 ∧
    ‖nativeFrameFirstBoundedNegativeL Q0 C i‖ ≤ (3*K*radialScalarEndpointBudget CQ*C1)*(d.radius y)^2 := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr1 : r ≤ 1 := ((radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hEll : ‖ell‖ ≤ CQ := by
    have hh := s.coefficients.firstCovectorJets (by norm_num) 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hN (a : I) : ‖nativeAxisNormalScalarCoefficient Q0 C a‖ ≤ C1*r^2 := by
    simpa only [nativeAxisNormalScalarCoefficient,norm_axis,mul_one] using
      hd.normal_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC (axis a) (C a)
  have hRadial (a : I) := norm_radialScalarBounded_endpoints_le CQ hCQ ell hEll
    (nativeAxisNormalScalarCoefficient Q0 C a) (C1*r^2) (mul_nonneg hC1 (sq_nonneg _)) (hN a)
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hCoeff (a : I) : |d.frame y i a| ≤ K :=
    hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hy) he i a
  constructor
  · exact (norm_weighted_sum_three_le (fun a => d.frame y i a)
      (fun a => radialScalarBoundedHalfL ell (nativeAxisNormalScalarCoefficient Q0 C a))
      K (CZ*(C1*r^2)) (zero_le_one.trans hK) hCoeff (fun a => (hRadial a).1)).trans_eq (by ring)
  · exact (norm_weighted_sum_three_le (fun a => d.frame y i a)
      (fun a => radialScalarBoundedNegativeL ell (nativeAxisNormalScalarCoefficient Q0 C a))
      K (CZ*(C1*r^2)) (zero_le_one.trans hK) hCoeff (fun a => (hRadial a).2)).trans_eq (by ring)

/-- BOTH compatible bounded corrections of the full actual first-base
coefficient have the uniform epsilon/beta norm weight. -/
lemma NativeRelativeHorizontalTaylorData.norm_full_first_bounded
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hΩ : IsOpen Ω) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCQ : 0 ≤ CQ)
    (Q0 : SmoothCoefficientJets 2) (hy : y ∈ Y) {CC CH : ℝ} (hCC : 0 ≤ CC)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    let CB := fullFirstBoundedBudget Q0 CQ K (M 0) (M ⟨1,by omega⟩) CC
    ‖fullFirstBoundedHalfL Q0 C j‖ ≤ CB*ε/beta d.γ d.radius y ∧
    ‖fullFirstBoundedNegativeL Q0 C j‖ ≤ CB*ε/beta d.γ d.radius y := by
  let r := d.radius y
  let β := beta d.γ d.radius y
  let B := 9*(K+1)*K^2
  let F := firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+
    firstCorrectionGradeBound (1/2:ℝ) K (M ⟨1,by omega⟩)
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let H := 3*K*radialScalarEndpointBudget CQ*C1
  let c := fun i : I => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hR := radius_bounds r β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hR.2.2.trans hε1
  have hrβ : r*β ≤ ε := hR.2.1.trans (div_le_self hε hf)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hF : 0 ≤ F := add_nonneg (firstCorrectionGradeBound_nonneg _ _ _) (firstCorrectionGradeBound_nonneg _ _ _)
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK))
    (radialScalarEndpointBudget_pos CQ).le) hC1
  have hc (i : I) : |c i| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add
      (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1
      (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy j i).2.1).trans_eq (by ring))
  have hFp (i : I) : ‖firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i‖ ≤ F :=
    (hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 _ hy i).trans
      (le_add_of_nonneg_left (firstCorrectionGradeBound_nonneg _ _ _))
  have hFn (i : I) : ‖firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i‖ ≤ F :=
    (hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 _ hy i).trans
      (le_add_of_nonneg_right (firstCorrectionGradeBound_nonneg _ _ _))
  have hZ := s.norm_native_frame_first_bounded hd hK hf hε hε1 hCQ Q0 hy hCC C
  constructor
  · exact (norm_radius_weighted_sum_three_small r ε β (2*B) F H hr.le hr1 hβ (by positivity) hF hH hrβ c
      (fun i => firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i) (nativeFrameFirstBoundedHalfL Q0 C)
      hc hFp (fun i => (hZ i).1)).trans_eq (by dsimp only [fullFirstBoundedBudget,B,F,H,C1];ring)
  · exact (norm_radius_weighted_sum_three_small r ε β (2*B) F H hr.le hr1 hβ (by positivity) hF hH hrβ c
      (fun i => firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i) (nativeFrameFirstBoundedNegativeL Q0 C)
      hc hFn (fun i => (hZ i).2)).trans_eq (by dsimp only [fullFirstBoundedBudget,B,F,H,C1];ring)
end ShrinkingSpheres
