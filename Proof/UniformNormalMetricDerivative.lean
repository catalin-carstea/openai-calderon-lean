import Proof.NormalMetricDerivative
import Proof.UniformNormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def normalMetricAngularDerivativeBudget {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  (72*|M ⟨1,by omega⟩| +4*K*backgroundSecondNormalVariationBudget hm K M)*K^3

/-- The actual rescaled metric has uniformly O(radius) angular first derivatives
    on every fixed enlarged ball, for every admitted radius profile. -/
theorem uniform_framed_normal_metric_derivative {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fun w => framedNormalMetric g d.frame d.expMap y (d.radius y) w i j) z‖ ≤
        normalMetricAngularDerivativeBudget hm K M*d.radius y := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hcenter
  have hEll : Elliptic Ω K g := by
    have hh := hmem
    simp only [mem_insert_iff,mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hd.1.1
    · exact hd.1.2.1
  have hw := frameVector_mem_disk d.γ d.frame y z L hFrame hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  let r := d.radius y
  let v := r • frameVector d.frame y z
  let J := normalVerticalJacobian d.expMap y v
  let N := backgroundSecondNormalVariationBudget hm K M
  let P := 72*|M ⟨1,by omega⟩| +4*K*N
  let B : X → ℝ := fun x => metricPair g (d.expMap (y,x))
    (normalVerticalJacobian d.expMap y x (d.frame y i))
    (normalVerticalJacobian d.expMap y x (d.frame y j))
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hN : 0 ≤ N := by
    dsimp [N,backgroundSecondNormalVariationBudget,secondNormalVariationBudget,
      backgroundSecondConnectionBudget,secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hJn : ‖J‖ ≤ 2 := by
    calc
      _ = ‖(J-ContinuousLinearMap.id ℝ X)+ContinuousLinearMap.id ℝ X‖ := by rw [sub_add_cancel]
      _ ≤ ‖J-ContinuousLinearMap.id ℝ X‖+‖ContinuousLinearMap.id ℝ X‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+1 := add_le_add hPack.2.2.2.1 (ContinuousLinearMap.norm_id_le)
      _ ≤ 2 := by norm_num
  have hDJ : ‖fderiv ℝ (normalVerticalJacobian d.expMap y) v‖ ≤ N :=
    hd.1.normalVerticalJacobian_derivative_bound hΩ hKpos hm hd.2.1 hy v hPack.1.1 hPack.1.2
  have hMetric (a b : I) : ‖fderiv ℝ (fun x => g x a b) (d.expMap (y,v))‖ ≤ |M ⟨1,by omega⟩| := by
    have hh := hd.1.2.2.2.2.1 g hmem ⟨1,by omega⟩ a b _ hPack.2.1
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (le_abs_self _)
  have hFrameNorm (a : I) : ‖d.frame y a‖ ≤ K := by
    have hs : d.frame y a ∈ sphereAt d.γ y := by
      change metricPair d.γ y (d.frame y a) (d.frame y a) = 1
      simpa using hFrame a a
    have hh := hd.1.1.sphere_norm_sq_bound hKpos hcenter hs
    apply (sq_le_sq₀ (norm_nonneg _) hKpos.le).mp
    nlinarith only [hh,hK]
  have hFrameVector (a : X) : ‖frameVector d.frame y a‖ ≤ K*‖a‖ := by
    have hh := (hd.1.1.frameVector_norm_sq_bounds hKpos hcenter d.frame hFrame a).2
    have hKsq : K ≤ K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKpos.le (norm_nonneg a))).mp
    have hMul := mul_le_mul_of_nonneg_right hKsq (sq_nonneg ‖a‖)
    nlinarith only [hh,hMul]
  have hF := hd.2.1.hasFDerivAt_velocity_slice hy v (interior_subset hPack.1.1)
  have hJ := (hd.2.1.contDiffAt_normalVerticalJacobian hy v (interior_subset hPack.1.1)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B v := metric_pair_comp_differentiableAt hΩ hEll
    (fun x => d.expMap (y,x)) (fun x => normalVerticalJacobian d.expMap y x (d.frame y i))
    (fun x => normalVerticalJacobian d.expMap y x (d.frame y j)) v hPack.2.1 hF.differentiableAt
    (hJ.clm_apply (differentiableAt_const _)) (hJ.clm_apply (differentiableAt_const _))
  have hV : HasFDerivAt (fun x => r • frameVector d.frame y x) (r • frameVectorLinear d.frame y) z := by
    convert (r • frameVectorLinear d.frame y).hasFDerivAt using 1
    funext x
    simp only [_root_.smul_apply,frameVectorLinear_apply]
  have hComp := hB.hasFDerivAt.comp z hV
  change HasFDerivAt (fun x => framedNormalMetric g d.frame d.expMap y r x i j)
    ((fderiv ℝ B v).comp (r • frameVectorLinear d.frame y)) z at hComp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by
    dsimp [normalMetricAngularDerivativeBudget]; positivity) hr.le)
  intro a
  rw [hComp.fderiv]
  change |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ _
  have hb := hd.2.1.normal_metric_velocity_derivative_bound hΩ hEll hKpos (abs_nonneg _)
    (show 0 ≤ (2:ℝ) by norm_num) hN hy v (d.frame y i) (d.frame y j)
    (r • frameVector d.frame y a) (interior_subset hPack.1.1) hMetric hJn hDJ
  have hCoeff : 9*|M ⟨1,by omega⟩| *(2:ℝ)^3+2*K*2*N = P := by dsimp [P]; ring
  change |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ _ at hb
  rw [hCoeff] at hb
  have hInput : ‖r • frameVector d.frame y a‖ ≤ r*(K*‖a‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hFrameVector a) hr.le
  have hh : |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ P*(r*(K*‖a‖))*K*K :=
    hb.trans (by gcongr; exact hFrameNorm i; exact hFrameNorm j)
  exact hh.trans_eq (by dsimp [normalMetricAngularDerivativeBudget,P,N,r]; ring)

end ShrinkingSpheres
