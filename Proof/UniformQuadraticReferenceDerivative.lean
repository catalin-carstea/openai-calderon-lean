import Proof.NormalMetricQuadraticDerivative
import Proof.UniformNormalMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def normalReferenceMetricAngularDerivativeBudget {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  normalReferenceMetricDerivativeBudget K (243*K*|M ⟨1,by omega⟩|)
    (backgroundConnectionDerivativeBudget (by omega) K M) (backgroundSecondConnectionBudget hm K M)
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| *K^4*(L+1)

/-- The genuine reference normal metric has angular C1 error O(radius squared)
    on each fixed enlarged ball, uniformly over the admitted class. -/
theorem uniform_framed_reference_metric_derivative_quadratic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fun w => framedNormalMetric d.γ d.frame d.expMap y (d.radius y) w i j) z‖ ≤
        normalReferenceMetricAngularDerivativeBudget hm K M L*(d.radius y)^2 := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hcenter
  have hw := frameVector_mem_disk d.γ d.frame y z L hFrame hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  let r := d.radius y
  let v := r • frameVector d.frame y z
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget (by omega : 2 ≤ m) K M
  let E := backgroundSecondConnectionBudget hm K M
  let P := normalReferenceMetricDerivativeBudget K C D E |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
  let B : X → ℝ := fun x => metricPair d.γ (d.expMap (y,x))
    (normalVerticalJacobian d.expMap y x (d.frame y i)) (normalVerticalJacobian d.expMap y x (d.frame y j))
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget];positivity
  have hE : 0 ≤ E := by dsimp [E,backgroundSecondConnectionBudget,secondConnectionBudget];positivity
  have hP : 0 ≤ P := by
    dsimp [P,normalReferenceMetricDerivativeBudget,secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget]
    positivity
  have hMetric (x : X) (hx : x ∈ Ω) (a b : I) : ‖fderiv ℝ (fun z => d.γ z a b) x‖ ≤ |M ⟨1,by omega⟩| :=
    (hd.1.reference_fderiv_bound (by omega) hx a b).trans (le_abs_self _)
  have hMetric2 (x : X) (hx : x ∈ Ω) (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun z => d.γ z a b)) x‖ ≤ |M ⟨2,by omega⟩| :=
    (hd.1.reference_second_fderiv_bound (by omega) hx a b).trans (le_abs_self _)
  have hVNorm : ‖v‖ ≤ r*(K*(L+1)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hd.1.1.disk_norm_bound_radius hK hcenter hL hw) hr.le
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
  have hB : DifferentiableAt ℝ B v := metric_pair_comp_differentiableAt hΩ hd.1.1
    (fun x => d.expMap (y,x)) (fun x => normalVerticalJacobian d.expMap y x (d.frame y i))
    (fun x => normalVerticalJacobian d.expMap y x (d.frame y j)) v hPack.2.1 hF.differentiableAt
    (hJ.clm_apply (differentiableAt_const _)) (hJ.clm_apply (differentiableAt_const _))
  have hV : HasFDerivAt (fun x => r • frameVector d.frame y x) (r • frameVectorLinear d.frame y) z := by
    convert (r • frameVectorLinear d.frame y).hasFDerivAt using 1
    funext x
    simp only [_root_.smul_apply,frameVectorLinear_apply]
  have hComp := hB.hasFDerivAt.comp z hV
  change HasFDerivAt (fun x => framedNormalMetric d.γ d.frame d.expMap y r x i j)
    ((fderiv ℝ B v).comp (r • frameVectorLinear d.frame y)) z at hComp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by
    dsimp [normalReferenceMetricAngularDerivativeBudget];positivity) (sq_nonneg _))
  intro a
  rw [hComp.fderiv]
  change |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ _
  have hb := hd.2.1.normal_metric_velocity_derivative_small hΩ hd.1.1 hKpos hC hD hE (abs_nonneg _) (abs_nonneg _)
    (fun x hx => hd.1.connection_budget hKpos (by omega) hx)
    (fun x hx => hd.1.connection_derivative_budget hΩ hKpos (by omega) hx)
    (fun x hx => hd.1.connection_second_derivative_budget hΩ hKpos hm hx)
    hMetric hMetric2 hy v (d.frame y i) (d.frame y j) (r • frameVector d.frame y a)
    hPack.1.1 hPack.1.2 (hPack.2.2.2.1.trans (by norm_num))
  change |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ P*‖v‖*‖r • frameVector d.frame y a‖*‖d.frame y i‖*‖d.frame y j‖ at hb
  have hInput : ‖r • frameVector d.frame y a‖ ≤ r*(K*‖a‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hFrameVector a) hr.le
  have hh : |fderiv ℝ B v (r • frameVector d.frame y a)| ≤ P*(r*(K*(L+1)))*(r*(K*‖a‖))*K*K :=
    hb.trans (by gcongr;exact hFrameNorm i;exact hFrameNorm j)
  exact hh.trans_eq (by dsimp [normalReferenceMetricAngularDerivativeBudget,P,C,D,E,r];ring)

end ShrinkingSpheres
