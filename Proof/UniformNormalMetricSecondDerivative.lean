import Proof.NormalMetricSecondDerivativeBounds
import Proof.UniformNormalMetricDerivative
import Proof.FirstMetricNormalDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def normalMetricAngularSecondDerivativeBudget {m : ℕ} (hm : 4 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  9*(16*|M ⟨2,by omega⟩|+20*|M ⟨1,by omega⟩| *backgroundSecondNormalVariationBudget (by omega) K M+
    4*K*backgroundThirdNormalVariationBudget hm K M+
    2*K*(backgroundSecondNormalVariationBudget (by omega) K M)^2)*K^4

/-- Second standard-angular derivatives of the genuine normalized metric are
    uniformly O(radius squared), on every fixed enlarged normal ball. -/
theorem uniform_framed_normal_metric_second_derivative {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fderiv ℝ (fun w => framedNormalMetric g d.frame d.expMap y (d.radius y) w i j)) z‖ ≤
        normalMetricAngularSecondDerivativeBudget hm K M*(d.radius y)^2 := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  refine ⟨min η (ρ/(2*(L+1))),lt_min hη (div_pos hρ (by positivity)),?_⟩
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
  have hPack := hControl floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy (frameVector d.frame y z) hw
  let r := d.radius y
  let v := r • frameVector d.frame y z
  let J := normalVerticalJacobian d.expMap y v
  let N2 := backgroundSecondNormalVariationBudget (show 3 ≤ m by omega) K M
  let N3 := backgroundThirdNormalVariationBudget hm K M
  let P := 9*(16*|M ⟨2,by omega⟩|+20*|M ⟨1,by omega⟩| *N2+4*K*N3+2*K*N2^2)
  let B : X → ℝ := fun x => metricPair g (d.expMap (y,x))
    (normalVerticalJacobian d.expMap y x (d.frame y i))
    (normalVerticalJacobian d.expMap y x (d.frame y j))
  let T : X →L[ℝ] X := r • frameVectorLinear d.frame y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hN2 : 0 ≤ N2 := by
    dsimp [N2,backgroundSecondNormalVariationBudget,secondNormalVariationBudget,
      backgroundSecondConnectionBudget,secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hN3 : 0 ≤ N3 := by
    dsimp [N3,backgroundThirdNormalVariationBudget,thirdNormalVariationBudget,secondNormalVariationBudget,
      backgroundThirdConnectionBudget,thirdConnectionBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hP : 0 ≤ P := by dsimp [P];positivity
  have hεR : ε*(L+1) ≤ ρ/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*(L+1) by positivity)).mp (hSmall.trans (min_le_right _ _))
    nlinarith only [hh]
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hrL : r*L < ρ := by
    have hh := mul_le_mul_of_nonneg_right hrε hL
    have hh' : ε*L ≤ ε*(L+1) := mul_le_mul_of_nonneg_left (by linarith : L ≤ L+1) hε
    exact (hh.trans hh').trans_lt (hεR.trans_lt (half_lt_self hρ))
  have hSq : (r*L)^2 < (max ρ r)^2 :=
    (sq_lt_sq₀ (mul_nonneg hr.le hL) (hρ.le.trans (le_max_left _ _))).2
      (hrL.trans_le (le_max_left _ _))
  have hStrict : metricPair d.γ y v v < (max ρ r)^2 := by
    have hUpper : metricPair d.γ y (frameVector d.frame y z) (frameVector d.frame y z) ≤ L^2 := hw
    have hScaled : metricPair d.γ y v v ≤ (r*L)^2 := by
      dsimp only [v]
      rw [metricPair_smul_left,metricPair_smul_right]
      have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg r)
      nlinarith only [hh]
    exact hScaled.trans_lt hSq
  have hRadius : ContinuousOn (fun x => max ρ (d.radius x)) Y := by
    intro x hx
    have hRad : ContinuousAt d.radius x :=
      (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).continuousAt
    have hMax : ContinuousAt (fun z : X => max ρ (d.radius z)) x := continuousAt_const.max hRad
    exact hMax.continuousWithinAt
  have hJn : ‖J‖ ≤ 2 := by
    calc
      _ = ‖(J-ContinuousLinearMap.id ℝ X)+ContinuousLinearMap.id ℝ X‖ := by rw [sub_add_cancel]
      _ ≤ ‖J-ContinuousLinearMap.id ℝ X‖+‖ContinuousLinearMap.id ℝ X‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+1 := add_le_add hPack.2.2.2.1 ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  have hMetric1 (a b : I) : ‖fderiv ℝ (fun x => g x a b) (d.expMap (y,v))‖ ≤ |M ⟨1,by omega⟩| := by
    have hh := hd.1.2.2.2.2.1 g hmem ⟨1,by omega⟩ a b _ hPack.2.1
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (le_abs_self _)
  have hMetric2 (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) (d.expMap (y,v))‖ ≤ |M ⟨2,by omega⟩| := by
    have hh := hd.1.2.2.2.2.1 g hmem ⟨2,by omega⟩ a b _ hPack.2.1
    rw [norm_iteratedFDeriv_two_eq_nested] at hh
    exact hh.trans (le_abs_self _)
  have hFrameNorm (a : I) : ‖d.frame y a‖ ≤ K := by
    have hs : d.frame y a ∈ sphereAt d.γ y := by
      change metricPair d.γ y (d.frame y a) (d.frame y a) = 1
      simpa using hFrame a a
    have hh := hd.1.1.sphere_norm_sq_bound hKpos hcenter hs
    apply (sq_le_sq₀ (norm_nonneg _) hKpos.le).mp
    nlinarith only [hh,hK]
  have hTNorm : ‖T‖ ≤ r*K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hd.1.1.norm_frameVectorLinear_le hK hcenter d.frame hFrame) hr.le
  have hB2 : ‖fderiv ℝ (fderiv ℝ B) v‖ ≤ P*K^2 := by
    have hb := hd.1.normal_metric_velocity_second_derivative_bound hY hΩ hKpos hm hd.2.1 hRadius hy v
      (d.frame y i) (d.frame y j) hStrict hPack.1.2 hJn g hEll
      |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _) hMetric1 hMetric2
    exact hb.trans ((show P*‖d.frame y i‖*‖d.frame y j‖ ≤ P*K*K by
      gcongr <;> exact hFrameNorm _).trans_eq (by ring))
  have hE : ContDiffAt ℝ ∞ (fun x : X => d.expMap (y,x)) v :=
    hPack.2.2.1.comp v (contDiffAt_const.prodMk contDiffAt_id)
  have hJ : ContDiffAt ℝ ∞ (normalVerticalJacobian d.expMap y) v :=
    hd.2.1.contDiffAt_normalVerticalJacobian hy v (interior_subset hPack.1.1)
  have hB : ContDiffAt ℝ ∞ B v := by
    have hG (a b : I) : ContDiffAt ℝ ∞ (fun x => g (d.expMap (y,x)) a b) v := by
      have hgi : ContDiffAt ℝ ∞ (fun x : X => g x a b) (d.expMap (y,v)) :=
        (hEll.1 a b).contDiffAt (hΩ.mem_nhds hPack.2.1)
      exact hgi.comp v hE
    have hU (a b : I) : ContDiffAt ℝ ∞ (fun x => normalVerticalJacobian d.expMap y x (d.frame y a) b) v :=
      (EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.contDiffAt.comp v (hJ.clm_apply contDiffAt_const)
    exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ((hG a b).mul (hU i a)).mul (hU j b)))
  have hInputDerivative : fderiv ℝ (T : X → X) = (fun _ => T) := by
    funext x
    exact T.hasFDerivAt.fderiv
  have hb := norm_second_fderiv_comp_at (T : X → X) B z T.contDiff.contDiffAt
    (show ContDiffAt ℝ ∞ B (T z) from hB)
  rw [hInputDerivative,fderiv_const_apply,norm_zero,mul_zero,zero_add] at hb
  change ‖fderiv ℝ (fderiv ℝ (fun w => framedNormalMetric g d.frame d.expMap y r w i j)) z‖ ≤ _
  have hFun : (B ∘ T) = (fun w => framedNormalMetric g d.frame d.expMap y r w i j) := rfl
  rw [hFun] at hb
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ B) v‖*‖T‖^2 := hb
    _ ≤ (P*K^2)*(r*K)^2 := by gcongr
    _ = _ := by dsimp only [normalMetricAngularSecondDerivativeBudget,P,N2,N3,r];ring

end ShrinkingSpheres
