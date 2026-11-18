import Proof.NormalMapSecondTaylor
import Proof.NormalVelocitySecondTaylor
import Proof.QuadraticMetricPullback
import Proof.MetricDensityBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def metricFirstJetMatrix (g : MetricField) (y v : X) : Mat :=
  fun i j => fderiv ℝ (fun x => g x i j) y v

lemma metricBilinear_firstJet (g : MetricField) (y v : X) :
    metricBilinear (fun _ => metricFirstJetMatrix g y v) 0 = metricDifferential g y v := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  rw [metricBilinear_apply,metricDifferential_apply]
  rfl

lemma norm_metricDifferential_apply_le (g : MetricField) (y v : X) (M1 : ℝ)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M1) :
    ‖metricDifferential g y v‖ ≤ (9*M1)*‖v‖ := by
  rw [← metricBilinear_firstJet]
  have hEntries (i j : I) : |metricFirstJetMatrix g y v i j| ≤ M1*‖v‖ :=
    ((fderiv ℝ (fun x => g x i j) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hD i j) (norm_nonneg v))
  exact (metricBilinear_norm_of_entry_bound _ _ (M1*‖v‖) hEntries).trans_eq (by ring)

lemma NormalCoordinates.metricBilinear_second_taylor_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C M1 M2 : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hΓ : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hD : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M1)
    (hD2 : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fderiv ℝ (fun z => g z i j)) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) :
    ‖metricBilinear g (expMap (y,v))-metricBilinear g y-metricDifferential g y v‖ ≤
      (9*((M2+M1*C)*K^2))*‖v‖^2 := by
  let A := g (expMap (y,v))-g y-metricFirstJetMatrix g y v
  have hEntries (i j : I) : |A i j| ≤ ((M2+M1*C)*K^2)*‖v‖^2 := by
    have hb := hN.map_second_taylor_bound hΩ hg hK hC hM1 hM2 hΓ (fun z => g z i j)
      (hg.1 i j) (fun x hx => hD x hx i j) (fun x hx => hD2 x hx i j) hy v hv
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    simpa only [A,metricFirstJetMatrix,Matrix.sub_apply,one_smul,one_pow,mul_one,Real.norm_eq_abs] using hb
  have hEq : metricBilinear g (expMap (y,v))-metricBilinear g y-metricDifferential g y v =
      metricBilinear (fun _ : X => A) 0 := by
    rw [← metricBilinear_firstJet]
    simp only [metricBilinear,A,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
  rw [hEq]
  exact (metricBilinear_norm_of_entry_bound _ _ _ hEntries).trans_eq (by ring)

lemma NormalCoordinates.normalVerticalJacobian_second_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1) :
    ‖normalVerticalJacobian expMap y v-(ContinuousLinearMap.id ℝ X-connectionBilinear g y v)‖ ≤
      normalVelocitySecondErrorBudget K C D*‖v‖^2 := by
  have hBudget : 0 ≤ normalVelocitySecondErrorBudget K C D := by
    dsimp [normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hBudget (sq_nonneg _))
  intro a
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hvT : (1:ℝ) • v ∈ disk g y (R y) := by simpa only [one_smul] using interior_subset hv
  have hError := hN.position_variation_second_error hΩ hg hK hC hD hΓ0 hΓ1 hy v a hv hv1 ht
  have hEq := hN.variation_position_eq hy v a 1 hvT
  simp only [one_smul,one_pow,mul_one] at hEq hError
  rw [hEq] at hError
  change ‖normalVerticalJacobian expMap y v a-(a-connectionBilinear g y v a)‖ ≤ _
  convert hError using 1
  congr 1
  rw [connectionBilinear_apply]
  abel

def normalReferenceMetricSecondBudget (K C D M1 M2 : ℝ) : ℝ :=
  4*(9*((M2+M1*C)*K^2))+(9*K+9*M1)*normalVelocitySecondErrorBudget K C D*(3+C)+
    9*K*C^2+9*M1*(2*C+C^2)

/-- The actual reference normal pullback has a uniform quadratic error. Metric
    compatibility cancels its complete first jet, not just its radial value at zero. -/
theorem NormalCoordinates.normalPullbackMetric_quadratic_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D M1 M2 : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hDg : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M1)
    (hDg2 : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fderiv ℝ (fun z => g z i j)) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u w : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    (hSmall : ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ X‖ ≤ 1) :
    |metricPair g (expMap (y,v)) (normalVerticalJacobian expMap y v u)
      (normalVerticalJacobian expMap y v w)-metricPair g y u w| ≤
      normalReferenceMetricSecondBudget K C D M1 M2*‖v‖^2*‖u‖*‖w‖ := by
  let J := normalVerticalJacobian expMap y v
  have hyΩ := hN.center_mem hy
  have hL0 := metricBilinear_norm_of_entry_bound g y K (hg.entry_abs_bound hK hyΩ)
  have hL1 := norm_metricDifferential_apply_le g y v M1 (hDg y hyΩ)
  have hG : ‖connectionBilinear g y v‖ ≤ C*‖v‖ :=
    ((connectionBilinear g y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hΓ0 y hyΩ) (norm_nonneg v))
  have hJ : ‖J‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro a
    have hDiff := ((J-ContinuousLinearMap.id ℝ X).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right hSmall (norm_nonneg a))
    have hEq : J a = (J a-a)+a := by abel
    have hh := norm_add_le (J a-a) a
    rw [← hEq] at hh
    change ‖J a-a‖ ≤ 1*‖a‖ at hDiff
    nlinarith only [hh,hDiff]
  have hJError := hN.normalVerticalJacobian_second_error hΩ hg hK hC hD hΓ0 hΓ1 hy v hv hv1
  have hLError := hN.metricBilinear_second_taylor_bound hΩ hg hK hC hM1 hM2 hΓ0 hDg hDg2 hy v (interior_subset hv)
  have hCompat (a b : X) : metricDifferential g y v a b =
      metricBilinear g y (connectionBilinear g y v a) b+metricBilinear g y a (connectionBilinear g y v b) := by
    simp only [metricBilinear_apply,connectionBilinear_apply]
    exact (connection_metric hΩ hg hK hyΩ v a b).symm
  have hb := norm_metric_pullback_quadratic_le (metricBilinear g (expMap (y,v))) (metricBilinear g y)
    (metricDifferential g y v) J (connectionBilinear g y v) ‖v‖ (9*K) (9*M1) C
    (normalVelocitySecondErrorBudget K C D) (9*((M2+M1*C)*K^2)) (norm_nonneg v) hv1
    (by positivity) (by positivity) hC (by dsimp [normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity)
    (by positivity) hL0 hL1 hJ hG hJError hLError hCompat u w
  simpa only [metricBilinear_apply,Real.norm_eq_abs,normalReferenceMetricSecondBudget] using hb

end ShrinkingSpheres
