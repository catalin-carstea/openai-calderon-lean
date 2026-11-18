import Proof.NormalMetricTransport
import Proof.NormalJacobianInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma metricBilinear_norm_of_entry_bound (g : MetricField) (y : X) (C : ℝ)
    (hc : ∀ i j,|g y i j| ≤ C) : ‖metricBilinear g y‖ ≤ 9*C := by
  have hAtom (i j : I) : ‖(EuclideanSpace.proj i : X →L[ℝ] ℝ).smulRight
      (EuclideanSpace.proj j : X →L[ℝ] ℝ)‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul (norm_euclidean_proj_le_one i) (norm_euclidean_proj_le_one j)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hTerm (i j : I) : ‖g y i j • (EuclideanSpace.proj i : X →L[ℝ] ℝ).smulRight
      (EuclideanSpace.proj j : X →L[ℝ] ℝ)‖ ≤ C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hAtom i j) (abs_nonneg _)).trans
      (by simpa only [mul_one] using hc i j)
  unfold metricBilinear
  calc
    _ ≤ ∑ i,‖∑ j,g y i j • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖g y i j • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : I,∑ _j : I,C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- Uniform operator-norm transport of the actual metric bilinear form. -/
theorem NormalCoordinates.metricBilinear_transport_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K M : ℝ} {γ g : MetricField} (hγ : Elliptic Ω K γ) (hK : 0 < K) (hM : 0 ≤ M)
    (hSmooth : ∀ i j,ContDiffOn ℝ ∞ (fun x => g x i j) Ω)
    (hD : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk γ y (R y)) :
    ‖metricBilinear g (expMap (y,v))-metricBilinear g y‖ ≤ 9*M*K*‖v‖ := by
  have hEntries (i j : I) : |g (expMap (y,v)) i j-g y i j| ≤ M*K*‖v‖ := by
    simpa only [one_smul,mul_one] using hN.metric_entry_transport_bound hΩ hγ hK hM hSmooth hD hy v hv
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) i j
  have heq : metricBilinear g (expMap (y,v))-metricBilinear g y =
      metricBilinear (fun x => g x-g y) (expMap (y,v)) := by
    simp only [metricBilinear,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
  rw [heq]
  exact (metricBilinear_norm_of_entry_bound _ _ (M*K*‖v‖) hEntries).trans_eq (by ring)

/-- Quantitative comparison of the actual normal pullback with its center metric.
    All constants come from the metric first jet and the checked normal Jacobi bound. -/
theorem NormalCoordinates.normalPullbackMetric_close {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D M : ℝ} {γ g : MetricField} (hγ : Elliptic Ω K γ) (hg : Elliptic Ω K g)
    (hK : 0 < K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear γ x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear γ) x‖ ≤ D)
    (hMetric : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y)
    (v u w : X) (hv : v ∈ interior (disk γ y (R y))) (hv1 : ‖v‖ ≤ 1)
    (hSmall : ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ X‖ ≤ 1) :
    |metricPair g (expMap (y,v)) (normalVerticalJacobian expMap y v u)
        (normalVerticalJacobian expMap y v w)-metricPair g y u w| ≤
      (36*M*K+3*K*normalVariationErrorBudget K C D)*‖v‖*‖u‖*‖w‖ := by
  let J := normalVerticalJacobian expMap y v
  let B := normalVariationErrorBudget K C D
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget]; positivity
  have hJ := hN.normalVerticalJacobian_sub_id_bound hΩ hγ hK hC hD hΓ0 hΓ1 hy v hv hv1
  have hErr (a : X) : ‖J a-a‖ ≤ B*‖v‖*‖a‖ := by
    exact ((J-ContinuousLinearMap.id ℝ X).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg a))
  have hJn (a : X) : ‖J a‖ ≤ 2*‖a‖ := by
    have ht : ‖J a‖ ≤ ‖J a-a‖+‖a‖ := by
      calc
        _ = ‖(J a-a)+a‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hh := mul_le_mul_of_nonneg_right hSmall (norm_nonneg a)
    have he : ‖J a-a‖ ≤ ‖J-ContinuousLinearMap.id ℝ X‖*‖a‖ :=
      (J-ContinuousLinearMap.id ℝ X).le_opNorm a
    nlinarith only [ht,hh,he]
  let L := metricBilinear g (expMap (y,v))-metricBilinear g y
  have hLn : ‖L‖ ≤ 9*M*K*‖v‖ :=
    hN.metricBilinear_transport_bound hΩ hγ hK hM hg.1 hMetric hy v (interior_subset hv)
  have hOne : |L (J u) (J w)| ≤ (9*M*K*‖v‖)*(2*‖u‖)*(2*‖w‖) := by
    calc
      _ ≤ ‖L‖*‖J u‖*‖J w‖ := by
        simpa only [Real.norm_eq_abs] using ((L (J u)).le_opNorm (J w)).trans
          (mul_le_mul_of_nonneg_right (L.le_opNorm (J u)) (norm_nonneg (J w)))
      _ ≤ _ := by gcongr; exact hJn u; exact hJn w
  have hTwo : |metricBilinear g y (J u-u) (J w)| ≤ K*(B*‖v‖*‖u‖)*(2*‖w‖) := by
    rw [metricBilinear_apply]
    exact (hg.metricPair_abs_le hK (hN.center_mem hy) _ _).trans (by gcongr; exact hErr u; exact hJn w)
  have hThree : |metricBilinear g y u (J w-w)| ≤ K*‖u‖*(B*‖v‖*‖w‖) := by
    rw [metricBilinear_apply]
    exact (hg.metricPair_abs_le hK (hN.center_mem hy) _ _).trans (by gcongr; exact hErr w)
  have heq : metricPair g (expMap (y,v)) (J u) (J w)-metricPair g y u w =
      L (J u) (J w)+metricBilinear g y (J u-u) (J w)+metricBilinear g y u (J w-w) := by
    dsimp only [L]
    simp only [_root_.sub_apply,map_sub,_root_.sub_apply,metricBilinear_apply]
    ring
  change |metricPair g (expMap (y,v)) (J u) (J w)-metricPair g y u w| ≤ _
  rw [heq]
  have hh : |L (J u) (J w)+metricBilinear g y (J u-u) (J w)+metricBilinear g y u (J w-w)| ≤
      (|L (J u) (J w)|+|metricBilinear g y (J u-u) (J w)|)+|metricBilinear g y u (J w-w)| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  exact (hh.trans (add_le_add (add_le_add hOne hTwo) hThree)).trans_eq (by dsimp only [B]; ring)

end ShrinkingSpheres
