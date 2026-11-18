import Proof.NormalMapTransport
import Proof.NormalMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma metricDifferential_sub_abs_le (g : MetricField) (x y : X) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ i j,‖fderiv ℝ (fun z => g z i j) x-fderiv ℝ (fun z => g z i j) y‖ ≤ M)
    (a u w : X) :
    |metricDifferential g x a u w-metricDifferential g y a u w| ≤ 9*M*‖a‖*‖u‖*‖w‖ := by
  have hTerm (i j : I) : |(fderiv ℝ (fun z => g z i j) x a-fderiv ℝ (fun z => g z i j) y a)*u i*w j| ≤
      M*‖a‖*‖u‖*‖w‖ := by
    have hda : |fderiv ℝ (fun z => g z i j) x a-fderiv ℝ (fun z => g z i j) y a| ≤ M*‖a‖ := by
      simpa only [Real.norm_eq_abs,ContinuousLinearMap.sub_apply] using
        ((fderiv ℝ (fun z => g z i j) x-fderiv ℝ (fun z => g z i j) y).le_opNorm a).trans
          (mul_le_mul_of_nonneg_right (hD i j) (norm_nonneg a))
    have hui : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hwj : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j
    rw [abs_mul,abs_mul]
    gcongr
  have hEq : metricDifferential g x a u w-metricDifferential g y a u w =
      ∑ i,∑ j,(fderiv ℝ (fun z => g z i j) x a-fderiv ℝ (fun z => g z i j) y a)*u i*w j := by
    simp only [metricDifferential_apply,sub_mul,Finset.sum_sub_distrib]
  rw [hEq]
  calc
    _ ≤ ∑ i,∑ j,|(fderiv ℝ (fun z => g z i j) x a-fderiv ℝ (fun z => g z i j) y a)*u i*w j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : I,∑ _j : I,M*‖a‖*‖u‖*‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

/-- Uniform transport of the metric first differential along an actual geodesic. -/
theorem NormalCoordinates.metricDifferential_transport_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K M2 : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (hM2 : 0 ≤ M2)
    (hD2 : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fderiv ℝ (fun z => g z i j)) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) (a u w : X) :
    |metricDifferential g (expMap (y,v)) a u w-metricDifferential g y a u w| ≤
      9*M2*K*‖v‖*‖a‖*‖u‖*‖w‖ := by
  have hDiff (i j : I) : ‖fderiv ℝ (fun z => g z i j) (expMap (y,v))-fderiv ℝ (fun z => g z i j) y‖ ≤ M2*K*‖v‖ := by
    have hb := hN.map_transport_bound hΩ hg hK hM2 (fderiv ℝ (fun z => g z i j))
      ((hg.1 i j).fderiv_of_isOpen (m:=∞) hΩ (by simp)) (fun x hx => hD2 x hx i j) hy v hv
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    simpa only [one_smul,mul_one] using hb
  exact (metricDifferential_sub_abs_le g (expMap (y,v)) y (M2*K*‖v‖) (by positivity) hDiff a u w).trans_eq (by ring)

end ShrinkingSpheres
