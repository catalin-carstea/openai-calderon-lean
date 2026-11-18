import Proof.CoordinateFiniteSumCalculus
import Proof.PrincipalAdjointWeights
import Proof.ConnectionSecondBounds
import Proof.ThirdDerivativeProductBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def densityTraceFirstBudget (K M1 M2 : ℝ) : ℝ := 243*K^2*M1^2+27*K*M2

def densityTraceSecondBudget (K M1 M2 M3 : ℝ) : ℝ :=
  27*(K*M3+2*(9*K^2*M1)*M2+(9*(162*K^3*M1^2+9*K^2*M2))*M1)

def densityThirdBudget (K M1 M2 M3 : ℝ) : ℝ :=
  densitySecondBudget K M1 M2*densityFirstBudget K M1+
    2*densityFirstBudget K M1*densityTraceFirstBudget K M1 M2+
    densityTraceSecondBudget K M1 M2 M3

/-- Relative third jets of the actual metric density, obtained from the connection
trace. Only three background metric jets occur, and no frame is differentiated. -/
theorem Elliptic.relative_density_coordinate_third {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {y : X} (hy : y ∈ Y)
    (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3)
    (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (metricDensity g))) y| ≤
      densityThirdBudget K M1 M2 M3*metricDensity g y := by
  let G (a : I) (x : X) : ℝ := ∑ l,christoffel g x l a l
  let D1 := densityFirstBudget K M1
  let D2 := densitySecondBudget K M1 M2
  let DG := densityTraceFirstBudget K M1 M2
  let DDG := densityTraceSecondBudget K M1 M2 M3
  have hK0 : 0 ≤ K := hK.le
  have hD10 : 0 ≤ D1 := by dsimp [D1,densityFirstBudget];positivity
  have hD20 : 0 ≤ D2 := by dsimp [D2,densitySecondBudget];positivity
  have hDG0 : 0 ≤ DG := by dsimp [DG,densityTraceFirstBudget];positivity
  have hDDG0 : 0 ≤ DDG := by dsimp [DDG,densityTraceSecondBudget];positivity
  have hμpos := metricDensity_pos h hK hy
  have hμ := h.contDiffOn_density hK
  have hΓ (a l : I) := h.contDiffOn_christoffel hY hK l a l
  have hG (a : I) : ContDiffOn ℝ ∞ (G a) Y := ContDiffOn.sum (fun l _ => hΓ a l)
  have hGB (a : I) : |G a y| ≤ D1 := by
    calc
      _ ≤ ∑ l,|christoffel g y l a l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : I,9*K*M1 := Finset.sum_le_sum (fun l _ => h.christoffel_entry_bound hK hy M1 hM1 hD l a l)
      _ = D1 := by simp [I,D1,densityFirstBudget];ring
  have hDGB (a b : I) : |coordDeriv b (G a) y| ≤ DG := by
    rw [show G a = (fun x => ∑ l,christoffel g x l a l) from rfl,coordinate_sum hY _ (hΓ a) hy b]
    calc
      _ ≤ ∑ l,|coordDeriv b (fun x => christoffel g x l a l) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : I,(81*K^2*M1^2+9*K*M2) := by
        apply Finset.sum_le_sum
        intro l _
        simpa only [coordDeriv,norm_axis,mul_one] using
          h.christoffel_derivative_entry_bound hY hK hy M1 M2 hM1 hM2 hD hD2 (axis b) l a l
      _ = DG := by simp [I,DG,densityTraceFirstBudget];ring
  have hDDGB (a b c : I) : |coordDeriv b (coordDeriv c (G a)) y| ≤ DDG := by
    rw [show G a = (fun x => ∑ l,christoffel g x l a l) from rfl,coordinate_second_sum hY _ (hΓ a) hy b c]
    have hEntry (l : I) : |coordDeriv b (coordDeriv c (fun x => christoffel g x l a l)) y| ≤
        9*(K*M3+2*(9*K^2*M1)*M2+(9*(162*K^3*M1^2+9*K^2*M2))*M1) := by
      have hd := (((hΓ a l).fderiv_of_isOpen (m:=∞) hY (by simp)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
      rw [coordinate_second_derivative _ y hd b c]
      have ht := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ (fun x => christoffel g x l a l)) y) (axis b) (axis c)
      rw [norm_axis,norm_axis,mul_one,mul_one,Real.norm_eq_abs] at ht
      exact ht.trans (h.christoffel_second_fderiv_bound hY hK hy M1 M2 M3 hM1 hM2 hM3 hD hD2
        (fun u v => by simpa only [norm_iteratedFDeriv_three_eq_nested] using hD3 u v) l a l)
    calc
      _ ≤ ∑ l,|coordDeriv b (coordDeriv c (fun x => christoffel g x l a l)) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : I,9*(K*M3+2*(9*K^2*M1)*M2+(9*(162*K^3*M1^2+9*K^2*M2))*M1) := Finset.sum_le_sum (fun l _ => hEntry l)
      _ = DDG := by simp [I,DDG,densityTraceSecondBudget];ring
  have hEq : coordDeriv k (metricDensity g) =ᶠ[𝓝 y] (fun x => metricDensity g x*G k x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact density_coordDeriv g x k (fun a b => ((h.1 a b).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) (h.posDef hK hx)
  have hEqD : coordDeriv j (coordDeriv k (metricDensity g)) =ᶠ[𝓝 y]
      (coordDeriv j (fun x => metricDensity g x*G k x)) :=
    hEq.fderiv.mono (fun _ hh => congrArg (fun L : X →L[ℝ] ℝ => L (axis j)) hh)
  have hExpand : coordDeriv i (coordDeriv j (coordDeriv k (metricDensity g))) y =
      coordDeriv i (coordDeriv j (metricDensity g)) y*G k y+
      coordDeriv j (metricDensity g) y*coordDeriv i (G k) y+
      coordDeriv i (metricDensity g) y*coordDeriv j (G k) y+
      metricDensity g y*coordDeriv i (coordDeriv j (G k)) y := by
    change fderiv ℝ (coordDeriv j (coordDeriv k (metricDensity g))) y (axis i) = _
    rw [hEqD.fderiv_eq]
    exact coordinate_second_mul hY hμ (hG k) hy i j
  have hμ1 (a : I) : |coordDeriv a (metricDensity g) y| ≤ D1*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hK hy M1 M2 hM1 hM2 hD hD2 a a).1
  have hμ2 (a b : I) : |coordDeriv a (coordDeriv b (metricDensity g)) y| ≤ D2*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hK hy M1 M2 hM1 hM2 hD hD2 b a).2
  have h1 := mul_le_mul (hμ2 i j) (hGB k) (abs_nonneg _) (mul_nonneg hD20 hμpos.le)
  have h2 := mul_le_mul (hμ1 j) (hDGB k i) (abs_nonneg _) (mul_nonneg hD10 hμpos.le)
  have h3 := mul_le_mul (hμ1 i) (hDGB k j) (abs_nonneg _) (mul_nonneg hD10 hμpos.le)
  have h4 : |metricDensity g y*coordDeriv i (coordDeriv j (G k)) y| ≤ metricDensity g y*DDG := by
    rw [abs_mul,abs_of_pos hμpos]
    exact mul_le_mul_of_nonneg_left (hDDGB k i j) hμpos.le
  simp only [← abs_mul] at h1 h2 h3
  rw [hExpand]
  have hAbs (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
    linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d]
  apply (hAbs _ _ _ _).trans
  change _ ≤ (D2*D1+2*D1*DG+DDG)*metricDensity g y
  linarith only [h1,h2,h3,h4]

end ShrinkingSpheres
