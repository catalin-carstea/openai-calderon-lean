import Proof.CoordinateSecondJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Relative first and second jets of the actual metric volume density, with explicit
    constants from the same ellipticity and two background derivative budgets. -/
theorem Elliptic.relative_density_coordinate_jets {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {y : X} (hy : y ∈ Y)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂) (i j : I) :
    |coordDeriv i (metricDensity g) y| ≤ (27*K*M₁)*metricDensity g y ∧
    |coordDeriv j (coordDeriv i (metricDensity g)) y| ≤
      (972*K^2*M₁^2+27*K*M₂)*metricDensity g y := by
  let G (a : I) (x : X) : ℝ := ∑ k,christoffel g x k a k
  have hG (a : I) : ContDiffOn ℝ ∞ (G a) Y := ContDiffOn.sum (fun k _ => h.contDiffOn_christoffel hY hK k a k)
  have hμ := h.contDiffOn_density hK
  have hμpos : 0 < metricDensity g y := Real.sqrt_pos.mpr (h.posDef hK hy).det_pos
  have hEq (a : I) (x : X) (hx : x ∈ Y) : coordDeriv a (metricDensity g) x = metricDensity g x*G a x :=
    density_coordDeriv g x a (fun b c => ((h.1 b c).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) (h.posDef hK hx)
  have hGB (a : I) : |G a y| ≤ 27*K*M₁ := by
    calc
      _ ≤ ∑ k,|christoffel g y k a k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : I,9*K*M₁ := Finset.sum_le_sum (fun k _ => h.christoffel_entry_bound hK hy M₁ hM₁ hD k a k)
      _ = _ := by simp [I]; ring
  have hμB (a : I) : |coordDeriv a (metricDensity g) y| ≤ (27*K*M₁)*metricDensity g y := by
    rw [hEq a y hy,abs_mul,abs_of_pos hμpos]
    have ht := mul_le_mul_of_nonneg_left (hGB a) hμpos.le
    nlinarith only [ht]
  have hDG (a : I) : |coordDeriv j (G a) y| ≤ 243*K^2*M₁^2+27*K*M₂ := by
    have hd (k : I) := ((h.contDiffOn_christoffel hY hK k a k).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hs : HasFDerivAt (G a) (∑ k,fderiv ℝ (fun x => christoffel g x k a k) y) y :=
      HasFDerivAt.fun_sum (fun k _ => (hd k).hasFDerivAt)
    change |(fderiv ℝ (G a) y) (axis j)| ≤ _
    rw [hs.fderiv]
    simp only [sum_apply]
    calc
      _ ≤ ∑ k,|(fderiv ℝ (fun x => christoffel g x k a k) y) (axis j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : I,(81*K^2*M₁^2+9*K*M₂) := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [norm_axis,mul_one] using h.christoffel_derivative_entry_bound hY hK hy M₁ M₂ hM₁ hM₂ hD hD₂ (axis j) k a k
      _ = _ := by simp [I]; ring
  refine ⟨hμB i,?_⟩
  have heq : coordDeriv i (metricDensity g) =ᶠ[𝓝 y] (fun x => metricDensity g x*G i x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hEq i x hx
  have hdμ := (hμ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hdG := ((hG i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have he : coordDeriv j (coordDeriv i (metricDensity g)) y =
      coordDeriv j (metricDensity g) y*G i y+metricDensity g y*coordDeriv j (G i) y := by
    change (fderiv ℝ (coordDeriv i (metricDensity g)) y) (axis j) = _
    rw [heq.fderiv_eq,(hdμ.hasFDerivAt.fun_mul hdG.hasFDerivAt).fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,coordDeriv]
    ring
  rw [he]
  have h1 := mul_le_mul (hμB j) (hGB i) (abs_nonneg _) (show 0 ≤ (27*K*M₁)*metricDensity g y by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hDG i) hμpos.le
  have ha := abs_add_le (coordDeriv j (metricDensity g) y*G i y) (metricDensity g y*coordDeriv j (G i) y)
  simp only [← abs_mul] at h1
  have h2' : |metricDensity g y*coordDeriv j (G i) y| ≤ metricDensity g y*(243*K^2*M₁^2+27*K*M₂) := by
    rw [abs_mul,abs_of_pos hμpos]
    exact h2
  nlinarith only [h1,h2',ha]

end ShrinkingSpheres
