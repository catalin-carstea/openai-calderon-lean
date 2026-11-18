import Proof.CoordinateSecondJetCalculus
import Proof.InverseMetricThirdDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma coordinate_third_swap_outer {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k f)) y = coordDeriv j (coordDeriv i (coordDeriv k f)) y :=
  coordinate_second_commute hY (contDiffOn_coordDeriv hY hf k) hy i j

lemma coordinate_third_swap_inner {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k f)) y = coordDeriv i (coordDeriv k (coordDeriv j f)) y := by
  have hEq : coordDeriv j (coordDeriv k f) =ᶠ[𝓝 y] coordDeriv k (coordDeriv j f) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_second_commute hY hf hx j k
  change fderiv ℝ (coordDeriv j (coordDeriv k f)) y (axis i) = _
  rw [hEq.fderiv_eq]
  rfl

lemma coordinate_third_abs_le_iterated {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤ ‖iteratedFDeriv ℝ 3 f y‖ := by
  calc
    _ ≤ ‖fderiv ℝ (coordDeriv j (coordDeriv k f)) y‖ := coordDeriv_abs_le _ y i
    _ = ‖iteratedFDeriv ℝ 1 (coordDeriv j (coordDeriv k f)) y‖ := (norm_iteratedFDeriv_one _).symm
    _ ≤ ‖iteratedFDeriv ℝ 2 (coordDeriv k f) y‖ :=
      norm_iteratedFDeriv_coordDeriv_le hY (contDiffOn_coordDeriv hY hf k) hy j 1
    _ ≤ ‖iteratedFDeriv ℝ 3 f y‖ := norm_iteratedFDeriv_coordDeriv_le hY hf hy k 2

lemma coordinate_third_sub {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k (fun x => f x-g x))) y =
      coordDeriv i (coordDeriv j (coordDeriv k f)) y-coordDeriv i (coordDeriv j (coordDeriv k g)) y := by
  have hEq : coordDeriv j (coordDeriv k (fun x => f x-g x)) =ᶠ[𝓝 y]
      (fun x => coordDeriv j (coordDeriv k f) x-coordDeriv j (coordDeriv k g) x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_second_sub hY hf hg hx j k
  have hDf := ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hf k) j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hDg := ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hg k) j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  change fderiv ℝ (coordDeriv j (coordDeriv k (fun x => f x-g x))) y (axis i) = _
  rw [hEq.fderiv_eq,fderiv_fun_sub hDf hDg]
  rfl

lemma coordinate_third_bound_of_chartPartials {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (C : ℝ)
    (hPartial : ∀ a b c : ℕ,a+b+c = 3 → |chartPartial a b c f y| ≤ C) (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤ C := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · change |coordDeriv (0:I) (coordDeriv (0:I) (coordDeriv (0:I) f)) y| ≤ C
    exact hPartial 3 0 0 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (0:I) (coordDeriv (1:I) f)) y| ≤ C
    exact hPartial 2 1 0 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (0:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 2 0 1 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (1:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 0 1 0]
    exact hPartial 2 1 0 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (1:I) (coordDeriv (1:I) f)) y| ≤ C
    exact hPartial 1 2 0 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (1:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (2:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 0 2 0]
    exact hPartial 2 0 1 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (2:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 0 2 1]
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (0:I) (coordDeriv (2:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 1 0 2 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (0:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 1 0 0]
    rw [coordinate_third_swap_inner hY hf hy 0 1 0]
    exact hPartial 2 1 0 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (0:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 1 0 1]
    exact hPartial 1 2 0 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (0:I) (coordDeriv (2:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 1 0 2]
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (1:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 1 1 0]
    rw [coordinate_third_swap_outer hY hf hy 1 0 1]
    exact hPartial 1 2 0 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (1:I) (coordDeriv (1:I) f)) y| ≤ C
    exact hPartial 0 3 0 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (1:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 0 2 1 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (2:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 1 2 0]
    rw [coordinate_third_swap_outer hY hf hy 1 0 2]
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (2:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 1 2 1]
    exact hPartial 0 2 1 (by decide)
  · change |coordDeriv (1:I) (coordDeriv (2:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 0 1 2 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (0:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 0 0]
    rw [coordinate_third_swap_inner hY hf hy 0 2 0]
    exact hPartial 2 0 1 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (0:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 0 1]
    rw [coordinate_third_swap_inner hY hf hy 0 2 1]
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (0:I) (coordDeriv (2:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 0 2]
    exact hPartial 1 0 2 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (1:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 1 0]
    rw [coordinate_third_swap_inner hY hf hy 1 2 0]
    rw [coordinate_third_swap_outer hY hf hy 1 0 2]
    exact hPartial 1 1 1 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (1:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 1 1]
    rw [coordinate_third_swap_inner hY hf hy 1 2 1]
    exact hPartial 0 2 1 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (1:I) (coordDeriv (2:I) f)) y| ≤ C
    rw [coordinate_third_swap_outer hY hf hy 2 1 2]
    exact hPartial 0 1 2 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (2:I) (coordDeriv (0:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 2 2 0]
    rw [coordinate_third_swap_outer hY hf hy 2 0 2]
    exact hPartial 1 0 2 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (2:I) (coordDeriv (1:I) f)) y| ≤ C
    rw [coordinate_third_swap_inner hY hf hy 2 2 1]
    rw [coordinate_third_swap_outer hY hf hy 2 1 2]
    exact hPartial 0 1 2 (by decide)
  · change |coordDeriv (2:I) (coordDeriv (2:I) (coordDeriv (2:I) f)) y| ≤ C
    exact hPartial 0 0 3 (by decide)

/-- The original eight-jet smallness budget controls every ordered third
coordinate derivative; no special radius or frame is introduced. -/
lemma Small.coordinate_third_component_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) {r : X → ℝ} {ε : ℝ}
    (hs : Small Y g g₂ r ε) {y : X} (hy : y ∈ Y) (i j k a b : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (fun x => (principal g g₂ x-(g x)⁻¹) a b))) y| ≤ ε*r y := by
  have hF : ContDiffOn ℝ ∞ (fun x => (principal g g₂ x-(g x)⁻¹) a b) Y := by
    simpa only [Matrix.sub_apply] using (contDiffOn_principal_entry h h₂ hK a b).sub (h.contDiffOn_inverse_entry hK a b)
  exact coordinate_third_bound_of_chartPartials hY hF hy (ε*r y)
    (fun n0 n1 n2 hn => hs.partial_bound hy n0 n1 n2 (by omega) a b) i j k

end ShrinkingSpheres
