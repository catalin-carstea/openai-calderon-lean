module

public import Proof.CalderonN.LocalIntegration
public import Proof.CalderonN.FrameBasis
import Mathlib.Tactic

@[expose] public section

/- Port of DensityDivergence.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ} [NeZero n]

lemma inverse_metric_symmetric (g : (MetricField n)) (y : (X n)) (h : (g y).PosDef) (i j : (I n)) :
    (g y)⁻¹ i j = (g y)⁻¹ j i := by simpa using h.inv.isHermitian.apply j i

/-- The two mixed derivative contractions cancel in the trace of the Christoffel symbols. -/
lemma christoffel_trace (g : (MetricField n)) (y : (X n)) (h : (g y).PosDef) (a : (I n)) :
    (∑ k, christoffel g y k a k) =
      (∑ i, ∑ j, (g y)⁻¹ j i * coordDeriv a (fun x => g x i j) y) / 2 := by
  have cancel : (∑ k, ∑ l, (g y)⁻¹ k l * coordDeriv k (fun x => g x a l) y) =
      (∑ k, ∑ l, (g y)⁻¹ k l * coordDeriv l (fun x => g x a k) y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [inverse_metric_symmetric g y h]
  simp only [christoffel, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div]
  rw [cancel]
  simp only [add_sub_cancel_right]
  rw [Finset.sum_comm]

lemma christoffel_lower_symmetric {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) {y : (X n)} (hy : y ∈ Ω) (k i j : (I n)) :
    christoffel g y k i j = christoffel g y k j i := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [metric_derivative_symmetric hΩ h hy l j i,
    metric_derivative_symmetric hΩ h hy i l j,
    metric_derivative_symmetric hΩ h hy i j l]
  ring

lemma density_coordDeriv (g : (MetricField n)) (y : (X n)) (a : (I n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun x => g x i j) y) (hp : (g y).PosDef) :
    coordDeriv a (metricDensity g) y = metricDensity g y * ∑ k, christoffel g y k a k := by
  rw [coordDeriv, fderiv_metricDensity_apply_entries g y (axis a) hg hp, christoffel_trace g y hp a]
  simp only [coordDeriv]
  ring

lemma density_connection_trace {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (v : (X n)) :
    fderiv ℝ (metricDensity g) y v = metricDensity g y *
      ∑ i, connection g y (axis i) v i := by
  have hg (i j : (I n)) := ((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  rw [linear_axis_expansion]
  have hd (a : (I n)) : fderiv ℝ (metricDensity g) y (axis a) =
      metricDensity g y * ∑ k, christoffel g y k a k := density_coordDeriv g y a hg (h.posDef hK hy)
  simp_rw [hd]
  have hc (i : (I n)) : connection g y (axis i) v i = ∑ j, christoffel g y i j i * v j := by
    calc
      _ = ∑ j, christoffel g y i i j * v j := by simp [connection, axis]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [christoffel_lower_symmetric hΩ h hy i i j]
  simp_rw [hc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma vectorComponent_fderiv (V : (X n) → (X n)) (y a : (X n)) (hV : DifferentiableAt ℝ V y) (i : (I n)) :
    fderiv ℝ (fun x => V x i) y a = fderiv ℝ V y a i := by
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hV.hasFDerivAt
  exact congrArg (fun L : (X n) →L[ℝ] ℝ => L a) hh.fderiv

lemma weightedDivergence_derivative_trace (ρ : (X n) → ℝ) (V : (X n) → (X n)) (y : (X n))
    (hρ : DifferentiableAt ℝ ρ y) (hV : DifferentiableAt ℝ V y) :
    weightedDivergence ρ V y = fderiv ℝ ρ y (V y) +
      ρ y * ∑ i, fderiv ℝ V y (axis i) i := by
  have hv (i : (I n)) : DifferentiableAt ℝ (fun x => V x i) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp y hV
  simp only [weightedDivergence, coordDeriv]
  simp_rw [fderiv_fun_mul hρ (hv _)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    vectorComponent_fderiv V y _ hV, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [linear_axis_expansion, add_comm]

/-- Metric-volume divergence equals the trace of covariant differentiation in any orthonormal
    frame, with all geometry and differentiability assumptions local to the given center. -/
lemma weightedDivergence_metric_frame {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n)) {y : (X n)} (hy : y ∈ Ω)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (V : (X n) → (X n)) (hV : DifferentiableAt ℝ V y) :
    weightedDivergence (metricDensity g) V y = metricDensity g y *
      ∑ i, metricPair g y (fderiv ℝ V y (e y i) + connection g y (e y i) (V y)) (e y i) := by
  have hd := (h.contDiffOn_density hK).contDiffAt (hΩ.mem_nhds hy)
  rw [weightedDivergence_derivative_trace _ _ y (hd.differentiableAt (by simp)) hV,
    density_connection_trace hΩ h hK hy]
  have ht := metric_frame_endomorphism_trace g e y he
    (fderiv ℝ V y + (connectionBilinear g y).flip (V y))
  simp only [_root_.add_apply, ContinuousLinearMap.flip_apply, connectionBilinear_apply,
    ← metricBilinear_apply, map_add, _root_.add_apply, PiLp.add_apply, Finset.sum_add_distrib] at ht
  simp only [← metricBilinear_apply, map_add, _root_.add_apply, Finset.sum_add_distrib]
  rw [ht]
  ring

end CalderonN
