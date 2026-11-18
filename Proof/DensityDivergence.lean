import Proof.LocalIntegration
import Proof.FrameBasis

noncomputable section
open Set
namespace ShrinkingSpheres

lemma inverse_metric_symmetric (g : MetricField) (y : X) (h : (g y).PosDef) (i j : I) :
    (g y)⁻¹ i j = (g y)⁻¹ j i := by simpa using h.inv.isHermitian.apply j i

/-- The two mixed derivative contractions cancel in the trace of the Christoffel symbols. -/
lemma christoffel_trace (g : MetricField) (y : X) (h : (g y).PosDef) (a : I) :
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

lemma christoffel_lower_symmetric {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (k i j : I) :
    christoffel g y k i j = christoffel g y k j i := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [metric_derivative_symmetric hΩ h hy l j i,
    metric_derivative_symmetric hΩ h hy i l j,
    metric_derivative_symmetric hΩ h hy i j l]
  ring

lemma density_coordDeriv (g : MetricField) (y : X) (a : I)
    (hg : ∀ i j, DifferentiableAt ℝ (fun x => g x i j) y) (hp : (g y).PosDef) :
    coordDeriv a (metricDensity g) y = metricDensity g y * ∑ k, christoffel g y k a k := by
  rw [coordDeriv, fderiv_metricDensity_apply_entries g y (axis a) hg hp, christoffel_trace g y hp a]
  simp only [coordDeriv]
  ring

lemma density_connection_trace {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (v : X) :
    fderiv ℝ (metricDensity g) y v = metricDensity g y *
      ∑ i, connection g y (axis i) v i := by
  have hg (i j : I) := ((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  rw [linear_axis_expansion]
  have hd (a : I) : fderiv ℝ (metricDensity g) y (axis a) =
      metricDensity g y * ∑ k, christoffel g y k a k := density_coordDeriv g y a hg (h.posDef hK hy)
  simp_rw [hd]
  have hc (i : I) : connection g y (axis i) v i = ∑ j, christoffel g y i j i * v j := by
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

lemma vectorComponent_fderiv (V : X → X) (y a : X) (hV : DifferentiableAt ℝ V y) (i : I) :
    fderiv ℝ (fun x => V x i) y a = fderiv ℝ V y a i := by
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hV.hasFDerivAt
  exact congrArg (fun L : X →L[ℝ] ℝ => L a) hh.fderiv

lemma weightedDivergence_derivative_trace (ρ : X → ℝ) (V : X → X) (y : X)
    (hρ : DifferentiableAt ℝ ρ y) (hV : DifferentiableAt ℝ V y) :
    weightedDivergence ρ V y = fderiv ℝ ρ y (V y) +
      ρ y * ∑ i, fderiv ℝ V y (axis i) i := by
  have hv (i : I) : DifferentiableAt ℝ (fun x => V x i) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp y hV
  simp only [weightedDivergence, coordDeriv]
  simp_rw [fderiv_fun_mul hρ (hv _)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    vectorComponent_fderiv V y _ hV, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [linear_axis_expansion, add_comm]

/-- Metric-volume divergence equals the trace of covariant differentiation in any orthonormal
    frame, with all geometry and differentiability assumptions local to the given center. -/
lemma weightedDivergence_metric_frame {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (V : X → X) (hV : DifferentiableAt ℝ V y) :
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

end ShrinkingSpheres
