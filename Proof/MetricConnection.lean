import Proof.Normalization
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set
namespace ShrinkingSpheres

/-- Lowering the upper connection index cancels the inverse metric in the Christoffel formula. -/
lemma lower_christoffel (g : MetricField) (y : X) (hg : (g y).PosDef) (l i j : I) :
    (∑ k, g y l k * christoffel g y k i j) =
      (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y -
        coordDeriv l (fun x => g x i j) y) / 2 := by
  let v : I → ℝ := fun a => coordDeriv i (fun x => g x a j) y +
    coordDeriv j (fun x => g x i a) y - coordDeriv a (fun x => g x i j) y
  have hinv := Matrix.mul_nonsing_inv (g y) (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  have hv := congrArg (fun M : Mat => (Matrix.mulVec M v) l) hinv
  rw [← Matrix.mulVec_mulVec] at hv
  simp only [Matrix.one_mulVec] at hv
  change (∑ k, g y l k * ∑ a, (g y)⁻¹ k a * v a) = v l at hv
  change (∑ k, g y l k * ((∑ a, (g y)⁻¹ k a * v a) / 2)) = v l / 2
  simp only [← mul_div_assoc, ← Finset.sum_div, hv]

/-- Symmetry of each coordinate derivative follows from symmetry throughout an open domain. -/
lemma metric_derivative_symmetric {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (i j a : I) :
    coordDeriv a (fun x => g x i j) y = coordDeriv a (fun x => g x j i) y := by
  have heq : (fun x => g x i j) =ᶠ[nhds y] (fun x => g x j i) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    have hh := congrArg (fun M : Mat => M i j) (h.2 x hx).1
    exact hh.symm
  exact congrArg (fun L : X →L[ℝ] ℝ => L (axis a)) heq.fderiv_eq

lemma connection_axis_components (g : MetricField) (y : X) (a i k : I) :
    connection g y (axis a) (axis i) k = christoffel g y k a i := by
  simp [connection, axis]

lemma metricPair_axis_left (g : MetricField) (y v : X) (i : I) :
    metricPair g y (axis i) v = ∑ j, g y i j * v j := by
  simp [metricPair, axis]

lemma metricPair_axis_right (g : MetricField) (y v : X) (j : I) :
    metricPair g y v (axis j) = ∑ i, g y i j * v i := by
  simp [metricPair, axis]

/-- Levi–Civita compatibility in the coordinate basis, from the actual metric derivatives. -/
lemma connection_metric_basis {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a i j : I) :
    metricPair g y (connection g y (axis a) (axis i)) (axis j) +
      metricPair g y (axis i) (connection g y (axis a) (axis j)) =
        coordDeriv a (fun x => g x i j) y := by
  rw [metricPair_axis_right, metricPair_axis_left]
  simp_rw [connection_axis_components]
  have hs (k : I) : g y k j = g y j k := by
    exact congrArg (fun M : Mat => M j k) (h.2 y hy).1
  simp_rw [hs]
  rw [lower_christoffel g y (h.posDef hK hy), lower_christoffel g y (h.posDef hK hy),
    metric_derivative_symmetric hΩ h hy j i a]
  ring

end ShrinkingSpheres
