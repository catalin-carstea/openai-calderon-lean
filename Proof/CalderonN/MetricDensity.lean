module

public import Proof.CalderonN.MetricConnection
public import Proof.CalderonN.MetricVolumeDifferential
public import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

@[expose] public section

/- Port of MetricDensity.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

abbrev metricDensity (g : (MetricField n)) (x : (X n)) : ℝ := chartVolume g x

theorem Elliptic.smoothMetric {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) : SmoothMetric Ω g :=
  ⟨h.1, fun y hy => h.posDef hK hy⟩

lemma fderiv_metricDensity_apply (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (metricDensity g) x V = (metricDensity g x / 2) *
      Matrix.trace ((g x)⁻¹ * matrixFieldDerivative g x V) := fderiv_vol_apply g x V hg hp


lemma fderiv_metricDensity_apply_entries (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (metricDensity g) x V = (metricDensity g x / 2) *
      ∑ i : Fin n, ∑ j : Fin n,
        (g x)⁻¹ j i * fderiv ℝ (fun y => g y i j) x V := fderiv_vol_apply_entries g x V hg hp
lemma Elliptic.contDiffOn_density {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) : ContDiffOn ℝ ∞ (metricDensity g) Ω :=
  contDiffOn_metric_volume (h.smoothMetric hK)

lemma metricDensity_pos {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) : 0 < metricDensity g y :=
  Real.sqrt_pos.mpr (h.posDef hK hy).det_pos

end CalderonN
