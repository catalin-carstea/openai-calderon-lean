module

public import Proof.Manuscript.StereoSphereMeasure

import Proof.Manuscript.StereoRadialChart

public section

noncomputable section

open Set Metric MeasureTheory CalderonN
open scoped ContDiff ENNReal

namespace CalderonPaper

variable {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

/-- Euclidean density of the normalized sphere measure in an actual
stereographic chart. -/
theorem exists_stereographic_sphereProbability_density
    (h : 1 ≤ dim) (v : ↥(sphere (0 : X dim) 1)) :
    ∃ w : X (dim-1) → ℝ, ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
      Measure.map (stereographic' (dim-1) v)
        ((sphereProbability dim).restrict (stereographic' (dim-1) v).source) =
        (volume : Measure (X (dim-1))).withDensity (fun x => ENNReal.ofReal (w x)) :=
  exists_stereographic_map_sphereProbability_eq_withDensity_of_radialMap v
    (stereoRadialCoordinates h) (stereoRadialMap h v) (stereoRadialMap_apply h v)
    (contDiff_stereoRadialMap h v) (stereoRadialMap_injOn h v)
    (stereoRadialMap_det_ne_zero h v)

end CalderonPaper
