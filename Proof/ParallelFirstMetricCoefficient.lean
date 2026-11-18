import Proof.ParallelNormalizedDensity
import Proof.MatrixFamilyCalculus
import Proof.FirstMetricNormalDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- Both metrics use the same reference connection, affine frame and normal map. -/
def parallelFirstMetric (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) : Mat :=
  fun i j => jointNormalMetricPair g₁ E (affineParallelFrame g y a L p.1 (axis i))
    (affineParallelFrame g y a L p.1 (axis j)) (parallelFrameInput g y a r L p)

def parallelNormalizedFirstCoefficient (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) (i j : I) : ℝ :=
  (firstMetricDensityFactor g g₁ (parallelFrameInput g y a r L p).1)⁻¹*
    matrixFamilyCoefficient (parallelFirstMetric g g₁ E y a r L) p i j

def parallelNormalizedFirstCoefficientRemainder (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) (i j : I) : ℝ :=
  parallelNormalizedFirstCoefficient g g₁ E y a r L p i j-(1:Mat) i j-
    firstDensityLogDifferential g g₁ (parallelFrameInput g y a r L p).1
      (parallelFrameInput g y a r L p).2*(1:Mat) i j

lemma matrixFamilyCoefficient_scalar_sq {P : Type*} (G H : P → Mat) (p : P) (c : ℝ) (hc : 0 < c)
    (hMetric : H p = c^2 • G p) (hDet : IsUnit (G p).det) (i j : I) :
    matrixFamilyCoefficient H p i j = c*matrixFamilyCoefficient G p i j := by
  have hb := congrArg (fun A : Mat => A i j)
    (principalCoefficient_radius_sq (fun _ : X => G p) c hc (0:X) hDet)
  simpa only [matrixFamilyCoefficient,matrixFamilyDensity,principalCoefficient,OAI.AnisotropicCalderon.vol,
    hMetric,Matrix.smul_apply,smul_eq_mul] using hb

theorem Background.parallelFirstMetric_density_factor {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (y a : X) (r : ℝ) (L : X →L[ℝ] X) (p : ℝ × X)
    (hx : E (parallelFrameInput g y a r L p) ∈ Ω) :
    parallelFirstMetric g g₁ E y a r L p =
      (firstMetricDensityFactor g g₁ (E (parallelFrameInput g y a r L p)))^2 •
        parallelFrameNormalMetric g E y a r L p := by
  ext i j
  change metricPair g₁ _ _ _ = _
  rw [h.firstMetricPair_eq_conformalFactor hK hx,← h.firstMetricDensityFactor_sq hK hx]
  rfl

/-- Exact dimension-three factorization for this genuine nonorthonormal local
    family. No orthonormality away from the center is assumed. -/
theorem Background.parallelNormalizedFirstCoefficient_eq {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (y a : X) (r : ℝ) (L : X →L[ℝ] X) (p : ℝ × X)
    (hx : E (parallelFrameInput g y a r L p) ∈ Ω)
    (hDet : IsUnit (parallelFrameNormalMetric g E y a r L p).det) (i j : I) :
    parallelNormalizedFirstCoefficient g g₁ E y a r L p i j =
      parallelNormalizedDensity g g₁ E y a r L p*
        matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) p i j := by
  have hb := matrixFamilyCoefficient_scalar_sq (parallelFrameNormalMetric g E y a r L)
    (parallelFirstMetric g g₁ E y a r L) p (firstMetricDensityFactor g g₁ (E (parallelFrameInput g y a r L p)))
    (firstMetricDensityFactor_pos _ _ _) (h.parallelFirstMetric_density_factor hK E y a r L p hx) hDet i j
  unfold parallelNormalizedFirstCoefficient
  rw [hb]
  simp only [parallelNormalizedDensity,normalizedJointFirstDensityFactor,div_eq_mul_inv]
  ring

theorem Background.parallelNormalizedFirstCoefficientRemainder_eq {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (y a : X) (r : ℝ) (L : X →L[ℝ] X) (p : ℝ × X)
    (hx : E (parallelFrameInput g y a r L p) ∈ Ω)
    (hDet : IsUnit (parallelFrameNormalMetric g E y a r L p).det) (i j : I) :
    parallelNormalizedFirstCoefficientRemainder g g₁ E y a r L p i j =
      (1:Mat) i j*parallelNormalizedDensityRemainder g g₁ E y a r L p+
      parallelNormalizedDensity g g₁ E y a r L p*
        (matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) p i j-(1:Mat) i j) := by
  unfold parallelNormalizedFirstCoefficientRemainder
  rw [h.parallelNormalizedFirstCoefficient_eq hK E y a r L p hx hDet i j]
  simp only [parallelNormalizedDensityRemainder,normalizedDensityAffineRemainder,parallelNormalizedDensity]
  ring

end ShrinkingSpheres
