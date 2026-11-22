module

public import Proof.CalderonN.HarmonicHilbertDecomposition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

@[expose] public section

/- Finite harmonic cutoffs and dominated convergence from the three-dimensional
   Proposition 5.3 proof, with the shared Hilbert decomposition in dimension n. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal
namespace CalderonN
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

lemma norm_sum_harmonicProjection_le (s : Finset ℕ) (u : SphereL2 n) :
    ‖∑ k ∈ s, (harmonicProjection k u : SphereL2 n)‖ ≤ ‖u‖ := by
  have hs : HasSum (fun k : ℕ => ‖harmonicProjection k u‖ ^ 2) (‖u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
      sphereHarmonicDecomposition_apply] using
      lp.hasSum_norm (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
        (sphereHarmonicDecomposition u)
  have hsum := isHilbertSum_harmonicSphereSubspaces.OrthogonalFamily.norm_sum
    (fun k => harmonicProjection k u) s
  have he : ‖∑ k ∈ s, (harmonicProjection k u : SphereL2 n)‖ ^ 2 =
      ∑ k ∈ s, ‖harmonicProjection k u‖ ^ 2 := hsum
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [he]
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) hs

def harmonicPartialSum (N : ℕ) : SphereL2 n →L[ℝ] SphereL2 n :=
  ∑ k ∈ Finset.range N, (harmonicSphereSubspace n k).subtypeL.comp (harmonicProjection k)

lemma harmonicPartialSum_apply (N : ℕ) (u : SphereL2 n) :
    harmonicPartialSum N u = ∑ k ∈ Finset.range N, (harmonicProjection k u : SphereL2 n) := by
  simp [harmonicPartialSum]

lemma norm_harmonicPartialSum_le (N : ℕ) (u : SphereL2 n) : ‖harmonicPartialSum N u‖ ≤ ‖u‖ := by
  rw [harmonicPartialSum_apply]
  exact norm_sum_harmonicProjection_le (Finset.range N) u

lemma tendsto_harmonicPartialSum (u : SphereL2 n) :
    Tendsto (fun N => harmonicPartialSum N u) atTop (𝓝 u) := by
  simpa only [harmonicPartialSum_apply] using (hasSum_harmonicProjection u).tendsto_sum_nat

/-- Finite harmonic cutoffs converge for every nonnegative measurable integration weight.
    The only domination requirement is the integrability of the original weighted L2 square. -/
theorem tendsto_integral_weighted_harmonicPartialSum {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (weight : A → ℝ) (hw : AEStronglyMeasurable weight μ)
    (hwpos : ∀ᵐ x ∂μ,0 ≤ weight x) (U : A → SphereL2 n) (hU : AEStronglyMeasurable U μ)
    (hint : Integrable (fun x => weight x*‖U x‖^2) μ) :
    Tendsto (fun N : ℕ => ∫ x,weight x*‖harmonicPartialSum N (U x)-U x‖^2 ∂μ) atTop (𝓝 0) := by
  have hmeas (N : ℕ) : AEStronglyMeasurable
      (fun x => weight x*‖harmonicPartialSum N (U x)-U x‖^2) μ :=
    hw.mul ((((harmonicPartialSum N).continuous.comp_aestronglyMeasurable hU).sub hU).norm.pow 2)
  have hbound (N : ℕ) : ∀ᵐ x ∂μ,‖weight x*‖harmonicPartialSum N (U x)-U x‖^2‖ ≤
      4*(weight x*‖U x‖^2) := by
    filter_upwards [hwpos] with x hx
    have hn : ‖harmonicPartialSum N (U x)-U x‖ ≤ 2*‖U x‖ := by
      calc
        _ ≤ ‖harmonicPartialSum N (U x)‖+‖U x‖ := norm_sub_le _ _
        _ ≤ ‖U x‖+‖U x‖ := add_le_add (norm_harmonicPartialSum_le N _) le_rfl
        _ = _ := by ring
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs hx]
  have hlim : ∀ᵐ x ∂μ,Tendsto (fun N : ℕ => weight x*‖harmonicPartialSum N (U x)-U x‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (((tendsto_harmonicPartialSum (U x)).sub_const (U x)).norm.pow 2).const_mul (weight x)
  simpa using tendsto_integral_of_dominated_convergence
    (fun x => 4*(weight x*‖U x‖^2)) hmeas (hint.const_mul 4) hbound hlim


end CalderonN
