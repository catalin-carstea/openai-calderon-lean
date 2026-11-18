import Proof.LegendreHilbert
import Proof.Archive.BoundedSpectralMultiplier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SphereHilbertDecomposition
open OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralWeightComparison
open OAI.AnisotropicCalderon.BoundedSpectralMultiplier

/-- Adopted unchanged from the supplied WeightedBaseSpectral, with its geometric imports removed. -/
lemma norm_sum_sphereHarmonicCoordinates_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : Finset ℕ) (u : SphereL2) :
    ‖∑ k ∈ s, (sphereHarmonicDecomposition hO hD u k : SphereL2)‖ ≤ ‖u‖ := by
  have hs : HasSum (fun k : ℕ => ‖sphereHarmonicDecomposition hO hD u k‖ ^ 2)
      (‖u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num)
        (sphereHarmonicDecomposition hO hD u)
  have hsum := (orthogonalFamily_harmonicSphereSubspaces hO).norm_sum
    (sphereHarmonicDecomposition hO hD u) s
  have he : ‖∑ k ∈ s, (sphereHarmonicDecomposition hO hD u k : SphereL2)‖ ^ 2 =
      ∑ k ∈ s, ‖sphereHarmonicDecomposition hO hD u k‖ ^ 2 := by
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using hsum
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [he]
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) hs

def harmonicPartialSum (n : ℕ) : SphereL2 →L[ℝ] SphereL2 :=
  sphereHarmonicPartialSum orthogonalSphereHarmonics denseSphereHarmonics n

lemma norm_harmonicPartialSum_le (n : ℕ) (u : SphereL2) : ‖harmonicPartialSum n u‖ ≤ ‖u‖ := by
  rw [harmonicPartialSum,sphereHarmonicPartialSum_apply]
  exact norm_sum_sphereHarmonicCoordinates_le orthogonalSphereHarmonics denseSphereHarmonics (Finset.range n) u

lemma tendsto_harmonicPartialSum (u : SphereL2) :
    Tendsto (fun n => harmonicPartialSum n u) atTop (𝓝 u) :=
  tendsto_sphereHarmonicPartialSum orthogonalSphereHarmonics denseSphereHarmonics u

/-- Finite harmonic cutoffs converge for every nonnegative measurable integration weight.
    The only domination requirement is the integrability of the original weighted L2 square. -/
theorem tendsto_integral_weighted_harmonicPartialSum {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (weight : A → ℝ) (hw : AEStronglyMeasurable weight μ)
    (hwpos : ∀ᵐ x ∂μ,0 ≤ weight x) (U : A → SphereL2) (hU : AEStronglyMeasurable U μ)
    (hint : Integrable (fun x => weight x*‖U x‖^2) μ) :
    Tendsto (fun n : ℕ => ∫ x,weight x*‖harmonicPartialSum n (U x)-U x‖^2 ∂μ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => weight x*‖harmonicPartialSum n (U x)-U x‖^2) μ :=
    hw.mul ((((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hU).sub hU).norm.pow 2)
  have hbound (n : ℕ) : ∀ᵐ x ∂μ,‖weight x*‖harmonicPartialSum n (U x)-U x‖^2‖ ≤
      4*(weight x*‖U x‖^2) := by
    filter_upwards [hwpos] with x hx
    have hn : ‖harmonicPartialSum n (U x)-U x‖ ≤ 2*‖U x‖ := by
      calc
        _ ≤ ‖harmonicPartialSum n (U x)‖+‖U x‖ := norm_sub_le _ _
        _ ≤ ‖U x‖+‖U x‖ := add_le_add (norm_harmonicPartialSum_le n _) le_rfl
        _ = _ := by ring
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs hx]
  have hlim : ∀ᵐ x ∂μ,Tendsto (fun n : ℕ => weight x*‖harmonicPartialSum n (U x)-U x‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (((tendsto_harmonicPartialSum (U x)).sub_const (U x)).norm.pow 2).const_mul (weight x)
  simpa using tendsto_integral_of_dominated_convergence
    (fun x => 4*(weight x*‖U x‖^2)) hmeas (hint.const_mul 4) hbound hlim

end ShrinkingSpheres
