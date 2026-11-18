import Proof.ModelOutputLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph

/-- The positive harmonic degrees through n, with the exact frozen Sobolev weights. -/
def partialSobolevSquare (s : ℝ) (n : ℕ) (U V : SphereL2) : ℝ :=
  ∑ k ∈ Finset.range n,(1+((k+1:ℕ):ℝ))^(2*s)*(‖harmonicProjection (k+1) U‖^2+‖harmonicProjection (k+1) V‖^2)

lemma hasSum_bessel_component_pair (s : ℝ) (U V B C : SphereL2)
    (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) :
    HasSum (fun k : ℕ => (1+(k:ℝ))^(2*s)*(‖harmonicProjection k U‖^2+‖harmonicProjection k V‖^2))
      (‖B‖^2+‖C‖^2) := by
  have hU := (summable_bessel_components s U B hB).hasSum
  have hV := (summable_bessel_components s V C hC).hasSum
  rw [← norm_sq_bessel_components s U B hB] at hU
  rw [← norm_sq_bessel_components s V C hC] at hV
  simpa only [← mul_add] using hU.add hV

lemma hasSum_positive_bessel_component_pair (s : ℝ) (U V B C : SphereL2)
    (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hU₀ : harmonicProjection 0 U = 0) (hV₀ : harmonicProjection 0 V = 0) :
    HasSum (fun k : ℕ => (1+((k+1:ℕ):ℝ))^(2*s)*(‖harmonicProjection (k+1) U‖^2+‖harmonicProjection (k+1) V‖^2))
      (‖B‖^2+‖C‖^2) := by
  have hh := hasSum_bessel_component_pair s U V B C hB hC
  have hlim := hh.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1),
    (1+(k:ℝ))^(2*s)*(‖harmonicProjection k U‖^2+‖harmonicProjection k V‖^2)) atTop (𝓝 (‖B‖^2+‖C‖^2)) at hlim
  simp only [Finset.sum_range_succ',hU₀,hV₀,norm_zero,zero_pow (by omega : 2 ≠ 0),
    add_zero,mul_zero] at hlim
  exact (hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity) _).mpr hlim

lemma partialSobolevSquare_nonneg (s : ℝ) (n : ℕ) (U V : SphereL2) : 0 ≤ partialSobolevSquare s n U V := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma partialSobolevSquare_le (s : ℝ) (n : ℕ) (U V B C : SphereL2)
    (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hU₀ : harmonicProjection 0 U = 0) (hV₀ : harmonicProjection 0 V = 0) :
    partialSobolevSquare s n U V ≤ ‖B‖^2+‖C‖^2 :=
  sum_le_hasSum (Finset.range n) (fun _ _ => by positivity)
    (hasSum_positive_bessel_component_pair s U V B C hB hC hU₀ hV₀)

lemma tendsto_partialSobolevSquare (s : ℝ) (U V B C : SphereL2)
    (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hU₀ : harmonicProjection 0 U = 0) (hV₀ : harmonicProjection 0 V = 0) :
    Tendsto (fun n => partialSobolevSquare s n U V) atTop (𝓝 (‖B‖^2+‖C‖^2)) :=
  (hasSum_positive_bessel_component_pair s U V B C hB hC hU₀ hV₀).tendsto_sum_nat

end ShrinkingSpheres
