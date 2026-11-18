import Proof.PartialEnergyBounds
import Proof.SmoothEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

lemma partial_density_le (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) {y : X} (hy : y ∈ Y) :
    physicalEnergyDensity g e r (E.partialField n) y ≤ physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have h1 := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => D.partial_horizontal_fiber_le hY h hK he hframe hφ n i hy)
  have h2 := E.partial_sobolev_le hframe 1 (by norm_num) n hy
  have h3 := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => D.partial_horizontal_sobolev_le hY h hK he hframe hφ (1/2) (by norm_num) n i hy)
  have h4 := E.partial_sobolev_le hframe (3/2) (by norm_num) n hy
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h1
    (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))) (mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hb)))
      (mul_le_mul_of_nonneg_left h4 hb)) (Real.sqrt_nonneg _)

lemma tendsto_partial_density (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) {y : X} (hy : y ∈ Y) :
    Tendsto (fun n => physicalEnergyDensity g e r (E.partialField n) y) atTop (𝓝 (physicalEnergyDensity g e r φ y)) := by
  have h1 := tendsto_finsetSum Finset.univ (fun i _ => D.tendsto_partial_horizontal_fiber hY h hK he hframe hφ i hy)
  have h2 := E.tendsto_partial_sobolev hframe 1 (by norm_num) hy
  have h3 := tendsto_finsetSum Finset.univ (fun i _ => D.tendsto_partial_horizontal_sobolev hY h hK he hframe hφ (1/2) (by norm_num) i hy)
  have h4 := E.tendsto_partial_sobolev hframe (3/2) (by norm_num) hy
  exact ((((h1.add (h2.const_mul ((beta g r y)^2))).add (h3.const_mul ((beta g r y)⁻¹))).add
    (h4.const_mul (beta g r y))).const_mul (metricDensity g y))

lemma integrable_partial_density (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor) (n : ℕ) :
    IntegrableOn (physicalEnergyDensity g e r (E.partialField n)) Y := by
  have hi : IntegrableOn (fun y => ∑ k ∈ Finset.range n,pairedModeDensity g e r (k+1) (E.basis k)
      (E.realCoefficients k) (E.imagCoefficients k) y) Y := by
    apply integrable_finsetSum
    intro k _
    exact (hp.integrable_pairedModeDensity hY h hK e he hfloor (k+1) (E.basis k) (E.realCoefficients k) (E.imagCoefficients k)
      (E.realSmooth k) (E.imagSmooth k) (E.real_compact k) (E.imag_compact k)
      ((E.realSupport k).trans E.supportSubset) ((E.imagSupport k).trans E.supportSubset)).integrableOn
  apply hi.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  exact (physicalEnergyDensity_finiteAngularField hY h hK e he hframe r (Finset.range n) (fun k => k+1)
    (fun k _ => by omega) (fun k hk j hj heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2) E.realCoefficients E.imagCoefficients
    (fun k _ => (E.realSmooth k).contDiffOn) (fun k _ => (E.imagSmooth k).contDiffOn) hy).symm

/-- The full four-term frozen energy converges for the same genuine finite harmonic fields
    used by the raising estimate. The original physical energy is the dominating function. -/
theorem tendsto_energySq_partialField (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (hφ : Test Y g e φ) :
    Tendsto (fun n => energySq Y g e r (E.partialField n)) atTop (𝓝 (energySq Y g e r φ)) := by
  simp_rw [energySq_eq_integral_density]
  apply tendsto_integral_of_dominated_convergence (physicalEnergyDensity g e r φ)
    (fun n => (D.integrable_partial_density hY h hK he hframe hp hfloor n).aestronglyMeasurable)
    (hp.integrableOn_physicalEnergyDensity hY h hK e he hframe hfloor hφ)
  · intro n
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalEnergyDensity_nonneg g e r (E.partialField n) y)]
    exact D.partial_density_le hY h hK he hframe hφ.1 n hy
  · filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact D.tendsto_partial_density hY h hK he hframe hφ.1 hy

end AngularModelData
end ShrinkingSpheres
