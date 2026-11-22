module

public import Proof.CalderonN.PartialAngularNorms
public import Proof.CalderonN.SmoothEnergyRegularity
public import Proof.CalderonN.FiniteAngularEnergy

import Mathlib.Tactic

@[expose] public section

/- The finite-to-smooth energy passage in Proposition 5.3 release f308cb9d,
   with the actual generalized projection and the same geometric test. -/
noncomputable section
open MeasureTheory Filter Set MvPolynomial
open scoped Topology ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields AngularPolynomial

variable {n : ℕ} [NeZero n]

lemma fiberSq_nonneg (e : (Frame n)) (y : (X n)) (u : (X n) → ℂ) : 0 ≤ fiberSq e y u := by
  rw [fiberSq_eq_integral_norm_sq]
  exact integral_nonneg (fun _ => sq_nonneg _)

lemma sobolevSq_nonneg (g : (MetricField n)) (e : (Frame n)) (s : ℝ) (y : (X n)) (u : (X n) → ℂ) :
    0 ≤ sobolevSq g e s y u := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (fiberSq_nonneg e y _)

lemma physicalEnergyDensity_nonneg (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (φ : (Field n)) (y : (X n)) :
    0 ≤ physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hH : 0 ≤ ∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)) :=
    Finset.sum_nonneg (fun _ _ => fiberSq_nonneg e y _)
  have hHs : 0 ≤ ∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)) :=
    Finset.sum_nonneg (fun _ _ => sobolevSq_nonneg g e _ y _)
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg
    (add_nonneg hH (mul_nonneg (sq_nonneg _) (sobolevSq_nonneg g e _ y _)))
    (mul_nonneg (inv_nonneg.mpr hb) hHs)) (mul_nonneg hb (sobolevSq_nonneg g e _ y _)))

private theorem positive_sobolev_hasSum (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (g : MetricField n) (e : Frame n) (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (G : Field n) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ v : UnitSphere n, G (y,v.val) = F (frameVector e y v.val))
    (U V : SphereL2 n)
    (hU : U = ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y)
    (hV : V = ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y)
    (h₀U : harmonicProjection 0 U = 0) (h₀V : harmonicProjection 0 V = 0) :
    HasSum (fun k : ℕ => (1+((k+1 : ℕ) : ℝ))^(2*s) *
      (‖harmonicProjection (k+1) U‖^2 + ‖harmonicProjection (k+1) V‖^2)) (sobolevSq g e s y F) := by
  let R : Field n → X n × X n → ℝ := fun H p => (H p).re
  let J : Field n → X n × X n → ℝ := fun H p => (H p).im
  have hR : ContDiff ℝ ∞ (R G) := Complex.reCLM.contDiff.comp hG
  have hJ : ContDiff ℝ ∞ (J G) := Complex.imCLM.contDiff.comp hG
  let B := ambientBesselField hn s hs (R G) hR y
  let C := ambientBesselField hn s hs (J G) hJ y
  have hB (k : ℕ) : harmonicProjection k B = besselWeight s k • harmonicProjection k U := by
    rw [hU]
    exact ambientBesselField_projection hn s hs (R G) hR y k
  have hC (k : ℕ) : harmonicProjection k C = besselWeight s k • harmonicProjection k V := by
    rw [hV]
    exact ambientBesselField_projection hn s hs (J G) hJ y k
  have hre : U =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (F (frameVector e y v.val)).re :=
    hU ▸ ((ambientSphereL2_ae (R G) hR y).trans
      (Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep v))))
  have him : V =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (F (frameVector e y v.val)).im :=
    hV ▸ ((ambientSphereL2_ae (J G) hJ y).trans
      (Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep v))))
  rw [sobolevSq_eq_bessel_components hn g e y hframe F U V B C hre him s hB hC]
  exact hasSum_positive_bessel_component_pair s U V B C hB hC h₀U h₀V

private theorem partialSobolevSquare_control {s : ℝ} {U V : SphereL2 n} {a : ℝ}
    (h : HasSum (fun k : ℕ => (1+((k+1 : ℕ) : ℝ))^(2*s) *
      (‖harmonicProjection (k+1) U‖^2 + ‖harmonicProjection (k+1) V‖^2)) a) :
    (∀ N, partialSobolevSquare s N U V ≤ a) ∧
      Tendsto (fun N => partialSobolevSquare s N U V) atTop (𝓝 a) :=
  ⟨fun N => sum_le_hasSum (Finset.range N) (fun _ _ => by positivity) h,h.tendsto_sum_nat⟩

namespace HarmonicTestExpansion

variable {Y : Set (X n)} {g : MetricField n} {e : Frame n} {φ : Field n}

private theorem partial_value_control (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) {y : X n} (hy : y ∈ Y) :
    (∀ N, sobolevSq g e s y (fun w => E.partialField N (y,w)) ≤ sobolevSq g e s y (fun w => φ (y,w))) ∧
      Tendsto (fun N => sobolevSq g e s y (fun w => E.partialField N (y,w))) atTop
        (𝓝 (sobolevSq g e s y (fun w => φ (y,w)))) := by
  simp_rw [E.partial_sobolevSquare hn hframe s _ hy]
  exact partialSobolevSquare_control (positive_sobolev_hasSum hn s hs g e y (hframe y hy)
    (fun w => φ (y,w)) E.representative E.representativeSmooth (E.representativeEq y hy)
    (E.realSection y) (E.imagSection y) rfl rfl (E.zeroDegreeReal y) (E.zeroDegreeImag y))

private theorem partial_horizontal_control (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : Test Y g e φ) (i : I n) {y : X n} (hy : y ∈ Y) :
    ((∀ N, fiberSq e y (fun w => horizontal g (E.partialField N) y w (e y i)) ≤
          fiberSq e y (fun w => horizontal g φ y w (e y i))) ∧
      Tendsto (fun N => fiberSq e y (fun w => horizontal g (E.partialField N) y w (e y i))) atTop
        (𝓝 (fiberSq e y (fun w => horizontal g φ y w (e y i))))) ∧
    ((∀ N, sobolevSq g e (1/2) y (fun w => horizontal g (E.partialField N) y w (e y i)) ≤
          sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i))) ∧
      Tendsto (fun N => sobolevSq g e (1/2) y (fun w => horizontal g (E.partialField N) y w (e y i))) atTop
        (𝓝 (sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i))))) := by
  obtain ⟨_,_,_,G,hG,hrep,_⟩ := hφ.exists_smooth_horizontal_representative hY h hK e he hframe i
  let H : X n → ℂ := fun w => horizontal g φ y w (e y i)
  let U := ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y
  let V := ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y
  have hre : U =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (H (frameVector e y v.val)).re :=
    (ambientSphereL2_ae _ _ y).trans (Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v)))
  have him : V =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (H (frameVector e y v.val)).im :=
    (ambientSphereL2_ae _ _ y).trans (Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v)))
  have hU₀ := E.horizontal_zeroDegree_component hY h hK he hframe hφ.1 Complex.reCLM
    E.zeroDegreeReal hy (e y i) U hre
  have hV₀ := E.horizontal_zeroDegree_component hY h hK he hframe hφ.1 Complex.imCLM
    E.zeroDegreeImag hy (e y i) V him
  have hseries (s : ℝ) (hs : s ≤ 2) :=
    positive_sobolev_hasSum hn s hs g e y (hframe y hy) H G hG (hrep y hy) U V rfl rfl hU₀ hV₀
  constructor
  · simp_rw [E.partial_horizontal_fiberSquare hY h hK he hframe hφ.1 hy _ i U V hre him]
    have h₀ := hseries 0 (by norm_num)
    rw [sobolevSq_zero_eq_fiberSq_components hn g e y (hframe y hy) H U V hre him] at h₀
    exact partialSobolevSquare_control h₀
  · simp_rw [E.partial_horizontal_sobolevSquare hY h hK he hframe hφ.1 hy hn _ _ i U V hre him]
    exact partialSobolevSquare_control (hseries (1/2) (by norm_num))

private theorem partial_energy_density_control (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : Test Y g e φ) (r : X n → ℝ) {y : X n} (hy : y ∈ Y) :
    (∀ N, physicalEnergyDensity g e r (E.partialField N) y ≤ physicalEnergyDensity g e r φ y) ∧
      Tendsto (fun N => physicalEnergyDensity g e r (E.partialField N) y) atTop
        (𝓝 (physicalEnergyDensity g e r φ y)) := by
  have hH i := E.partial_horizontal_control hn hY h hK he hframe hφ i hy
  have hV := E.partial_value_control hn hframe 1 (by norm_num) hy
  have hW := E.partial_value_control hn hframe (3/2) (by norm_num) hy
  constructor
  · intro N
    have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hH i).1.1 N)
    have h3 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hH i).2.1 N)
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h1
      (mul_le_mul_of_nonneg_left (hV.1 N) (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hb)))
      (mul_le_mul_of_nonneg_left (hW.1 N) hb)) (Real.sqrt_nonneg _)
  · have h1 := tendsto_finsetSum Finset.univ (fun i _ => (hH i).1.2)
    have h3 := tendsto_finsetSum Finset.univ (fun i _ => (hH i).2.2)
    have h12 := h1.add (hV.2.const_mul ((beta g r y)^2))
    have h123 := h12.add (h3.const_mul ((beta g r y)⁻¹))
    exact (h123.add (hW.2.const_mul (beta g r y))).const_mul (metricDensity g y)

private theorem integrable_partial_density (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X n → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor) (N : ℕ) :
    IntegrableOn (physicalEnergyDensity g e r (E.partialField N)) Y := by
  have hi : IntegrableOn (fun y => ∑ k ∈ Finset.range N, pairedModeDensity g e r (k+1) (E.basis k)
      (E.realCoefficients k) (E.imagCoefficients k) y) Y := by
    apply integrable_finsetSum
    intro k _
    exact (hp.integrable_pairedModeDensity hY h hK e he hfloor (k+1) (E.basis k) (E.realCoefficients k) (E.imagCoefficients k)
      (E.realSmooth k) (E.imagSmooth k) (E.real_compact k) (E.imag_compact k)
      ((E.realSupport k).trans E.supportSubset) ((E.imagSupport k).trans E.supportSubset)).integrableOn
  apply hi.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  exact (physicalEnergyDensity_finiteAngularField hn hY h hK e he hframe r (Finset.range N) (fun k => k+1)
    (fun k _ => by omega) (fun k _ j _ heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2)
    E.realCoefficients E.imagCoefficients (fun k _ => (E.realSmooth k).contDiffOn)
    (fun k _ => (E.imagSmooth k).contDiffOn) hy).symm

/-- The same genuine finite harmonic cutoffs converge in the full frozen energy. -/
theorem tendsto_energySq_partialField (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X n → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor) (hφ : Test Y g e φ) :
    Tendsto (fun N => energySq Y g e r (E.partialField N)) atTop (𝓝 (energySq Y g e r φ)) := by
  simp_rw [energySq_eq_integral_density]
  apply tendsto_integral_of_dominated_convergence (physicalEnergyDensity g e r φ)
    (fun N => (E.integrable_partial_density hn hY h hK he hframe hp hfloor N).aestronglyMeasurable)
    (hp.integrableOn_physicalEnergyDensity hn hY h hK e he hframe hfloor hφ)
  · intro N
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalEnergyDensity_nonneg g e r (E.partialField N) y)]
    exact (E.partial_energy_density_control hn hY h hK he hframe hφ r hy).1 N
  · filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact (E.partial_energy_density_control hn hY h hK he hframe hφ r hy).2

end HarmonicTestExpansion
end CalderonN
