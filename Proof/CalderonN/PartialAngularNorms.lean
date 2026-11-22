module

public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.FiniteAngularNorms
public import Proof.CalderonN.SmoothBesselSections

import Mathlib.Tactic

@[expose] public section

/- The finite cutoff norm comparisons from SpectralEnergyCoordinates and
   SpectralPartialEnergy in Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff Topology

namespace CalderonN

open OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

/-- The first positive angular modes in the protected Sobolev square. -/
def partialSobolevSquare (s : ℝ) (N : ℕ) (U V : SphereL2 n) : ℝ :=
  ∑ k ∈ Finset.range N, (1+((k+1 : ℕ) : ℝ))^(2*s) *
    (‖harmonicProjection (k+1) U‖^2 + ‖harmonicProjection (k+1) V‖^2)

theorem hasSum_positive_bessel_component_pair (s : ℝ) (U V B C : SphereL2 n)
    (hB : ∀ k, harmonicProjection k B = besselWeight s k • harmonicProjection k U)
    (hC : ∀ k, harmonicProjection k C = besselWeight s k • harmonicProjection k V)
    (hU₀ : harmonicProjection 0 U = 0) (hV₀ : harmonicProjection 0 V = 0) :
    HasSum (fun k : ℕ => (1+((k+1:ℕ):ℝ))^(2*s) *
      (‖harmonicProjection (k+1) U‖^2 + ‖harmonicProjection (k+1) V‖^2))
      (‖B‖^2 + ‖C‖^2) := by
  have hh : HasSum (fun k : ℕ => (1+(k:ℝ))^(2*s) *
      (‖harmonicProjection k U‖^2 + ‖harmonicProjection k V‖^2))
      (‖B‖^2 + ‖C‖^2) := by
    simpa only [← mul_add] using
      (hasSum_weighted_harmonicProjection s U B hB).add
        (hasSum_weighted_harmonicProjection s V C hC)
  have hlim := hh.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N+1),
    (1+(k:ℝ))^(2*s)*(‖harmonicProjection k U‖^2+‖harmonicProjection k V‖^2))
    atTop (𝓝 (‖B‖^2+‖C‖^2)) at hlim
  simp only [Finset.sum_range_succ',hU₀,hV₀,norm_zero,zero_pow (by omega : 2 ≠ 0),
    add_zero,mul_zero] at hlim
  exact (hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity) _).mpr hlim

theorem normalizedFischerSquare_eq_projection_norm (k : ℕ) (p : MvPolynomial (I n) ℝ)
    (hp : p ∈ harmonicHomogeneous n k) (u : SphereL2 n)
    (hrep : polynomialSphereL2 p = (harmonicProjection k u : SphereL2 n)) :
    normalizedFischerSquare k p = ‖harmonicProjection k u‖^2 := by
  rw [← polynomialSphereL2_norm_sq (sphereFischerInner n) k p hp,hrep]
  rfl

namespace HarmonicTestExpansion

variable {Y : Set (X n)} {g : MetricField n} {e : Frame n} {φ : Field n}

private theorem normalized_value_square (E : HarmonicTestExpansion Y g e φ)
    (k : ℕ) (y : X n) (c : X n → Fin (E.dimension k) → ℝ) (U : SphereL2 n)
    (hU : polynomialSphereL2 (finitePolynomialField (E.basis k) c y) =
      (harmonicProjection (k+1) U : SphereL2 n)) :
    normalizedFischerSquare (k+1) (finitePolynomialField (E.basis k) c y) =
      ‖harmonicProjection (k+1) U‖^2 :=
  normalizedFischerSquare_eq_projection_norm (k+1) _
    ⟨finitePolynomialField_homogeneous (E.basis k) (fun j => (E.basisHarmonic k j).1) c y,
      finitePolynomialField_harmonic (E.basis k) (fun j => (E.basisHarmonic k j).2) c y⟩ U hU

theorem partial_sobolevSquare (hn : 3 ≤ n) (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (N : ℕ) {y : X n} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => E.partialField N (y,w)) =
      partialSobolevSquare s N (E.realSection y) (E.imagSection y) := by
  change sobolevSq g e s y (fun w => finiteAngularField g e (Finset.range N)
    E.basis E.realCoefficients E.imagCoefficients (y,w)) = _
  rw [sobolevSq_finiteAngularField hn g e y (hframe y hy) s (Finset.range N) (fun k => k+1)
    (fun k _ j _ heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2)]
  unfold partialSobolevSquare
  exact Finset.sum_congr rfl (fun k _ => by
    rw [E.normalized_value_square k y _ _ (E.realCoordinates k y),
      E.normalized_value_square k y _ _ (E.imagCoordinates k y)]
    rfl)

section Horizontal

variable (E : HarmonicTestExpansion Y g e φ)
variable (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
variable (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
variable (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
variable (hφ : smoothNear φ (bundle Y g))
variable {y : X n} (hy : y ∈ Y) (a : X n)

include hY h hK he hframe hφ hy

/-- Express a polynomial component of the horizontal derivative in the
same Hilbert eigenspace as the projection of the smooth test. -/
theorem covariant_polynomial_L2 (k : ℕ) (L : ℂ →L[ℝ] ℝ)
    (c : X n → Fin (E.dimension k) → ℝ) (hc : ContDiff ℝ ∞ c)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField (E.basis k) c x) =
      (harmonicProjection (k+1) (ambientSphereL2 (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth) x) : SphereL2 n))
    (H : SphereL2 n) (hH : H =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => L (horizontal g φ y (frameVector e y v.val) a))) :
    polynomialSphereL2 (covariantPolynomialDerivative g e (E.basis k) c y a) =
      (harmonicProjection (k+1) H : SphereL2 n) := by
  have hU : ContDiff ℝ ∞ (fun x => harmonicProjection (k+1)
      (ambientSphereL2 (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth) x)) :=
    (harmonicProjection (k+1)).contDiff.comp (contDiff_ambientSphereL2 _ _)
  rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe (k+1) (E.basis k)
    (E.basisHarmonic k) c _ hc hU hrep hy a,
    harmonicProjection_horizontal_component hY h hK e he hframe φ hφ E.representative
      E.representativeSmooth E.representativeEq L hy a H hH (k+1)]

private theorem normalized_covariant_square (k : ℕ) (L : ℂ →L[ℝ] ℝ)
    (c : X n → Fin (E.dimension k) → ℝ) (hc : ContDiff ℝ ∞ c)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField (E.basis k) c x) =
      (harmonicProjection (k+1) (ambientSphereL2 (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth) x) : SphereL2 n))
    (H : SphereL2 n) (hH : H =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => L (horizontal g φ y (frameVector e y v.val) a))) :
    normalizedFischerSquare (k+1) (covariantPolynomialDerivative g e (E.basis k) c y a) =
      ‖harmonicProjection (k+1) H‖^2 := by
  have hq : covariantPolynomialDerivative g e (E.basis k) c y a ∈ harmonicHomogeneous n (k+1) :=
    ⟨covariantPolynomialDerivative_homogeneous (by omega) g e (E.basis k)
      (fun j => (E.basisHarmonic k j).1) c y a,
      covariantPolynomialDerivative_harmonic g e (E.basis k)
        (fun j => (E.basisHarmonic k j).2) c y a (frameConnection_skew hY h hK e he hframe hy a)⟩
  exact normalizedFischerSquare_eq_projection_norm (k+1) _ hq H
    (E.covariant_polynomial_L2 hY h hK he hframe hφ hy a k L c hc hrep H hH)

theorem partial_horizontal_sobolevSquare (hn : 3 ≤ n) (s : ℝ) (N : ℕ) (i : I n)
    (U V : SphereL2 n)
    (hU : U =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => (horizontal g φ y (frameVector e y v.val) (e y i)).re))
    (hV : V =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => (horizontal g φ y (frameVector e y v.val) (e y i)).im)) :
    sobolevSq g e s y (fun w => horizontal g (E.partialField N) y w (e y i)) =
      partialSobolevSquare s N U V := by
  change sobolevSq g e s y (fun w => horizontal g (finiteAngularField g e (Finset.range N)
    E.basis E.realCoefficients E.imagCoefficients) y w (e y i)) = _
  rw [sobolevSq_finiteAngularField_horizontal hn hY h hK e he hframe s (Finset.range N)
    (fun k => k+1) (fun k _ => by omega) (fun k _ j _ heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2)
    E.realCoefficients E.imagCoefficients (fun k _ => (E.realSmooth k).contDiffOn)
    (fun k _ => (E.imagSmooth k).contDiffOn) hy i]
  unfold partialSobolevSquare
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [E.normalized_covariant_square hY h hK he hframe hφ hy (e y i) k Complex.reCLM
      (E.realCoefficients k) (E.realSmooth k) (E.realCoordinates k) U hU,
    E.normalized_covariant_square hY h hK he hframe hφ hy (e y i) k Complex.imCLM
      (E.imagCoefficients k) (E.imagSmooth k) (E.imagCoordinates k) V hV]

theorem partial_horizontal_fiberSquare (N : ℕ) (i : I n)
    (U V : SphereL2 n)
    (hU : U =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => (horizontal g φ y (frameVector e y v.val) (e y i)).re))
    (hV : V =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => (horizontal g φ y (frameVector e y v.val) (e y i)).im)) :
    fiberSq e y (fun w => horizontal g (E.partialField N) y w (e y i)) =
      partialSobolevSquare 0 N U V := by
  change fiberSq e y (fun w => horizontal g (finiteAngularField g e (Finset.range N)
    E.basis E.realCoefficients E.imagCoefficients) y w (e y i)) = _
  rw [fiberSq_finiteAngularField_horizontal hY h hK e he hframe (Finset.range N)
    (fun k => k+1) (fun k _ => by omega) (fun k _ j _ heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2)
    E.realCoefficients E.imagCoefficients (fun k _ => (E.realSmooth k).contDiffOn)
    (fun k _ => (E.imagSmooth k).contDiffOn) hy i]
  unfold partialSobolevSquare
  simp only [mul_zero, Real.rpow_zero, one_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [E.normalized_covariant_square hY h hK he hframe hφ hy (e y i) k Complex.reCLM
      (E.realCoefficients k) (E.realSmooth k) (E.realCoordinates k) U hU,
    E.normalized_covariant_square hY h hK he hframe hφ hy (e y i) k Complex.imCLM
      (E.imagCoefficients k) (E.imagSmooth k) (E.imagCoordinates k) V hV]

end Horizontal
end HarmonicTestExpansion
end CalderonN
