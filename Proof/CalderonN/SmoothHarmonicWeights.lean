module

public import Proof.CalderonN.SmoothAmbientAngularCasimir
public import Proof.CalderonN.HarmonicMultiplier
public import Proof.CalderonN.SmoothZonalSobolev

import Mathlib.Tactic

public section

/- Adapted from the smooth Bessel fields in Proposition 5.3 release f308cb9d.
   The weight denominator uses the actual dimension-n Casimir. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

@[expose] def besselWeight (s : ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ s

lemma besselWeight_nonneg (s : ℝ) (k : ℕ) : 0 ≤ besselWeight s k :=
  Real.rpow_nonneg (by positivity) _

lemma besselWeight_square (s : ℝ) (k : ℕ) :
    (besselWeight s k)^2 = (1 + (k : ℝ))^(2*s) := by
  rw [besselWeight, ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

@[expose] def casimirWeight (n k : ℕ) : ℝ := 1 + (k : ℝ) * ((k : ℝ) + n - 2)

lemma casimirWeight_pos (hn : 3 ≤ n) (k : ℕ) : 0 < casimirWeight n k := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hterm : 0 ≤ (k : ℝ) + n - 2 := by linarith
  unfold casimirWeight
  linarith [mul_nonneg hk hterm]

private theorem besselCasimirRatio_bound (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2) (k : ℕ) :
    |besselWeight s k / casimirWeight n k| ≤ 2 := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_div, abs_of_nonneg (besselWeight_nonneg _ _), abs_of_pos (casimirWeight_pos hn _),
    div_le_iff₀ (casimirWeight_pos hn _)]
  calc
    besselWeight s k ≤ (1+(k : ℝ))^2 := by
      unfold besselWeight
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    _ ≤ 2 * casimirWeight n k := by
      unfold casimirWeight
      nlinarith [mul_nonneg hk (sub_nonneg.mpr hn')]

/-- A single shifted Casimir derivative controls every Bessel lift of order at most two. -/
def ambientBesselField (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (G : X n × X n → ℝ) (hG : ContDiff ℝ ∞ G) (y : X n) : SphereL2 n :=
  harmonicMultiplier (fun k => besselWeight s k / casimirWeight n k) 2
    (by norm_num) (besselCasimirRatio_bound hn s hs)
    (ambientSphereL2 (ambientShiftedAngularCasimir G) (contDiff_ambientShiftedAngularCasimir G hG) y)

theorem ambientBesselField_projection (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (G : X n × X n → ℝ) (hG : ContDiff ℝ ∞ G) (y : X n) (k : ℕ) :
    harmonicProjection k (ambientBesselField hn s hs G hG y) =
      besselWeight s k • harmonicProjection k (ambientSphereL2 G hG y) := by
  rw [ambientBesselField, harmonicProjection_harmonicMultiplier,
    ambientSphereL2_eq_smoothSphereLift, ambientSphereL2_eq_smoothSphereLift]
  have he := ambientShiftedAngularCasimir_slice G hG y
  have hLift : smoothSphereLift (fun z => ambientShiftedAngularCasimir G (y,z))
      (contDiff_angular_slice _ (contDiff_ambientShiftedAngularCasimir G hG) y) =
      smoothSphereLift (shiftedAngularCasimir (fun z => G (y,z)))
        (contDiff_shiftedAngularCasimir _ (contDiff_angular_slice G hG y)) := by
    unfold smoothSphereLift
    congr 1
    ext z
    exact congrFun he z.val
  rw [hLift, harmonicProjection_shiftedAngularCasimir, smul_smul]
  change (besselWeight s k / casimirWeight n k * casimirWeight n k) • _ = _
  rw [div_mul_cancel₀ _ (casimirWeight_pos hn k).ne']

theorem contDiff_ambientBesselField (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (G : X n × X n → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientBesselField hn s hs G hG) :=
  (harmonicMultiplier _ _ _ _).contDiff.comp (contDiff_ambientSphereL2 _ _)

theorem ambientBesselField_zero (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (G : X n × X n → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set (X n))
    (hzero : ∀ y ∉ K, ∀ v : UnitSphere n, G (y,v.val) = 0) (y : X n) (hy : y ∉ K) :
    ambientBesselField hn s hs G hG y = 0 := by
  rw [ambientBesselField, ambientSphereL2_eq_zero _ _ _
    (ambientShiftedAngularCasimir_sphere_zero G hG K hzero y hy), map_zero]

theorem hasSum_weighted_harmonicProjection (s : ℝ) (u b : SphereL2 n)
    (h : ∀ k, harmonicProjection k b = besselWeight s k • harmonicProjection k u) :
    HasSum (fun k : ℕ => (1+(k : ℝ))^(2*s) * ‖harmonicProjection k u‖^2) (‖b‖^2) := by
  have hb := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (sphereHarmonicDecomposition b)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    sphereHarmonicDecomposition_apply] at hb
  simpa only [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (besselWeight_nonneg s _), mul_pow,
    besselWeight_square] using hb

end CalderonN
