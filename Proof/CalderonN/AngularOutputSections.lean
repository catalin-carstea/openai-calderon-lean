module

public import Proof.CalderonN.BoundedHarmonicShift

import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

private theorem degreeBesselRatio_le (hn : 3 ≤ n) (k : ℕ) :
    |((k : ℝ)+1) * k / casimirWeight n k| ≤ 1 := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_of_nonneg (div_nonneg (by positivity) (casimirWeight_pos hn k).le),
    div_le_iff₀ (casimirWeight_pos hn k), one_mul]
  unfold casimirWeight
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hn')]

/-- The degree operator followed by one Bessel weight on a smooth sphere field. -/
private def ambientDegreeBessel (hn : 3 ≤ n) (G : X n × X n → ℝ)
    (hG : ContDiff ℝ ∞ G) (y : X n) : SphereL2 n :=
  harmonicMultiplier (fun k => ((k : ℝ)+1) * k / casimirWeight n k) 1
    (by norm_num) (degreeBesselRatio_le hn)
    (ambientSphereL2 (ambientShiftedAngularCasimir G) (contDiff_ambientShiftedAngularCasimir G hG) y)

private theorem ambientDegreeBessel_projection (hn : 3 ≤ n) (G : X n × X n → ℝ)
    (hG : ContDiff ℝ ∞ G) (y : X n) (k : ℕ) :
    harmonicProjection k (ambientDegreeBessel hn G hG y) =
      (((k : ℝ)+1) * k) • harmonicProjection k (ambientSphereL2 G hG y) := by
  rw [ambientDegreeBessel, harmonicProjection_harmonicMultiplier,
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
  change ((((k : ℝ)+1)*k) / casimirWeight n k * casimirWeight n k) • _ = _
  rw [div_mul_cancel₀ _ (casimirWeight_pos hn k).ne']

private theorem contDiff_ambientDegreeBessel (hn : 3 ≤ n) (G : X n × X n → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientDegreeBessel hn G hG) :=
  (harmonicMultiplier _ _ _ _).contDiff.comp (contDiff_ambientSphereL2 _ _)

private theorem ambientDegreeBessel_zero (hn : 3 ≤ n) (G : X n × X n → ℝ)
    (hG : ContDiff ℝ ∞ G) (S : Set (X n)) (hzero : ∀ y ∉ S, ∀ v : UnitSphere n, G (y,v.val) = 0)
    (y : X n) (hy : y ∉ S) : ambientDegreeBessel hn G hG y = 0 := by
  rw [ambientDegreeBessel, ambientSphereL2_eq_zero _ _ _
    (ambientShiftedAngularCasimir_sphere_zero G hG S hzero y hy), map_zero]

/-- The degree-k component of the signed horizontal input to the angular model. -/
@[expose] def weightedAngularComponent (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (sign : ℝ) (y : X n) (k : ℕ) : harmonicSphereSubspace n k :=
  sign • harmonicProjection k (ambientSphereL2 H hH y) +
    (b y * (k : ℝ)) • harmonicProjection k (ambientSphereL2 G hG y)

private def weightedAngularBesselSection (hn : 3 ≤ n)
    (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (sign : ℝ) (y : X n) : SphereL2 n :=
  sign • ambientBesselField hn 1 (by norm_num) H hH y + b y • ambientDegreeBessel hn G hG y

private theorem weightedAngularBesselSection_projection (hn : 3 ≤ n)
    (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (sign : ℝ) (y : X n) (k : ℕ) :
    harmonicProjection k (weightedAngularBesselSection hn H G hH hG b sign y) =
      ((k : ℝ)+1) • weightedAngularComponent H G hH hG b sign y k := by
  rw [weightedAngularBesselSection, weightedAngularComponent, map_add, map_smul, map_smul,
    ambientBesselField_projection, ambientDegreeBessel_projection, smul_add]
  simp only [besselWeight, Real.rpow_one, smul_smul, add_comm (1 : ℝ) (k : ℝ)]
  congr 2 <;> ring

private theorem contDiff_weightedAngularBesselSection (hn : 3 ≤ n)
    (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (hb : ContDiff ℝ ∞ b) (sign : ℝ) :
    ContDiff ℝ ∞ (weightedAngularBesselSection hn H G hH hG b sign) :=
  ((contDiff_ambientBesselField hn _ (by norm_num) H hH).const_smul sign).add
    (hb.smul (contDiff_ambientDegreeBessel hn G hG))

private theorem weightedAngularBesselSection_zero (hn : 3 ≤ n)
    (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (sign : ℝ) (S : Set (X n))
    (hHz : ∀ y ∉ S,∀ v : UnitSphere n,H (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere n,G (y,v.val) = 0) {y : X n} (hy : y ∉ S) :
    weightedAngularBesselSection hn H G hH hG b sign y = 0 := by
  rw [weightedAngularBesselSection, ambientBesselField_zero hn _ _ H hH S hHz y hy,
    ambientDegreeBessel_zero hn G hG S hGz y hy, smul_zero, smul_zero, add_zero]

variable (hn : 3 ≤ n)
variable (H : I n → X n × X n → ℝ) (G : X n × X n → ℝ)
variable (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
variable (b : I n → X n → ℝ)

def angularRaisingSum (y : X n) : SphereL2 n :=
  ∑ i, normalizedRaising i (weightedAngularBesselSection hn (H i) G (hH i) hG (b i) 1 y)

def angularLoweringSum (y : X n) : SphereL2 n :=
  ∑ i, normalizedLowering i (weightedAngularBesselSection hn (H i) G (hH i) hG (b i) (-1) y)

theorem harmonicProjection_angularRaisingSum_zero (y : X n) :
    harmonicProjection 0 (angularRaisingSum hn H G hH hG b y) = 0 := by
  rw [angularRaisingSum, map_sum]
  simp only [normalizedRaising_projection_zero, Finset.sum_const_zero]

theorem harmonicProjection_angularRaisingSum_succ (y : X n) (k : ℕ) :
    harmonicProjection (k+1) (angularRaisingSum hn H G hH hG b y) =
      ∑ i,harmonicDerivativeAdjoint (sphereFischerInner n) k i
        (weightedAngularComponent (H i) G (hH i) hG (b i) 1 y k) := by
  rw [angularRaisingSum,map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normalizedRaising_projection_succ, weightedAngularBesselSection_projection,
    map_smul, smul_smul, inv_mul_cancel₀ (by positivity : (k : ℝ)+1 ≠ 0), one_smul]

theorem harmonicProjection_angularLoweringSum (y : X n) (k : ℕ) :
    harmonicProjection k (angularLoweringSum hn H G hH hG b y) =
      ∑ i,harmonicDerivative (sphereFischerInner n) k i
        (weightedAngularComponent (H i) G (hH i) hG (b i) (-1) y (k+1)) := by
  rw [angularLoweringSum,map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normalizedLowering_projection, weightedAngularBesselSection_projection, map_smul, smul_smul]
  rw [show ((k+1 : ℕ) : ℝ)+1 = (k:ℝ)+2 by push_cast; ring,
    inv_mul_cancel₀ (by positivity : (k : ℝ)+2 ≠ 0), one_smul]

theorem contDiff_angularRaisingSum (hb : ∀ i, ContDiff ℝ ∞ (b i)) :
    ContDiff ℝ ∞ (angularRaisingSum hn H G hH hG b) :=
  ContDiff.sum fun i _ => (normalizedRaising i).contDiff.comp
    (contDiff_weightedAngularBesselSection hn (H i) G (hH i) hG (b i) (hb i) 1)

theorem contDiff_angularLoweringSum (hb : ∀ i, ContDiff ℝ ∞ (b i)) :
    ContDiff ℝ ∞ (angularLoweringSum hn H G hH hG b) :=
  ContDiff.sum fun i _ => (normalizedLowering i).contDiff.comp
    (contDiff_weightedAngularBesselSection hn (H i) G (hH i) hG (b i) (hb i) (-1))

theorem angularRaisingSum_zero (S : Set (X n))
    (hHz : ∀ i,∀ y ∉ S,∀ v : UnitSphere n,H i (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere n,G (y,v.val) = 0) {y : X n} (hy : y ∉ S) :
    angularRaisingSum hn H G hH hG b y = 0 := by
  unfold angularRaisingSum
  simp only [weightedAngularBesselSection_zero hn _ _ _ _ _ _ S
    (hHz _) hGz hy,map_zero,Finset.sum_const_zero]

theorem angularLoweringSum_zero (S : Set (X n))
    (hHz : ∀ i,∀ y ∉ S,∀ v : UnitSphere n,H i (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere n,G (y,v.val) = 0) {y : X n} (hy : y ∉ S) :
    angularLoweringSum hn H G hH hG b y = 0 := by
  unfold angularLoweringSum
  simp only [weightedAngularBesselSection_zero hn _ _ _ _ _ _ S
    (hHz _) hGz hy,map_zero,Finset.sum_const_zero]

end CalderonN
