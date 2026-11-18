import Proof.ActualRotatedWeakOperatorTaylorData
import Proof.NativeEllipticWeakData
import Proof.WeakFirstVariationDerivative
import Proof.CommonSupportWeakConormalTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift weakFirstPoissonVariationL

def weakRotationConormalDerivativeBudget (KP C0 CT P Q : ℝ) : ℝ :=
  let CI := 5*metricDensityBudget KP*KP
  let CA := metricDensityBudget KP*KP
  let N := ‖fixedHarmonicH1LiftL‖
  let DB := 9*(P+Q)
  let V1 := 9*P
  let CS := CI*(9*Q+C0*DB*V1)*N
  let DS := CI*((CT+CT*C0*V1+DB*C0*CT)*N+CT*CS)
  let CP1 := C0*V1*N
  let DP1 := C0*CT*N
  sphereSurfaceMass⁻¹*N*(CT*CS+CA*DS+CT*CP1+DB*DP1+CT*N)

lemma weakRotationConormalDerivativeBudget_nonneg (KP C0 CT P Q : ℝ)
    (hKP : 1 ≤ KP) (hC0 : 0 ≤ C0) (hCT : 0 ≤ CT) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ weakRotationConormalDerivativeBudget KP C0 CT P Q := by
  have hKP0 : 0 ≤ KP := le_trans zero_le_one hKP
  have hMass : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  unfold weakRotationConormalDerivativeBudget metricDensityBudget
  positivity

private lemma coefficient_affine_difference_bound
    (a a1 : X → Mat) (c r P Q : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hFirst : ∀ z ∈ (ballOpens:Set X),∀ i j,|a1 z i j| ≤ P)
    (hR : ∀ z ∈ (ballOpens:Set X),∀ i j,|(a z-c • (1:Mat)-r • a1 z) i j| ≤ Q*r^2) :
    ∀ z ∈ (ballOpens:Set X),∀ i j,|a z i j-(c • (1:Mat)) i j| ≤ (P+Q)*r := by
  intro z hz i j
  have hAlg : a z i j-(c • (1:Mat)) i j = (a z-c • (1:Mat)-r • a1 z) i j+r*a1 z i j := by
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [hAlg]
  calc
    _ ≤ |(a z-c • (1:Mat)-r • a1 z) i j|+|r*a1 z i j| := abs_add_le _ _
    _ ≤ Q*r^2+r*P := add_le_add (hR z hz i j) (by
      rw [abs_mul,abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left (hFirst z hz i j) hr)
    _ ≤ Q*r+r*P := by
      have hrr : r^2 ≤ r := by nlinarith
      exact add_le_add (mul_le_mul_of_nonneg_left hrr hQ) (le_refl _)
    _ = _ := by ring

/-- The actual rotated elliptic coefficient and its genuine first model give
    a quadratic conormal Taylor derivative through the same native weak inverse. -/
theorem norm_rotated_commonSupportWeakConormal_taylor_derivative_le
    (H : MetricField) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP H) (i j : I)
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (c r C0 CT P Q : ℝ) (hc : 0 < c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hC0 : 0 ≤ C0) (hCT : 0 ≤ CT) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hRep : ∀ θ z,z ∈ (ballOpens:Set X) → a (θ,z) = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z))
    (hFirst : ∀ z ∈ (ballOpens:Set X),∀ k l,|a1 (0,z) k l| ≤ P)
    (hTaylor : ∀ z ∈ (ballOpens:Set X),∀ k l,|(a (0,z)-c • (1:Mat)-r • a1 (0,z)) k l| ≤ Q*r^2)
    (hI0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hDA : ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ CT*r)
    (hDE : ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ CT*r)
    (hDT1 : ‖fderiv ℝ (commonSupportWeakEnergy a1 ha1) 0‖ ≤ CT)
    (hDQWeak : ‖fderiv ℝ (fun θ => commonSupportWeakEnergy a ha θ-
      nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)-
      r • commonSupportWeakEnergy a1 ha1 θ) 0‖ ≤ CT*r^2)
    (hDQFull : ‖fderiv ℝ (fun θ => commonSupportFullWeakEnergy a ha θ-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound c)-r • commonSupportFullWeakEnergy a1 ha1 θ) 0‖ ≤ CT*r^2) :
    ‖fderiv ℝ (fun θ => commonSupportWeakConormalEndpoint a ha θ-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)) 0‖ ≤
      weakRotationConormalDerivativeBudget KP C0 CT P Q*r^2 := by
  let CI := 5*metricDensityBudget KP*KP
  let CA := metricDensityBudget KP*KP
  let N := ‖fixedHarmonicH1LiftL‖
  let DB := 9*(P+Q)
  let V1 := 9*P
  let CS := CI*(9*Q+C0*DB*V1)*N
  let DS := CI*((CT+CT*C0*V1+DB*C0*CT)*N+CT*CS)
  let CP1 := C0*V1*N
  let DP1 := C0*CT*N
  have hKP0 : 0 ≤ KP := le_trans zero_le_one hKP
  have hCI : 0 ≤ CI := by dsimp [CI,metricDensityBudget];positivity
  have hCA : 0 ≤ CA := by dsimp [CA,metricDensityBudget];positivity
  have hDB : 0 ≤ DB := by dsimp [DB];positivity
  have hV1 : 0 ≤ V1 := by dsimp [V1];positivity
  have hCS : 0 ≤ CS := by dsimp only [CS,N];positivity
  have hDS : 0 ≤ DS := by dsimp only [DS,N];positivity
  have hCP1 : 0 ≤ CP1 := by dsimp only [CP1,N];positivity
  have hDP1nonneg : 0 ≤ DP1 := by dsimp only [DP1,N];positivity
  have hNative (θ : ℝ) : NativeWeakEnergyData (fun z => a (θ,z)) CI CA := by
    have hCont : Continuous (fun z => a (θ,z)) := ha.continuous.comp
      (continuous_const.prodMk continuous_id)
    exact nativeWeakEnergyData_of_rotated_coefficient H KP hKP hEll i j θ
      (fun z => a (θ,z)) hCont (hRep θ)
  have hInv (θ : ℝ) : (commonSupportZeroWeakEnergy a ha θ).IsInvertible :=
    nativeZeroCoefficientEnergy_isInvertible (a:=fun z => a (θ,z)) (commonSupportEnergyMemLp a ha θ) (hNative θ).coercive
  have hFlat := flat_native_weak_energy_data c hc
  have hInv0 : (nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).IsInvertible :=
    nativeZeroCoefficientEnergy_isInvertible (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c) hFlat.coercive
  have hNI : ‖(commonSupportZeroWeakEnergy a ha 0).inverse‖ ≤ CI := by
    change ‖(nativeZeroCoefficientEnergyL (fun z => a (0,z)) 0 0 (commonSupportEnergyMemLp a ha 0)).inverse‖ ≤ CI
    rw [nativeZeroCoefficientEnergy_inverse_eq (a:=fun z => a (0,z))]
    exact (hNative 0).inverse_bound
  have hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).inverse‖ ≤ C0 := by
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    exact hI0
  have hDiff := coefficient_affine_difference_bound (fun z => a (0,z)) (fun z => a1 (0,z)) c r P Q
    hr hr1 hP hQ hFirst hTaylor
  have hNB : ‖commonSupportZeroWeakEnergy a ha 0-
      nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ DB*r :=
    (norm_nativeZeroCoefficientEnergy_sub_le (a:=fun z => a (0,z)) (a0:=fun _ : X => c • (1:Mat))
      (commonSupportEnergyMemLp a ha 0) (flatCoefficientBound c) ((P+Q)*r) (by positivity) hDiff).trans_eq (by dsimp [DB];ring)
  have hEDiff : ‖commonSupportFullWeakEnergy a ha 0-TauCeti.PDE.energyFormH1L (flatCoefficientBound c)‖ ≤ DB*r :=
    (norm_unitBall_full_energyForm_sub_le (a:=fun z => a (0,z)) (a0:=fun _ : X => c • (1:Mat))
      (commonSupportEnergyMemLp a ha 0) (flatCoefficientBound c) ((P+Q)*r) (by positivity) hDiff).trans_eq (by dsimp [DB];ring)
  have hNV1 : ‖commonSupportWeakEnergy a1 ha1 0‖ ≤ V1 :=
    (norm_nativeWeakEnergyL_of_entries (a:=fun z => a1 (0,z)) (commonSupportEnergyMemLp a1 ha1 0) P hP hFirst).2
  have hFirstNorm : ‖weakFirstPoissonVariationL c (fun z => a1 (0,z)) (commonSupportEnergyMemLp a1 ha1 0)‖ ≤ CP1 :=
    norm_weakFirstPoissonVariationL_le (a1:=fun z => a1 (0,z)) c (commonSupportEnergyMemLp a1 ha1 0)
      C0 P hC0 hP hI0 hFirst
  have hBulkPoint : ‖commonSupportWeakHalfLift a ha 0-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (fun z => a1 (0,z)) (commonSupportEnergyMemLp a1 ha1 0)‖ ≤ CS*r^2 :=
    norm_nativeWeakHalfLift_first_remainder_le (a:=fun z => a (0,z)) (a1:=fun z => a1 (0,z))
      (commonSupportEnergyMemLp a ha 0) (commonSupportEnergyMemLp a1 ha1 0) c r CI C0 (P+Q) P Q
      hr hCI hC0 (add_nonneg hP hQ) hP hQ (hNative 0).coercive hFlat.coercive
      (hNative 0).inverse_bound hI0 hDiff hFirst hTaylor
  have hADiff := (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).differentiable (by simp) 0
  have hTDiff := (contDiff_commonSupportWeakEnergy a ha S hS hz).differentiable (by simp) 0
  have hT1Diff := (contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hEDiffAt := (contDiff_commonSupportFullWeakEnergy a ha S hS hz).differentiable (by simp) 0
  have hE1Diff := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hPOn := contDiffOn_commonSupportWeakHalfLift a ha S hS hz Set.univ (fun θ _ => hInv θ)
  have hPSmooth : ContDiff ℝ ∞ (commonSupportWeakHalfLift a ha) := contDiffOn_univ.mp hPOn
  have hPDiff := hPSmooth.differentiable (by simp) 0
  have hP1Theorem := commonSupport_weakFirstPoisson_derivative a1 ha1 c 0 hT1Diff C0 CT hC0 hCT hI0 hDT1
  obtain ⟨hP1Diff,hDP1⟩ := hP1Theorem
  have hBulkDerivative : ‖fderiv ℝ (fun θ => commonSupportWeakHalfLift a ha θ-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)) 0‖ ≤ DS*r^2 := by
    have hBound := norm_nativeWeakHalfLift_first_remainder_derivative_le (P:=ℝ)
      (fun θ z => a (θ,z)) (fun θ z => a1 (θ,z))
      (commonSupportEnergyMemLp a ha) (commonSupportEnergyMemLp a1 ha1)
      c r 0 Set.univ isOpen_univ (mem_univ _) (fun θ _ => hInv θ) hInv0 hADiff hTDiff hT1Diff
      CI C0 CT DB V1 CT CT CS hr hr1 hCI hC0 hCT hDB hV1 hCT hCT hCS
      hNI hNI0 hDA hNB hNV1 hDT1 hDQWeak hBulkPoint
    exact hBound
  have hNE : ‖commonSupportFullWeakEnergy a ha 0‖ ≤ CA := (hNative 0).energy_bound
  have hFinal := norm_commonSupportWeakConormal_first_remainder_derivative_le
    a a1 ha ha1 c r 0 CA CT DB CP1 DP1 CS DS CT
    hEDiffAt hE1Diff hPDiff hP1Diff hr hr1 hCA hCT hDB hCP1 hDP1nonneg hCS hDS hCT
    hNE hDE hEDiff hFirstNorm hDP1 hBulkPoint hBulkDerivative hDQFull
  exact hFinal

end ShrinkingSpheres
