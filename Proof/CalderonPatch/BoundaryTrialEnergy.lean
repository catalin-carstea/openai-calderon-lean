module

public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.WeakDirichletEnergy

import Proof.CalderonPatch.GlobalStationarity
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold NNReal ENNReal

namespace CalderonPatch

open CalderonN (X I chartVolume coordDeriv)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "J" => 𝓡∂ (n+1)
local notation "R" => 𝓘(ℝ, ℝ)
local notation "Z" => X (n+1)

/-- The volume Green pairing of a smooth trial extension equals
its exact bottom-face flux. -/
theorem boundaryTrialGreen_eq_flux {g : SmoothMetric (n+1) M}
    {p : M} (D : NativeBoundaryMetricChart g p) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {U : Set Z} (hU : IsOpen U) (hUD : U ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) U)
    {f : Z → ℝ} (hf : ContDiff ℝ ∞ f) (hfC : HasCompactSupport f)
    (hSupp : tsupport f ∩ inwardHalfSpace (n+1) ⊆ normalHalfBox l r) :
    let u := boundaryChartTest D f
    let face (z : I n → ℝ) := normalFacePoint (WithLp.toLp 2 z)
    (∫ x, u x * nativeLaplace g u x + covectorEnergy g x (mfderiv J R u x) ∂μ) =
      -∫ z in Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0),
        f (face z) * (chartVolume D.field (face z) * coordDeriv 0 f (face z)) := by
  let u := boundaryChartTest D f
  let H := inwardHalfSpace (n+1)
  have hAmbient : U ∩ H ⊆ D.coord.target := by
    rw [D.target_eq]
    exact inter_subset_inter_left _ hUD
  have hT : tsupport f ∩ H ⊆ D.coord.target := by
    intro x hx
    have h := hBox (normalHalfBox_subset_closedBox hl0 (hSupp hx))
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ U at h
    rw [WithLp.toLp_ofLp] at h
    exact hAmbient ⟨h,hx.2⟩
  have hu : ContMDiff J R ∞ u := contMDiff_boundaryChartTest D hf hfC hT
  have hu0 := (boundaryChartTest_comp_inverse D f).mono hAmbient
  have h := integral_nativeGreenPairing_normalHalfBox D μ hμ hlr hl0 hU hUD hBox hu hu
      hf.contDiffOn hf.contDiffOn hu0 hu0 (tsupport_boundaryChartTest_subset_halfBox D hl0
        (hBox.mono_right hUD) hfC hSupp)
  simpa only [energyPairingDensity_self,u,normalFacePoint,WithLp.ofLp_toLp] using h

variable [PreconnectedSpace M]

/-- A uniform bound for the Laplacian gives both a quadratic correction
to the measured energy and a linear bound for the volume pairing. -/
theorem DirichletData.abs_dirichletQuadraticEnergy_sub_green_le (D : DirichletData n M)
    {f : M → ℝ} (hf : ContMDiff J R ∞ f) {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (hF : ∀ x, |f x| ≤ A) (hL : ∀ x, |nativeLaplace D.metric f x| ≤ e) :
    |dirichletQuadraticEnergy D.metric D.volume f -
      (∫ x, f x * nativeLaplace D.metric f x +
        covectorEnergy D.metric x (mfderiv J R f x) ∂D.volume)| ≤
      ‖D.l2Value‖ ^ 2 *
        ((((measureUnivNNReal D.volume) ^ ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) * e) ^ 2 +
        (D.volume univ).toReal * (A * e) := by
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  have hN : ‖D.positiveLaplaceLp f hf‖ ≤
      (((measureUnivNNReal D.volume) ^ ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) * e := by
    apply Lp.norm_le_of_ae_bound he
    filter_upwards [D.positiveLaplaceLp_ae_eq f hf] with x hx
    rw [hx,Pi.neg_apply,norm_neg,Real.norm_eq_abs]
    exact hL x
  have hE := (D.abs_dirichletQuadraticEnergy_sub_trial_le f hf).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hN 2) (sq_nonneg _))
  have hI : |∫ x, f x * nativeLaplace D.metric f x ∂D.volume| ≤
      (D.volume univ).toReal * (A * e) := by
    rw [← Real.norm_eq_abs,mul_comm]
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hF x) (hL x) (abs_nonneg _) hA)
  rw [integral_add (integrable_mul_nativeLaplace D.metric D.volume D.metric_volume hf hf)
    ((integrable_energyPairingDensity D.metric D.volume D.metric_volume hf hf).congr
      (Eventually.of_forall (energyPairingDensity_self D.metric f)))]
  calc
    _ ≤ |dirichletQuadraticEnergy D.metric D.volume f -
        (∫ x, covectorEnergy D.metric x (mfderiv J R f x) ∂D.volume)| +
        |∫ x, f x * nativeLaplace D.metric f x ∂D.volume| := by
      rw [add_comm (∫ x, f x * nativeLaplace D.metric f x ∂D.volume), ← sub_sub]
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (dirichletQuadraticEnergy D.metric D.volume f -
          (∫ x, covectorEnergy D.metric x (mfderiv J R f x) ∂D.volume))
          (-(∫ x, f x * nativeLaplace D.metric f x ∂D.volume))
    _ ≤ _ := add_le_add hE hI

end CalderonPatch
