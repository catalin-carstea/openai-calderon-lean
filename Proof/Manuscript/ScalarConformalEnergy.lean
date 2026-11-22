module

public import Proof.Manuscript.ScalarConductivityDefs

import Proof.CalderonPatch.MetricDualEnergy
import Proof.CalderonPatch.BoundaryMetric
import Proof.CalderonN.MetricCalculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Bundle Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

open CalderonPatch
open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- Multiply a Riemannian metric by a smooth positive function. -/
def scaleSmoothMetric (g : SmoothMetric n M) (a : M → ℝ)
    (ha : ContMDiff J R ∞ a) (hpos : ∀ x, 0 < a x) : SmoothMetric n M where
  inner x := a x • g.inner x
  symm x v w := by simp only [smul_apply, smul_eq_mul, g.symm x v w]
  pos x v hv := by
    change 0 < a x * g.inner x v v
    exact mul_pos (hpos x) (g.pos x v hv)
  isVonNBounded x := by
    let t := Real.sqrt (a x)
    have ht : 0 < t := Real.sqrt_pos.mpr (hpos x)
    have ht₂ : t * t = a x := Real.mul_self_sqrt (hpos x).le
    let L : TangentSpace J x →L[ℝ] TangentSpace J x :=
      t⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace J x)
    apply (g.isVonNBounded x).image L |>.subset
    intro v hv
    refine ⟨t • v, ?_, ?_⟩
    · change g.inner x (t • v) (t • v) < 1
      change a x * g.inner x v v < 1 at hv
      simp only [map_smul, smul_apply, smul_eq_mul]
      rwa [← mul_assoc, ht₂]
    · simp [L, smul_smul, mul_inv_cancel₀ ht.ne']
  contMDiff := by
    exact ha.smul_section g.contMDiff

theorem covectorEnergy_scaleSmoothMetric (g : SmoothMetric n M) (a : M → ℝ)
    (ha : ContMDiff J R ∞ a) (hpos : ∀ x, 0 < a x)
    (x : M) (d : TangentSpace J x →L[ℝ] ℝ) :
    covectorEnergy (scaleSmoothMetric g a ha hpos) x d = (a x)⁻¹ * covectorEnergy g x d := by
  let G := scaleSmoothMetric g a ha hpos
  let v := metricDual g x d
  have hdu : metricDual G x d = (a x)⁻¹ • v := by
    apply (existsUnique_metricDual G x d).unique (metricDual_spec G x d)
    intro w
    change (a x • g.inner x) ((a x)⁻¹ • v) w = d w
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (hpos x).ne', one_mul]
    exact metricDual_spec g x d w
  change covectorEnergy G x d = _
  rw [covectorEnergy_eq_metricDual, covectorEnergy_eq_metricDual, hdu]
  change a x * g.inner x ((a x)⁻¹ • v) ((a x)⁻¹ • v) = (a x)⁻¹ * g.inner x v v
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp [(hpos x).ne']

private theorem map_withDensity_from_comp {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {f : A → C} (hf : AEMeasurable f μ)
    {a : A → ℝ≥0∞} (ha : AEMeasurable a μ)
    {b : C → ℝ≥0∞} (hb : AEMeasurable b (μ.map f))
    (hread : a =ᵐ[μ] b ∘ f) :
    (μ.withDensity a).map f = (μ.map f).withDensity b := by
  ext1 s hs
  have hs' : Measurable (s.indicator (1 : C → ℝ≥0∞)) := measurable_const.indicator hs
  have hf' := hf.mono_ac (withDensity_absolutelyContinuous μ a)
  calc
    _ = ∫⁻ y, s.indicator (1 : C → ℝ≥0∞) y ∂(μ.withDensity a).map f :=
      (lintegral_indicator_one hs).symm
    _ = ∫⁻ x, s.indicator (1 : C → ℝ≥0∞) (f x) ∂μ.withDensity a :=
      lintegral_map' hs'.aemeasurable hf'
    _ = ∫⁻ x, a x * s.indicator (1 : C → ℝ≥0∞) (f x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul₀ ha (hs'.comp_aemeasurable hf)
    _ = ∫⁻ x, s.indicator b (f x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hread] with x hx
      change a x = b (f x) at hx
      by_cases hm : f x ∈ s <;> simp [hx, hm]
    _ = ∫⁻ y, s.indicator b y ∂μ.map f := (lintegral_map' (hb.indicator hs) hf).symm
    _ = _ := by rw [lintegral_indicator hs, withDensity_apply _ hs]

def expScaledMetric (g : SmoothMetric n M) (ψ : M → ℝ) (hψ : ContMDiff J R ∞ ψ) :
    SmoothMetric n M :=
  scaleSmoothMetric g (fun x => Real.exp (2 * ψ x))
    ((contMDiff_iff_contDiff.mpr ((Real.contDiff_exp (n := ∞)).comp
      (contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun z : ℝ => 2 * z))).comp hψ)
    (fun _ => Real.exp_pos _)

variable [MeasurableSpace M] [BorelSpace M]

def expScaledVolume (μ : Measure M) (ψ : M → ℝ) : Measure M :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp ((n : ℝ) * ψ x)))

theorem isMetricVolume_expScaled (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) (ψ : M → ℝ) (hψ : ContMDiff J R ∞ ψ) :
    IsMetricVolume (expScaledMetric g ψ hψ) (expScaledVolume (n := n) μ ψ) := by
  intro p
  let e := extChartAt J p
  let μc := μ.restrict e.source
  let μE : Measure (X n) := volume.restrict e.target
  let G := expScaledMetric g ψ hψ
  let a (y : X n) := ENNReal.ofReal (Real.sqrt (chartMetric g p y).det)
  let b (y : X n) := ENNReal.ofReal (Real.sqrt (chartMetric G p y).det)
  let ρ (x : M) := ENNReal.ofReal (Real.exp ((n : ℝ) * ψ x))
  let d (y : X n) := ρ (e.symm y)
  have hρ : Continuous ρ :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hψ.continuous))
  have hSrc : MeasurableSet e.source := (isOpen_extChartAt_source (I := J) p).measurableSet
  have hTar : MeasurableSet e.target := by
    change MeasurableSet (extChartAt J p).target
    rw [extChartAt_target]
    exact (((chartAt (EuclideanHalfSpace n) p).open_target).preimage
      (𝓡∂ n).continuous_symm).measurableSet.inter (𝓡∂ n).isClosed_range.measurableSet
  have he : AEMeasurable e μc := (continuousOn_extChartAt (I := J) p).aemeasurable hSrc
  have hμc : μc.map e = μE.withDensity a := hμ p
  have ha : AEMeasurable a μE :=
    (ENNReal.continuous_ofReal.continuousOn.comp
      (CalderonN.contDiffOn_metric_volume (chartMetric_smooth g p)).continuousOn
      (mapsTo_univ _ _)).aemeasurable hTar
  have hd : AEMeasurable d μE :=
    (hρ.continuousOn.comp (continuousOn_extChartAt_symm (I := J) p)
      (mapsTo_univ _ _)).aemeasurable hTar
  have hd' : AEMeasurable d (μc.map e) :=
    hμc.symm ▸ hd.mono_ac (withDensity_absolutelyContinuous μE a)
  have hread : ρ =ᵐ[μc] d ∘ e := by
    filter_upwards [ae_restrict_mem hSrc] with x hx
    change ρ x = ρ (e.symm (e x))
    rw [e.left_inv hx]
  change ((μ.withDensity ρ).restrict e.source).map e = μE.withDensity b
  rw [restrict_withDensity hSrc, map_withDensity_from_comp he hρ.measurable.aemeasurable hd' hread,
    hμc, ← withDensity_mul₀ ha hd]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hTar] with y hy
  let t := ψ (e.symm y)
  let w := Real.exp (2 * t)
  have hmatrix : chartMetric G p y = w • chartMetric g p y := rfl
  have hwp : 0 ≤ w := (Real.exp_pos _).le
  have hpow : w ^ n = Real.exp (2 * ((n : ℝ) * t)) := by
    dsimp only [w]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrt : Real.sqrt (w ^ n) = Real.exp ((n : ℝ) * t) := by
    rw [hpow, show 2 * ((n : ℝ) * t) = (n : ℝ) * t + (n : ℝ) * t by ring,
      Real.exp_add, ← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb : Real.sqrt (chartMetric G p y).det =
      Real.exp ((n : ℝ) * t) * Real.sqrt (chartMetric g p y).det := by
    rw [hmatrix, Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (pow_nonneg hwp n), hsqrt]
  change ENNReal.ofReal (Real.sqrt (chartMetric g p y).det) *
    ENNReal.ofReal (Real.exp ((n : ℝ) * t)) =
    ENNReal.ofReal (Real.sqrt (chartMetric G p y).det)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hb, mul_comm]

theorem expScaledEnergy_eq_conductivity (g : SmoothMetric n M) (μ : Measure M)
    (ψ : M → ℝ) (hψ : ContMDiff J R ∞ ψ) (f : M → ℝ) :
    dirichletQuadraticEnergy (expScaledMetric g ψ hψ) (expScaledVolume (n := n) μ ψ) f =
      conductivityQuadraticEnergy g μ (fun x => Real.exp (((n : ℝ) - 2) * ψ x)) f := by
  unfold dirichletQuadraticEnergy conductivityQuadraticEnergy
  congr 1
  ext c
  apply exists_congr
  intro u
  have hInt : (∫ x, covectorEnergy (expScaledMetric g ψ hψ) x (mfderiv J R u x)
        ∂(expScaledVolume (n := n) μ ψ)) =
      ∫ x, Real.exp (((n : ℝ) - 2) * ψ x) * covectorEnergy g x (mfderiv J R u x) ∂μ := by
    unfold expScaledVolume
    rw [integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      change Real.exp ((n : ℝ) * ψ x) *
        covectorEnergy (expScaledMetric g ψ hψ) x (mfderiv J R u x) = _
      unfold expScaledMetric
      rw [covectorEnergy_scaleSmoothMetric (n := n) (M := M), ← mul_assoc, ← Real.exp_neg, ← Real.exp_add]
      congr 2
      ring
    · exact ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)).measurable
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [hInt]

end CalderonPaper
