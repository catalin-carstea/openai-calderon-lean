module

public import Proof.CalderonN.Coercivity

import Proof.CalderonN.Moments
public import Proof.CalderonN.SphereFrame
import Mathlib.MeasureTheory.Function.LocallyIntegrable

public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace CalderonN

variable {n : ℕ}

@[expose] def cutoffDensity (χ : X n → ℝ) (ψ : Field n) (p : X n × X n) : ℂ :=
  (χ p.1 : ℂ) * (ψ p - 1)

theorem continuous_frame_density {Y : Set (X n)} {γ : MetricField n} {e : Frame n} {ψ : Field n}
    (hψ : smoothNear ψ (bundle Y γ)) {y : X n} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    Continuous (fun w : ↥(standardSphere n) => ψ (y, frameVector e y w)) := by
  obtain ⟨V, _, hV, hψ⟩ := hψ
  refine hψ.continuousOn.comp_continuous
    (continuous_const.prodMk ((continuous_frameVector e y).comp continuous_subtype_val)) ?_
  intro w
  exact hV ⟨hy, frameVector_mem_sphere γ e y he w⟩

/-- Constant reproduction gives a compactly supported, fiber-mean-zero test
for the same metric, frame and transfer density entering coercivity. -/
theorem cutoffDensity_test [NeZero n] {Y : Set (X n)} {γ : MetricField n} {e : Frame n} {ψ : Field n} {χ : X n → ℝ}
    (hψ : smoothNear ψ (bundle Y γ))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχY : tsupport χ ⊆ Y)
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hmean : ∀ y ∈ Y, sphereAverage e y (fun w => ψ (y, w)) = 1) :
    Test Y γ e (cutoffDensity χ ψ) := by
  have hsm : smoothNear (cutoffDensity χ ψ) (bundle Y γ) := by
    obtain ⟨V, hVopen, hV, hψ⟩ := hψ
    refine ⟨V, hVopen, hV, ?_⟩
    have hc : ContDiff ℝ ∞ (fun p : X n × X n => (χ p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)
    exact hc.contDiffOn.mul (hψ.sub contDiffOn_const)
  refine ⟨hsm, ⟨tsupport χ, hχc, hχY, ?_⟩, ?_⟩
  · intro y hy w _
    have hz : χ y = 0 := image_eq_zero_of_notMem_tsupport hy.2
    simp [cutoffDensity, hz]
  · intro y hy
    let v : ↥(standardSphere n) → ℂ := fun w => ψ (y, frameVector e y w)
    let : CompactSpace ↥(standardSphere n) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X n) 1)
    have hv : Integrable v (sphereProbability n) :=
      (continuous_frame_density hψ hy (he y hy)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace v)
    have hm : (∫ w, v w ∂sphereProbability n) = 1 := hmean y hy
    change (∫ w, (χ y : ℂ) * (v w - 1) ∂sphereProbability n) = 0
    rw [integral_const_mul, integral_sub hv (integrable_const (1 : ℂ)), hm,
      integral_const, probReal_univ, one_smul, sub_self, mul_zero]

/-- Apply the coercivity estimate to the physical density with the actual
cutoff. The bound on the trace operator is the remaining analytic input. -/
theorem cutoffDensity_energy_bound [NeZero n]
    {Y Ω : Set (X n)} {K ρ c₀ : ℝ} {m : ℕ} {M : Fin (m + 1) → ℝ} {Cj : Fin 9 → ℝ}
    {floor ε₀ C ε B : ℝ} (hC : 0 ≤ C)
    (hEstimate : UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C)
    {d : Data n} (hε : 0 ≤ ε) (hle : ε ≤ ε₀)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {ψ : Field n} {χ : X n → ℝ} (hψ : smoothNear ψ (bundle Y d.γ))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχY : tsupport χ ⊆ Y)
    (hmean : ∀ y ∈ Y, sphereAverage d.frame y (fun w => ψ (y, w)) = 1)
    (hYΩ : Y ⊆ Ω) (houtput : traceNorm Y d (cutoffDensity χ ψ) ≤ B) :
    energyNorm Y d (cutoffDensity χ ψ) ≤ C * B := by
  have hframe := hd.1.2.2.2.2.2.2.2
  have htest := cutoffDensity_test hψ hχ hχc hχY (fun y hy => hframe y (hYΩ hy)) hmean
  exact (hEstimate d ε hε hle hd _ htest).trans (mul_le_mul_of_nonneg_left houtput hC)

end CalderonN
