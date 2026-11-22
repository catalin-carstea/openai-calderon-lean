module

public import Proof.CalderonN.TransferMomentEnergy
public import Proof.CalderonN.WeightedMomentEnergy
public import Proof.CalderonN.TransferReproduction

import Proof.CalderonN.MetricPair
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem normal_frame_endpoint_range
    {Y Ω : Set (X dim)} {d : (Data dim)} {ρ : ℝ}
    (hN : NormalCoordinates Y Ω d.γ d.expMap (fun y => max ρ (d.radius y)))
    {y : (X dim)} (hy : y ∈ Y) (hr : 0 < d.radius y)
    (he : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0) :
    Continuous (fun w : ↥(standardSphere dim) => endpoint d.expMap d.radius (y,frameVector d.frame y w)) ∧
      ∀ w : ↥(standardSphere dim), endpoint d.expMap d.radius (y,frameVector d.frame y w) ∈ Ω := by
  let V (w : ↥(standardSphere dim)) := (y,d.radius y • frameVector d.frame y w)
  have hV : Continuous V := continuous_const.prodMk
    (((continuous_frameVector d.frame y).comp continuous_subtype_val).const_smul (d.radius y))
  have hDisk (w : ↥(standardSphere dim)) : (V w).2 ∈ disk d.γ y (max ρ (d.radius y)) := by
    have hs : metricPair d.γ y (frameVector d.frame y w) (frameVector d.frame y w) = 1 :=
      frameVector_mem_sphere d.γ d.frame y he w
    change metricPair d.γ y (d.radius y • frameVector d.frame y w) (d.radius y • frameVector d.frame y w)
      ≤ (max ρ (d.radius y))^2
    rw [metricPair_smul_same, hs, mul_one]
    exact pow_le_pow_left₀ hr.le (le_max_right _ _) 2
  obtain ⟨U,_,hSub,hE⟩ := hN.1
  exact ⟨hE.continuousOn.comp_continuous hV (fun w => hSub ⟨hy,hDisk w⟩),
    fun w => ((hN.2 y hy).2.2 _ (hDisk w)).1⟩

/-- The protected moving-trace estimate controls the actual weighted
harmonic increment on the same center domain and at the same radius. -/
theorem weighted_pair_moment_of_coercivity
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hYΩ : Y ⊆ Ω)
    {K ρ c₀ : ℝ} {m₀ : ℕ} {M : Fin (m₀+1) → ℝ} {Cj : Fin 9 → ℝ}
    {floor ε₀ C ε : ℝ} (hC : 0 ≤ C) (hfloor : 1 ≤ floor)
    (hEstimate : UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C)
    {d : (Data dim)} (hε : 0 ≤ ε) (hle : ε ≤ ε₀)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {ψ : (Field dim)} {χ u₁ u₂ : (X dim) → ℝ}
    (hψ : smoothNear ψ (bundle Y d.γ))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχY : tsupport χ ⊆ Y)
    (hu₁ : ContinuousOn u₁ Ω) (hu₂ : ContinuousOn u₂ Y)
    (hmean : ∀ y ∈ Y, sphereAverage d.frame y (fun w => ψ (y,w)) = 1)
    (hcoords : ∀ i : (I dim), EqOn (transferValue d ψ (fun x => x i)) (fun x => x i) Y)
    (htransfer : EqOn (transferValue d ψ u₁) u₂ Y)
    (Ctay volFloor B H : ℝ) (hCtay : 0 ≤ Ctay) (hvolFloor : 0 < volFloor) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hvolume : ∀ y ∈ Y, volFloor ≤ chartVolume d.γ y)
    (hTaylor : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      let z := endpoint d.expMap d.radius (y,frameVector d.frame y w)
      |u₁ z - (u₁ y + fderiv ℝ u₁ y (z-y))| ≤ Ctay * (d.radius y)^2)
    (hParseval : ∀ y ∈ Y, sobolevSq d.γ d.frame 0 y (fun w => cutoffDensity χ ψ (y,w)) =
      fiberSq d.frame y (fun w => cutoffDensity χ ψ (y,w)))
    (hSummable : ∀ y ∈ Y, Summable (fun k : ℕ => (1+(k:ℝ))^(2*(1:ℝ)) *
      fiberSq d.frame y (degreePart d.γ d.frame k y (fun w => cutoffDensity χ ψ (y,w)))))
    (hEint : IntegrableOn (sphereEnergyDensity d (cutoffDensity χ ψ)) Y)
    (hχbound : (∫ y in Y, χ y^2) ≤ H)
    (houtput : traceNorm Y d (cutoffDensity χ ψ) ≤ B) :
    eLpNorm (fun y => χ y * (u₂ y-u₁ y) / (d.radius y)^2) 2 ((volume : Measure (X dim)).restrict Y) ≤
      ENNReal.ofReal (Real.sqrt (2 * Ctay^2 * ((C*B)^2 / volFloor + H))) := by
  have hframe := hd.1.2.2.2.2.2.2.2
  have hp := hd.2.2.2.2.1
  have hrad (y : (X dim)) (hy : y ∈ Y) : 0 < d.radius y := (hp.2 y hy).1
  have hq : ContinuousOn (fun y => χ y * (u₂ y-u₁ y) / (d.radius y)^2) Y :=
    (hχ.continuous.continuousOn.mul (hu₂.sub (hu₁.mono hYΩ))).div
      (hp.1.continuousOn.pow 2) (fun y hy => pow_ne_zero _ (hrad y hy).ne')
  have hχsq : HasCompactSupport (fun y => χ y^2) :=
    hχc.mono (fun y hy hz => hy (by simp [hz]))
  have hχint : IntegrableOn (fun y => χ y^2) Y :=
    ((hχ.continuous.pow 2).integrable_of_hasCompactSupport hχsq).integrableOn
  have henergy := cutoffDensity_energy_bound hC hEstimate hε hle hd hψ hχ hχc hχY hmean hYΩ houtput
  apply weighted_moment_of_energy hY.measurableSet d ψ χ _ Ctay volFloor (C*B) H hvolFloor
    (mul_nonneg hC hB) hH (hq.aestronglyMeasurable hY.measurableSet) hEint hχint hχbound henergy
  intro y hy
  have he := hframe y (hYΩ hy)
  have hdom := mul_fiberSq_le_energyDensity d (cutoffDensity χ ψ) y volFloor hvolFloor.le
    (hvolume y hy) (hfloor.trans (hp.2 y hy).2.1) (hParseval y hy) (hSummable y hy)
  refine ⟨hdom,?_⟩
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  let Z (w : ↥(standardSphere dim)) := endpoint d.expMap d.radius (y,frameVector d.frame y w)
  let P (w : ↥(standardSphere dim)) := ψ (y,frameVector d.frame y w)
  have hP : Continuous P := continuous_frame_density hψ hy he
  have ⟨hZ,hZΩ⟩ := normal_frame_endpoint_range hd.2.1 hy (hrad y hy) he
  have hU : Continuous (fun w => u₁ (Z w)) := hu₁.comp_continuous hZ hZΩ
  have hPLp : MemLp P 2 (sphereProbability dim) := hP.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hZLp : MemLp Z 2 (sphereProbability dim) := hZ.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hULp : MemLp (fun w => u₁ (Z w)) 2 (sphereProbability dim) := hU.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hPI : Integrable P (sphereProbability dim) :=
    hP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst : (∫ w : ↥(standardSphere dim), (P w).re ∂(sphereProbability dim)) = 1 := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (hmean y hy)
    change RCLike.re (∫ w, P w ∂(sphereProbability dim)) = RCLike.re (1 : ℂ) at h
    rw [← integral_re hPI] at h
    exact h
  exact weighted_pair_sq_le_fiberEnergy d ψ χ u₁ u₂ y Ctay volFloor hCtay hvolFloor (hrad y hy)
    hPLp hZLp hULp hconst (fun i => hcoords i hy) (htransfer hy)
    (Eventually.of_forall (hTaylor y hy)) hdom

end CalderonN
