module

public import Proof.CalderonN.Density
public import Proof.CalderonN.Moments
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.MetricDivergence
public import Proof.CalderonN.SmoothEnergyLimit
public import Proof.CalderonN.ComplexZonalProjection

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem fiberSq_le_sobolevSq_one (g : (MetricField dim)) (e : (Frame dim)) (y : (X dim)) (u : (X dim) → ℂ)
    (hParseval : sobolevSq g e 0 y u = fiberSq e y u)
    (hSummable : Summable (fun k : ℕ => (1+(k:ℝ))^(2*(1:ℝ)) * fiberSq e y (degreePart g e k y u))) :
    fiberSq e y u ≤ sobolevSq g e 1 y u := by
  rw [← hParseval]
  unfold sobolevSq
  have hle (k : ℕ) : (1+(k:ℝ))^(2*(0:ℝ)) * fiberSq e y (degreePart g e k y u) ≤
      (1+(k:ℝ))^(2*(1:ℝ)) * fiberSq e y (degreePart g e k y u) := by
    apply mul_le_mul_of_nonneg_right _ (fiberSq_nonneg e y _)
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by norm_num)
  exact Summable.tsum_le_tsum hle
    (hSummable.of_nonneg_of_le (fun _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (fiberSq_nonneg e y _)) hle)
    hSummable

/-- The integrand in the protected coercivity energy, including chart volume. -/
abbrev sphereEnergyDensity (d : Data dim) (φ : Field dim) : X dim → ℝ :=
  physicalEnergyDensity d.γ d.frame d.radius φ

/-- Parseval and the positive slope floor let the actual energy dominate
the unweighted angular density at each center. -/
theorem mul_fiberSq_le_energyDensity (d : (Data dim)) (φ : (Field dim)) (y : (X dim)) (m : ℝ)
    (hm : 0 ≤ m) (hvolume : m ≤ chartVolume d.γ y) (hβ : 1 ≤ beta d.γ d.radius y)
    (hParseval : sobolevSq d.γ d.frame 0 y (fun w => φ (y,w)) =
      fiberSq d.frame y (fun w => φ (y,w)))
    (hSummable : Summable (fun k : ℕ => (1+(k:ℝ))^(2*(1:ℝ)) *
      fiberSq d.frame y (degreePart d.γ d.frame k y (fun w => φ (y,w))))) :
    m * fiberSq d.frame y (fun w => φ (y,w)) ≤ sphereEnergyDensity d φ y := by
  let b := beta d.γ d.radius y
  let u := fun w => φ (y,w)
  let H := fun i w => horizontal d.γ φ y w (d.frame y i)
  have hf := fiberSq_nonneg d.frame y u
  have h₁ := fiberSq_le_sobolevSq_one d.γ d.frame y u hParseval hSummable
  have h₁pos := sobolevSq_nonneg d.γ d.frame 1 y u
  have hb : 0 ≤ b := zero_le_one.trans hβ
  have hβ2 : 1 ≤ b^2 := one_le_pow₀ hβ
  have h₂ : fiberSq d.frame y u ≤ b^2 * sobolevSq d.γ d.frame 1 y u :=
    h₁.trans (le_mul_of_one_le_left h₁pos hβ2)
  have hh : 0 ≤ ∑ i, fiberSq d.frame y (H i) := Finset.sum_nonneg fun i _ => fiberSq_nonneg _ _ _
  have hhalf : 0 ≤ b⁻¹ * (∑ i, sobolevSq d.γ d.frame (1/2) y (H i)) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg fun i _ => sobolevSq_nonneg _ _ _ _ _)
  have hthree : 0 ≤ b * sobolevSq d.γ d.frame (3/2) y u :=
    mul_nonneg hb (sobolevSq_nonneg _ _ _ _ _)
  calc
    _ ≤ chartVolume d.γ y * fiberSq d.frame y u := mul_le_mul_of_nonneg_right hvolume hf
    _ ≤ sphereEnergyDensity d φ y := by
      apply mul_le_mul_of_nonneg_left _ (hm.trans hvolume)
      linarith only [h₂,hh,hhalf,hthree]

end CalderonN
