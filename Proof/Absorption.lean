import Proof.Geometry
import Proof.ArchiveReduction
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory
namespace ShrinkingSpheres

/-- Common Hilbert space of all outputs for one configuration. Coordinates on the sphere
    come from the same orthonormal frame as the energy and the physical norm. -/
def outputMeasure (Y : Set X) (d : Data) : Measure (X × ↥standardSphere) :=
  let σ := (volume : Measure X).toSphere
  let base := ((volume : Measure X).restrict Y).withDensity
    (fun y => ENNReal.ofReal (Real.sqrt (d.γ y).det))
  base.prod ((σ univ)⁻¹ • σ)

abbrev Output (Y : Set X) (d : Data) := Lp ℂ 2 (outputMeasure Y d)

/-- The unproved estimates at the last application. The physical output must have exactly
    the norm of the explicit moving trace of this test. These witnesses belong in a proof. -/
def AnalyticEstimates (Y : Set X) (d : Data) (φ : Field) (floor ε c CE CJ : ℝ) : Prop :=
  let N := energyNorm Y d φ
  ∃ T Tf U Ud J P : Output Y d, ∃ err : ℝ,
    c * N^2 ≤ ‖T‖^2 - ‖Tf‖^2 ∧
    ‖(2:ℝ) • T + U‖^2 - ‖(2:ℝ) • Tf + Ud‖^2 = 4 * (‖T‖^2 - ‖Tf‖^2) + err ∧
    |err| ≤ CE * ε * N^2 ∧ ‖J‖ ≤ CJ / floor * N ∧ P = (2:ℝ) • T + U + J ∧
    ‖P‖ = traceNorm Y d φ

/-- The producer can require a minimum profile slope and a small perturbation. Its constants
    are uniform across every admitted configuration and test. -/
theorem uniformEstimate_of_analyticEstimates (Y Ω : Set X) (K ρ c₀ : ℝ)
    {m : ℕ} (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (B η c CE CJ : ℝ) (hη : 0 < η) (hc : 0 < c) (hCE : 0 ≤ CE) (hCJ : 0 ≤ CJ)
    (produce : ∀ floor, B ≤ floor → ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ, Test Y d.γ d.frame φ →
      AnalyticEstimates Y d φ floor ε c CE CJ) :
    ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  let floor := max B (max 1 (2*CJ/Real.sqrt c))
  let ε₀ := min η (c / (CE+1))
  refine ⟨floor, ε₀, 2/Real.sqrt c, (le_max_left ..).trans (le_max_right ..),
    lt_min hη (div_pos hc (by linarith)), div_pos (by norm_num) (Real.sqrt_pos.mpr hc), ?_⟩
  intro d ε hε hsmall hd φ hφ
  obtain ⟨T,Tf,U,Ud,J,P,err,hR,hcompare,herr,hJ,hP,hnorm⟩ :=
    produce floor (le_max_left ..) ε hε (hsmall.trans (min_le_left ..)) d hd φ hφ
  rw [← hnorm]
  exact OAI.AnisotropicCalderon.Proposition53GeneralReduction.coercivity_of_estimates
    _ _ _ _ _ _ hc hCE hCJ (Real.sqrt_nonneg _) (le_max_right ..) hε
    (hsmall.trans (min_le_right ..)) T Tf U Ud J P err hR hcompare herr hJ hP

end ShrinkingSpheres
