module

public import Proof.Manuscript.LowerGreen.BallPoissonCenterSource
public import Proof.Manuscript.LowerGreen.BallConormalSourcePairing
public import Proof.CalderonN.NormalFluxDensity

import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n)

set_option maxHeartbeats 1800000 in
/-- The probability-normalized Poisson density at the center, with
arbitrarily many derivatives in the coefficient and angular parameters.
The ambient angular argument is radially projected to the sphere. -/
theorem exists_radialBallPoissonDensity (k : ℕ) :
    ∃ ψ : P × X n → ℝ,
      ContDiffOn ℝ k ψ (F.V ×ˢ ({0}ᶜ : Set (X n))) ∧
      (∀ p z, z ≠ 0 → ψ (p,z) = ψ (p,sphereNormalize z)) ∧
      ∀ p ∈ F.V, ∀ u : SmoothData n,
        EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1) →
          ∫ w : ↥(standardSphere n), ψ (p,w) * u.1 w ∂(sphereProbability n) = u.1 0 := by
  let s := k+n+2
  obtain ⟨f,hf,hRep⟩ := F.exists_ballPoissonCenterSource s
  let U (p : P) : BallSobolev n (s+2) := F.inverseL s p (f p).1
  have hf' : ContDiffOn ℝ ∞ (fun p => (f p).1) F.V :=
    ((closedBallSobolev n s).toSubmodule.subtypeL).contDiff.comp_contDiffOn hf
  have hU : ContDiffOn ℝ ∞ U F.V := (F.contDiffOn_inverseL s).clm_apply hf'
  obtain ⟨b,hb,hbVal⟩ := exists_smooth_closedBall_lift F.openV hU
    (fun p hp => F.inverseL_mem_closed hp (f p))
  let ψ (q : P × X n) := -(unitSphereArea n) * radialClosedBallConormal F.a (s+2) b q
  have hs : 1+k+n+3 ≤ s+2 := by dsimp [s]; omega
  refine ⟨ψ,contDiffOn_const.mul (contDiffOn_radialClosedBallConormal F.smooth hs hb),?_,?_⟩
  · intro p z hz
    have hN := sphereNormalize_eq_of_sphere (sphereNormalize_mem_sphere hz)
    simp only [ψ,radialClosedBallConormal,hN]
  · intro p hp u hu
    have hbEq : b p = F.inverseOnClosedL hp s (f p) := Subtype.ext (hbVal p hp)
    have hPair := F.inverseOnClosedL_boundaryPairing hp s (by omega) (f p) u hu
    have hNorm := integral_unitSphereArea_mul_probability (fun w : ↥(standardSphere n) =>
      closedBallConormal (fun z => F.a (p,z)) (s+2) (b p) w * u.1 w)
    have hE : (fun w : ↥(standardSphere n) => ψ (p,w) * u.1 w) =
        fun w : ↥(standardSphere n) => -((unitSphereArea n) *
          (closedBallConormal (fun z => F.a (p,z)) (s+2) (b p) w * u.1 w)) := by
      funext w
      rw [show ψ (p,w) = -(unitSphereArea n) *
          radialClosedBallConormal F.a (s+2) b (p,w) from rfl,
        radialClosedBallConormal_eq_on_sphere]
      ring
    rw [hE,integral_neg,hNorm,hbEq]
    exact hPair.trans (hRep p hp u hu)

end SupportedBallFamily

end CalderonPaper.LowerGreen

end
