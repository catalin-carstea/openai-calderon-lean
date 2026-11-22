module

public import Mathlib.Analysis.Normed.Operator.Bilinear

import Mathlib.Tactic

/-! The bilinear boundary energy expansion of `BilinearPoissonTaylor`
and the flat harmonic cancellation of `FirstConormalCoefficientDerivative`
in the released Proposition 5.3 proof. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 18

namespace CalderonN

/-- With a flat harmonic test in the second slot, the low conormal
remainder uses only a first-order bound for the Poisson lift difference.
The first correction is the coefficient energy on the two flat lifts. -/
theorem norm_weakConormal_energy_remainder_le
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E E0 E1 : H →L[ℝ] H →L[ℝ] ℝ) (P P0 : F →L[ℝ] H)
    (hFlat : E0.bilinearComp (P-P0) P0 = 0)
    (r B C D : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : ‖E-E0‖ ≤ B*r) (hP : ‖P-P0‖ ≤ C*‖P0‖*r)
    (hR : ‖E-E0-r • E1‖ ≤ D*r^2) :
    ‖E.bilinearComp P P0-E0.bilinearComp P0 P0-r • E1.bilinearComp P0 P0‖ ≤
      (B*C+D)*‖P0‖^2*r^2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro f g
  simp only [sub_apply,smul_apply,ContinuousLinearMap.bilinearComp_apply,smul_eq_mul]
  have hZ : E0 (P f-P0 f) (P0 g) = 0 := by
    have h := congrArg (fun Q : F →L[ℝ] F →L[ℝ] ℝ => Q f g) hFlat
    simpa only [ContinuousLinearMap.bilinearComp_apply,sub_apply,zero_apply] using h
  have hEq :
      E (P f) (P0 g)-E0 (P0 f) (P0 g)-r*E1 (P0 f) (P0 g) =
        (E-E0) ((P-P0) f) (P0 g)+(E-E0-r • E1) (P0 f) (P0 g) := by
    simp only [sub_apply,smul_apply,map_sub,smul_eq_mul]
    simp only [map_sub,sub_apply] at hZ
    linarith only [hZ]
  rw [hEq]
  have hf : ‖(P-P0) f‖ ≤ (C*‖P0‖*r)*‖f‖ :=
    ((P-P0).le_opNorm f).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg f))
  have h1 : ‖(E-E0) ((P-P0) f) (P0 g)‖ ≤ (B*r)*((C*‖P0‖*r)*‖f‖)*(‖P0‖*‖g‖) :=
    ((E-E0).le_opNorm₂ _ _).trans (by gcongr; exact P0.le_opNorm g)
  have h2 : ‖(E-E0-r • E1) (P0 f) (P0 g)‖ ≤ (D*r^2)*(‖P0‖*‖f‖)*(‖P0‖*‖g‖) :=
    ((E-E0-r • E1).le_opNorm₂ _ _).trans (by
      gcongr
      exact P0.le_opNorm f
      exact P0.le_opNorm g)
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

end CalderonN
