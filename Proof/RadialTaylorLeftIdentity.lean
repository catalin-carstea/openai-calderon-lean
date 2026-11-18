import Proof.LowRadialPerturbation
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres

/-- The genuine radial Taylor remainder solves this exact left identity with
    the actual normal multiplier. Only the actual point inverse is used. -/
theorem radialErrorAssembly_first_remainder_left_identity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N N1 D : E →L[ℝ] F) (M M1 : F →L[ℝ] F)
    (T : Fin 3 → F →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (c r : ℝ) (hc : c ≠ 0) (hM : M.IsInvertible) :
    M.comp (radialErrorAssembly N M D T G-r • (c⁻¹ • (N1-M1.comp D))) =
      (N-c • D-r • N1)-(M-c • ContinuousLinearMap.id ℝ F-r • M1).comp D-
        ∑ j : Fin 3,(T j).comp (G j)-
        r • (M-c • ContinuousLinearMap.id ℝ F).comp (c⁻¹ • (N1-M1.comp D)) := by
  let B := c⁻¹ • (N1-M1.comp D)
  let S := ∑ j : Fin 3,(T j).comp (G j)
  have hcB : c • B = N1-M1.comp D := by
    dsimp only [B]
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  have hRaw : M.comp (radialErrorAssembly N M D T G) = N-M.comp D-S := by
    unfold radialErrorAssembly
    rw [← ContinuousLinearMap.comp_assoc,hM.self_comp_inverse,ContinuousLinearMap.id_comp]
  change M.comp (radialErrorAssembly N M D T G-r • B) = _
  rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,hRaw]
  simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.id_comp]
  rw [hcB]
  module

end ShrinkingSpheres
