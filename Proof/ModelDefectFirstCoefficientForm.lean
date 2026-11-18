import Proof.CoarseBalancedAdjointPairing
import Proof.ModelAdjointDefectPairing
import Proof.WeightedErrorForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The first coefficient/model-defect form uses angular adjunction only.
Its source term has one horizontal half derivative, and its coefficient
jet term has the permitted beta times H3/2 mass. -/
lemma model_defect_first_coefficient_form_bound (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (B : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (F : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hB : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp B=
      C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp A=
      C.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (CB CJ ε : ℝ) (hCB : 0 ≤ CB) (hCJ : 0 ≤ CJ) (hε : 0 ≤ ε)
    (hβ : 0 < beta d.γ d.radius y)
    (hAN : ‖A‖ ≤ CB*ε/beta d.γ d.radius y)
    (hFN : ‖F‖ ≤ CJ*(beta d.γ d.radius y)^2)
    (u : SphereSobolev (3/2:ℝ)) (v w : SphereSobolev 1)
    (hD : sphereSobolevInclusionL 1 0 (by norm_num) v=
      modelAdjointDefectCoarseL d y w+F (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)) :
    |⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,B v⟫_ℝ| ≤
      CB*((∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖)+CJ)*ε*
        ((beta d.γ d.radius y)⁻¹*‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) w‖^2+
          beta d.γ d.radius y*‖u‖^2) := by
  let β := beta d.γ d.radius y
  let CZ := ∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖
  let H := ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) w‖
  let V := ‖u‖
  let I0 := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hβne : β ≠ 0 := hβ.ne'
  have hCZ : 0 ≤ CZ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hVN : 0 ≤ V := norm_nonneg _
  have hHN : 0 ≤ H := norm_nonneg _
  have hZN : ‖I0 (modelAdjointDefectCoarseL d y w)‖ ≤ CZ*β*H := by
    have hh := DFunLike.congr_fun (modelAdjointDefectCoarseL_half_graph d y) w
    simp only [ContinuousLinearMap.comp_apply] at hh
    rw [show I0 (modelAdjointDefectCoarseL d y w)=
      modelAdjointDefectSobolevL (1/2:ℝ) d y
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) w) from hh]
    exact ((modelAdjointDefectSobolevL (1/2:ℝ) d y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_modelAdjointDefectSobolevL_le (1/2:ℝ) d y hFrame) hHN)
  have hFVN : ‖I0 (F (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))‖ ≤ CJ*β^2*V := by
    calc
      _ ≤ ‖F (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)‖ :=
        norm_sphereSobolevInclusionL_apply_le 0 (-(1/2:ℝ)) (by norm_num) _
      _ ≤ ‖F‖*‖sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u‖ := F.le_opNorm _
      _ ≤ (CJ*β^2)*V := mul_le_mul hFN
        (norm_sphereSobolevInclusionL_apply_le (3/2:ℝ) 1 (by norm_num) u)
        (norm_nonneg _) (mul_nonneg hCJ (sq_nonneg β))
  have hDN : ‖I0 (sphereSobolevInclusionL 1 0 (by norm_num) v)‖ ≤ CZ*β*H+CJ*β^2*V := by
    rw [hD,map_add]
    exact (norm_add_le _ _).trans (add_le_add hZN hFVN)
  have hAu : ‖A u‖ ≤ (CB*ε/β)*V :=
    (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hAN hVN)
  have hCross : V*H ≤ β⁻¹*H^2+β*V^2 := by
    simpa only [mul_comm V H] using weighted_product_le H V β hβ
  have hMass : β*V^2 ≤ β⁻¹*H^2+β*V^2 :=
    le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hβ.le) (sq_nonneg H))
  rw [coarse_balanced_adjoint_pairing B C A hB hA u v]
  calc
    _ ≤ ‖A u‖*‖I0 (sphereSobolevInclusionL 1 0 (by norm_num) v)‖ :=
      abs_sphereSobolevDualPairing_le (1/2:ℝ) (A u) _
    _ ≤ ((CB*ε/β)*V)*(CZ*β*H+CJ*β^2*V) := mul_le_mul hAu hDN
      (norm_nonneg _) (mul_nonneg (div_nonneg (mul_nonneg hCB hε) hβ.le) hVN)
    _ = CB*ε*(CZ*(V*H)+CJ*(β*V^2)) := by field_simp [hβne] <;> ring
    _ ≤ CB*ε*(CZ*(β⁻¹*H^2+β*V^2)+CJ*(β⁻¹*H^2+β*V^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hCross hCZ)
        (mul_le_mul_of_nonneg_left hMass hCJ)) (mul_nonneg hCB hε)
    _ = _ := by ring

end ShrinkingSpheres
