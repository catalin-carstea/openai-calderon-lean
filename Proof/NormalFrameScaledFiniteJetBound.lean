import Proof.NormalFrameHorizontalRescaling
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Scaled finite jets bound true horizontal derivatives at any finite order.
The horizontal field contains the metric connection, with no frame derivatives. -/
lemma ordered_normalFrame_horizontal_bound_of_scaled_finite_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (d : Data) (y : X) (a : ℕ → X) (D B : ℝ) (hD : 1 ≤ D)
    (hβ : 1 ≤ beta d.γ d.radius y) (F : NormalFrameRelativeParameter → E)
    (hFs : SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
      ((0,frameVectorLinear d.frame y),0) N B)
    (hV : ∀ j,ContDiffAt ℝ ∞
      (normalFrameRelativeScaledHorizontalField d.γ d.radius (beta d.γ d.radius y) y (a j))
      ((0,frameVectorLinear d.frame y),0))
    (hVJets : ∀ j : ℕ,j < N → ∀ k : ℕ,k+1 ≤ N →
      ‖iteratedFDeriv ℝ k (normalFrameRelativeScaledHorizontalField d.γ d.radius (beta d.γ d.radius y) y (a j))
        ((0,frameVectorLinear d.frame y),0)‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) :
    ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
      ((y,frameVectorLinear d.frame y),0)‖ ≤ ((2:ℝ)^N*D)^N*B*(beta d.γ d.radius y)^n := by
  let β := beta d.γ d.radius y
  let p0 : NormalFrameRelativeParameter := ((0,frameVectorLinear d.frame y),0)
  let p1 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Φ := normalFrameRelativeScaledParameter β y
  let V := fun j => normalFrameRelativeScaledHorizontalField d.γ d.radius β y (a j)
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hD0 := zero_le_one.trans hD
  have hB := hFs.nonneg
  have hPow : (1:ℝ) ≤ 2^N := one_le_pow₀ (by norm_num)
  have hBase : 1 ≤ (2:ℝ)^N*D := hD.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hPow hD0)
  have hPoint : Φ p0 = p1 := normalFrameRelativeScaledParameter_point β y _
  have hOrd := norm_iteratedFDeriv_orderedDirectionalFamily_le V (F ∘ Φ) p0 hFs.smooth hV N B D
    hB hD0 hFs.bound hVJets n 0 (by omega)
  simp only [norm_iteratedFDeriv_zero] at hOrd
  have hOrd' : ‖orderedDirectionalFamily V (F ∘ Φ) n p0‖ ≤ ((2:ℝ)^N*D)^N*B := hOrd.trans (by
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBase hn) hB)
  have hExact := congrFun (ordered_normalFrame_horizontal_rescaling d.γ d.radius β hβpos.ne' y a F n) p0
  change orderedDirectionalFamily V (F ∘ Φ) n p0 = (β⁻¹)^n • orderedDirectionalFamily
    (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n (Φ p0) at hExact
  rw [hPoint] at hExact
  have hNorm := congrArg norm hExact
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (β⁻¹)^n)] at hNorm
  have hScaled : (β⁻¹)^n*‖orderedDirectionalFamily
      (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n p1‖ ≤ ((2:ℝ)^N*D)^N*B := by
    rw [← hNorm]
    exact hOrd'
  calc
    _ = β^n*((β⁻¹)^n*‖orderedDirectionalFamily
        (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n p1‖) := by
      rw [inv_pow]
      field_simp
      rfl
    _ ≤ β^n*(((2:ℝ)^N*D)^N*B) := mul_le_mul_of_nonneg_left hScaled (by positivity)
    _ = _ := by ring
end ShrinkingSpheres
