import Proof.NormalFrameRelativeActualParameter
import Proof.RelativeInverseRadiusFactorJets
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

lemma relativeInverseRadiusFactor_actual (d : Data) {r0 : ℝ} (hr : r0 ≠ 0) (x : X) :
    r0⁻¹*normalFrameRelativeInverseRadiusFactor (normalFrameRelativeActualParameter d r0 x) =
      (d.radius x)⁻¹ := by
  change r0⁻¹*(1+(d.radius x/r0-1))⁻¹ = _
  rw [show 1+(d.radius x/r0-1) = d.radius x/r0 by ring,div_eq_mul_inv,mul_inv_rev,inv_inv]
  rw [← mul_assoc,inv_mul_cancel₀ hr,one_mul]
end ShrinkingSpheres
