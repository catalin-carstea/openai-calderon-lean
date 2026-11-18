import Proof.FirstErrorScalarCoefficients
import Proof.ScaledLogRadiusDirection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared physical coframe norm, independent of radius/profile derivatives. -/
lemma Admissible.relative_coframe_direction_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    {y : X} (hyΩ : y ∈ Ω) (a : X) (j : I) :
    |normalFrameRelativeCoframeValue d.γ a j ((y,frameVectorLinear d.frame y),0)| ≤
      (9*|M 0| *K)*‖a‖ := by
  have he0 := hd.1.2.2.2.2.2.2.2 y hyΩ
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using he0 i j
  rw [normalFrameRelativeCoframeValue_orthonormal d.γ a j y _ he]
  have hh := ((frameCoordinateLinear d.γ d.frame y j).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (hd.1.1.norm_frameCoordinateLinear_le hK hyΩ d.frame he0 |M 0| (abs_nonneg _)
      (fun i l => (hd.1.reference_entry_bound hyΩ i l).trans (le_abs_self _)) j) (norm_nonneg a))
  simpa only [Real.norm_eq_abs,frameCoordinateLinear_apply,frameVectorLinear_apply,frameVector_axis] using hh
end ShrinkingSpheres
