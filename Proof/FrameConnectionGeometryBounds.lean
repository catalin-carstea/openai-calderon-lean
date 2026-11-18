import Proof.FirstMetricNormalDensity
import Proof.FramePullback
import Proof.CoordinateSprayBounds
import Proof.UniformNormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres

/-- Shared frame-value and connection bounds for coarse and balanced tensor
    callers. No derivative norm of the chosen frame appears. -/
theorem Admissible.frame_connection_geometry_bounds {Y Ω : Set X}
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y) :
    (∀ k : I,‖d.frame y k‖ ≤ K) ∧
    ∀ i j a : I,|(connection d.γ y (d.frame y i) (d.frame y j)) a| ≤
      (243*K*|M ⟨1,by omega⟩|)*K^2 := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have heN (k : I) : ‖d.frame y k‖ ≤ K := by
    have h := (frameVectorLinear d.frame y).le_opNorm (axis k)
    rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at h
    exact h.trans (hd.1.1.norm_frameVectorLinear_le hK (hd.2.1.center_mem hy) d.frame hFrame)
  refine ⟨heN,?_⟩
  intro i j a
  let CΓ := 243*K*|M ⟨1,by omega⟩|
  have hΓ : 0 ≤ CΓ := by dsimp only [CΓ];positivity
  have hB : ‖connectionBilinear d.γ y‖ ≤ CΓ :=
    hd.1.connection_budget hKp (by omega) (hd.2.1.center_mem hy)
  calc
    _ ≤ ‖connection d.γ y (d.frame y i) (d.frame y j)‖ := by
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (connection d.γ y (d.frame y i) (d.frame y j)) a
    _ = ‖(connectionBilinear d.γ y) (d.frame y i) (d.frame y j)‖ := by rw [connectionBilinear_apply]
    _ ≤ ‖connectionBilinear d.γ y‖*‖d.frame y i‖*‖d.frame y j‖ := norm_bilinear_apply_le _ _ _
    _ ≤ CΓ*K*K := mul_le_mul (mul_le_mul hB (heN i) (norm_nonneg _) hΓ)
      (heN j) (norm_nonneg _) (mul_nonneg hΓ hK0)
    _ = _ := by dsimp only [CΓ];ring
end ShrinkingSpheres
