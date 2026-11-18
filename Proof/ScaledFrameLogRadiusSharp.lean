import Proof.FrameLogRadiusComponentBound
import Proof.ScaledLogRadiusBound
noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

/-- The actual radius-weighted frame logarithmic coefficient retains the
pointwise inverse-beta weight required by the first-base coefficient. -/
theorem Admissible.scaled_frame_logRadius_beta_small {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hf : 1 ≤ floor)
    {y : X} (hy : y ∈ Y) (i : I) :
    |d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)| ≤ ε/beta d.γ d.radius y := by
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < beta d.γ d.radius y := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hLog := frame_logRadius_component_bound d.γ d.frame d.radius y
    (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) i
  apply (le_div_iff₀ hβ).2
  rw [abs_mul,abs_of_pos hr]
  calc
    _ ≤ (d.radius y*beta d.γ d.radius y)*beta d.γ d.radius y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hr.le) hβ.le
    _ = d.radius y*(beta d.γ d.radius y)^2 := by ring
    _ ≤ ε := (hd.2.2.2.2.2 y hy).2
end ShrinkingSpheres
