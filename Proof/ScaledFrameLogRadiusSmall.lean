import Proof.FrameLogRadiusComponentBound
import Proof.ScaledLogRadiusBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace ShrinkingSpheres

/-- The actual frame logarithmic coefficient retains the small radius weight. -/
theorem Admissible.scaled_frame_logRadius_small {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hf : 1 ≤ floor)
    {y : X} (hy : y ∈ Y) (i : I) :
    |d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)| ≤ ε/floor := by
  let b := beta d.γ d.radius y
  let ell := fderiv ℝ (fun x => Real.log (d.radius x)) y
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEll : |ell (d.frame y i)| ≤ b :=
    frame_logRadius_component_bound d.γ d.frame d.radius y hFrame i
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRadius := (radius_bounds (d.radius y) b floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.1
  calc
    _ = d.radius y*|ell (d.frame y i)| := by rw [abs_mul,abs_of_pos hr]
    _ ≤ d.radius y*b := mul_le_mul_of_nonneg_left hEll hr.le
    _ ≤ ε/floor := hRadius
end ShrinkingSpheres
