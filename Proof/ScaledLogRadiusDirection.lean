import Proof.LogRadiusDirectionalBound
import Proof.ScaledLogRadiusBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres

lemma Admissible.scaled_logRadius_direction_bound {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : X} (hx : x ∈ Y) (a : X) :
    d.radius x*|fderiv ℝ (fun y => Real.log (d.radius y)) x a| ≤ 3*K*‖a‖ := by
  have hr := (hd.2.2.2.2.1.2 x hx).1
  have hc := hd.2.1.center_mem hx
  have hFrame := hd.1.2.2.2.2.2.2.2 x hc
  have hDir := hd.1.1.logRadius_direction_bound hK d.frame d.radius hc hFrame a
  have hRadius := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.1
  have hrβ : d.radius x*beta d.γ d.radius x ≤ 1 :=
    hRadius.trans ((div_le_self hε hf).trans hε1)
  calc
    _ ≤ d.radius x*(3*K*beta d.γ d.radius x*‖a‖) := mul_le_mul_of_nonneg_left hDir hr.le
    _ = (3*K*‖a‖)*(d.radius x*beta d.γ d.radius x) := by ring
    _ ≤ (3*K*‖a‖)*1 := mul_le_mul_of_nonneg_left hrβ (by positivity)
    _ = _ := mul_one _
end ShrinkingSpheres
