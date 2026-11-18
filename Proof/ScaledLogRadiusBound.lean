import Proof.ProfileRadiusJets
import Proof.UniformFrozenTraceAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres

/-- The potentially large logarithmic-radius derivative is bounded after its
    actual radius factor, uniformly for every admitted profile. -/
theorem Admissible.scaled_coord_logRadius_bound {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i : I) :
    d.radius y*|coordDeriv i (fun x => Real.log (d.radius x)) y| ≤ K := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hb := hd.1.1.coord_logRadius_bound hK d.frame d.radius hCenter hFrame i
  have hRadius := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.1
  have hrβ : d.radius y*beta d.γ d.radius y ≤ 1 :=
    hRadius.trans ((div_le_self hε hf).trans hε1)
  calc
    _ ≤ d.radius y*(K*beta d.γ d.radius y) := mul_le_mul_of_nonneg_left hb hr.le
    _ = K*(d.radius y*beta d.γ d.radius y) := by ring
    _ ≤ K*1 := mul_le_mul_of_nonneg_left hrβ (zero_le_one.trans hK)
    _ = K := mul_one _

end ShrinkingSpheres
