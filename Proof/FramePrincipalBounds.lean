import Proof.FrameTensorMatrix
import Proof.PrincipalCoefficientWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The actual principal coefficient in the moving frame differs from the
    identity by O(epsilon*r), and stays bounded using frame values alone. -/
theorem Admissible.framePrincipalCoefficient_bounds {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i j : I) :
    |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)| ≤
        9*K^2*ε*d.radius y ∧
    |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j| ≤ 9*(K+1)*K^2 ∧
    |(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0))/d.radius y| ≤ 9*K^2*ε := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans hε1
  have hεr : ε*d.radius y ≤ 1 := (mul_le_mul_of_nonneg_right hε1 hr.le).trans (by simpa using hr1)
  have hDiff := frameTensorMatrix_abs_le d.γ d.frame hd.1.1 hK (hd.2.1.center_mem hy) hFrame
    (principal d.γ d.g₂ y-(d.γ y)⁻¹) (mul_nonneg hε hr.le) (fun a b => hd.2.2.2.2.2.component_bound hy a b) i j
  rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y hFrame] at hDiff
  have hDiff' : |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)| ≤
      9*K^2*ε*d.radius y := hDiff.trans_eq (by ring)
  have hEll : Elliptic Y K d.γ := ⟨fun a b => (hd.1.1.1 a b).mono (fun x hx => hd.2.1.center_mem hx),
    fun x hx => hd.1.1.2 x (hd.2.1.center_mem hx)⟩
  have hQ (a b : I) : |principal d.γ d.g₂ y a b| ≤ K+1 :=
    (principal_entry_le_inverse_add hEll (zero_lt_one.trans_le hK) hd.2.2.2.2.2
      hy a b).trans (by linarith)
  have hBound := frameTensorMatrix_abs_le d.γ d.frame hd.1.1 hK (hd.2.1.center_mem hy) hFrame
    (principal d.γ d.g₂ y) (show 0 ≤ K+1 by linarith) hQ i j
  refine ⟨hDiff',hBound,?_⟩
  rw [abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).2 hDiff'
end ShrinkingSpheres
