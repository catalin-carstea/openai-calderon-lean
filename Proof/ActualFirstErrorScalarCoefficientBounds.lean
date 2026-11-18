import Proof.FirstErrorScalarCoefficientBounds
import Proof.ActualCoframeDirectionBound
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

lemma Admissible.first_error_scalar_coefficient_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    (∑ k,taylorGeneratorWeight (d.radius y) k*‖firstErrorScalarCoefficients Q0 (d.radius y)⁻¹
      (fderiv ℝ (fun x => Real.log (d.radius x)) y a)
      (fun j => normalFrameRelativeCoframeValue d.γ a j ((y,frameVectorLinear d.frame y),0))
      (fun j => (C j).closed ((y,frameVectorLinear d.frame y),0)) k‖) ≤
      (firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC))*‖a‖*(d.radius y) := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hyΩ := hd.2.1.center_mem hy
  have hV (j : I) : |normalFrameRelativeCoframeValue d.γ a j ((y,frameVectorLinear d.frame y),0)| ≤
      (9* |M 0| *K)*‖a‖ := hd.relative_coframe_direction_bound hK hyΩ a j
  have hLog := hd.scaled_logRadius_direction_bound hK hf hε hε1 hy a
  have hb : |fderiv ℝ (fun x => Real.log (d.radius x)) y a| ≤ (3*K)*‖a‖*(d.radius y)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hr).2 (by simpa only [mul_comm (d.radius y)] using hLog)
  have hQ (j : I) : ‖(C j).closed ((y,frameVectorLinear d.frame y),0)‖ ≤ CC*‖a‖*(d.radius y)^2 := by
    have hh := (C j).joint 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hh := firstErrorScalarCoefficients_weighted_bound Q0 (d.radius y) ‖a‖ (9* |M 0| *K) (3*K) CC hr hr1
    (norm_nonneg _) (by positivity) (by positivity) hCC _ _ _ hb hV hQ
  exact hh.trans_eq (by ring)
end ShrinkingSpheres
