import Proof.ActualFirstErrorScalarCoefficientBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Read the normal coefficient budget from the degree slot of the already
controlled scalar generator coefficients. -/
lemma normal_scalar_coefficient_of_weighted_bound (Q0 : SmoothCoefficientJets 2)
    (r b B : ℝ) (hr : 0 < r) (v : I → ℝ) (Q : I → ClosedCoefficientJets 3)
    (hB : (∑ a,taylorGeneratorWeight r a*‖firstErrorScalarCoefficients Q0 r⁻¹ b v Q a‖) ≤ B) :
    ‖∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j)‖ ≤ r*B := by
  have hw (a : TaylorGeneratorIndex) : 0 ≤ taylorGeneratorWeight r a := by
    cases a <;> simp only [taylorGeneratorWeight] <;> positivity
  have hh := Finset.single_le_sum
    (fun a _ => mul_nonneg (hw a) (norm_nonneg (firstErrorScalarCoefficients Q0 r⁻¹ b v Q a)))
    (Finset.mem_univ TaylorGeneratorIndex.degree)
  have hD : r⁻¹*‖∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j)‖ ≤ B := by
    have hD' := hh.trans hB
    simpa only [taylorGeneratorWeight,one_mul,firstErrorScalarCoefficients,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)] using hD'
  have hMul := mul_le_mul_of_nonneg_left hD hr.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hMul

lemma Admissible.normal_scalar_coefficient_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    ‖∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed ((y,frameVectorLinear d.frame y),0))‖ ≤
      (firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC))*‖a‖*(d.radius y)^2 := by
  have hh := normal_scalar_coefficient_of_weighted_bound Q0 (d.radius y)
    (fderiv ℝ (fun x => Real.log (d.radius x)) y a) _ (hd.2.2.2.2.1.2 y hy).1
    (fun j => normalFrameRelativeCoframeValue d.γ a j ((y,frameVectorLinear d.frame y),0))
    (fun j => (C j).closed ((y,frameVectorLinear d.frame y),0))
    (hd.first_error_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a C)
  exact hh.trans_eq (by ring)
end ShrinkingSpheres
