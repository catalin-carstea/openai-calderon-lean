import Proof.PhysicalPotentialQuadraticSplit
import Proof.ModelPotentialRadiusBudget
import Proof.FiniteMatrixNormBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The single-degree model complement is genuinely angular order one. -/
def principalModelPotentialLinearCoarseL (d : Data) (y : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    ((d.radius y*hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)) •
      sphereSobolevDegreeL)

lemma principalModelPotentialLinearCoarseL_balanced (d : Data) (y : X) :
    balancedCoarsePotentialL (principalModelPotentialLinearCoarseL d y)=principalModelPotentialLinearHalfL d y := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [balancedCoarsePotentialL,principalModelPotentialLinearCoarseL,principalModelPotentialLinearHalfL,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    sphereSobolevDegreeL_half,sphereSobolevInclusionL_trans_apply]

lemma Admissible.norm_principalModelPotentialLinearCoarseL_small {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖principalModelPotentialLinearCoarseL d y‖ ≤ 81*(K+1)*K^2*(2*|Cj 2|+4)*ε := by
  let B := 9*(K+1)*K^2
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hD : ‖sphereSobolevDegreeL‖ ≤ 2 := by
    simpa only [sphereSobolevShiftedDegreeL_one_eq_degree] using norm_sphereSobolevShiftedDegreeL_le_two 1
  have hF (i j : I) : ‖(d.radius y*hessianBilinear d.γ (fun x => Real.log (d.radius x)) y
      (d.frame y i) (d.frame y j)) • sphereSobolevDegreeL‖ ≤ (2*|Cj 2|+4)*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hd.radius_frame_logRadius_hessian_small hY hy i j) hD (norm_nonneg _) (by positivity)).trans_eq (by ring)
  exact (norm_weighted_matrix_three_le (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)) _ B _ hB
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1) hF).trans_eq
      (by dsimp only [B];ring)
end ShrinkingSpheres
