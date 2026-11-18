import Proof.ParallelFirstPotentialRow
import Proof.ParallelNormAssemblyReservedAdjointWeakGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma bounded_quadratic_pair_point_bound
    (R : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : SphereSobolev (-(1/2:ℝ))) (z : SphereSobolev (1/2:ℝ)) (u : SphereSobolev (3/2:ℝ))
    {CR CQ ε β : ℝ} (hCR : 0 ≤ CR) (hCQ : 0 ≤ CQ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hR : ‖R‖ ≤ CR*ε) (hQ : ‖Q‖ ≤ CQ*ε*‖u‖) :
    |sphereSobolevDualPairing (1/2:ℝ) (R z) Q| ≤
      CR*CQ*ε^2*(β⁻¹*‖z‖^2+β*‖u‖^2) := by
  calc
    _ ≤ ‖R z‖*‖Q‖ := abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ (CR*ε*‖z‖)*(CQ*ε*‖u‖) := mul_le_mul
      ((R.le_opNorm z).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg z))) hQ (norm_nonneg _) (by positivity)
    _ = (CR*CQ*ε^2)*(‖z‖*‖u‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_product_le ‖z‖ ‖u‖ β hβ) (by positivity)

/-- Both bounded correction/scalar-drift orientations use genuine
order-zero half outputs and the weak complete potential outputs. -/
theorem firstPotential_bounded_row_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK RF RA : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (hCG : 0 ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (b : I)
    (hRF : 0 ≤ RF) (hRA : 0 ≤ RA)
    (hF : ‖effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y‖ ≤ RF*ε)
    (hA : ‖effectiveFirstBoundedAdjointHalfL d b y‖ ≤ RA*ε)
    (u : SphereSobolev (5/2:ℝ)) (v : SphereSobolev (3/2:ℝ)) :
    let β := beta d.γ d.radius y
    let u3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
    let CQF := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
    let CQA := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
    |⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (firstPotentialBoundedForwardHigherL d b y v),P.potentialQuadraticCoreL W u⟫_ℝ+
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (effectiveFirstBoundedAdjointHigherL d b y v),P.potentialQuadraticAdjointCoreL W u⟫_ℝ| ≤
      (RF*CQF+RA*CQA)*ε^2*
        (β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖^2+β*‖u3‖^2) := by
  let β := beta d.γ d.radius y
  let u3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  let z := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v
  let CQF := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
  let CQA := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hCQF : 0 ≤ CQF := by dsimp only [CQF,potentialWordEntryBudget];positivity
  have hCQA : 0 ≤ CQA := by dsimp only [CQA,potentialWordEntryBudget];positivity
  have hQN : ‖P.potentialQuadraticHalfL y u3‖ ≤ CQF*ε*‖u3‖ :=
    ((P.potentialQuadraticHalfL y).le_opNorm u3).trans (mul_le_mul_of_nonneg_right
      (P.norm_potentialQuadraticHalfL_weighted_small hd hK hf hε hε1 hy) (norm_nonneg _))
  have hAN := actual_potential_adjoint_weak_norm_bound P hd hK hf hε hε1 hy hCG W u3
  have hFB := bounded_quadratic_pair_point_bound (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y)
    (P.potentialQuadraticHalfL y u3) z u3 hRF hCQF hε hβ hF hQN
  have hAB := bounded_quadratic_pair_point_bound (effectiveFirstBoundedAdjointHalfL d b y)
    (quadraticWordAdjointWeakValue P W (PhysicalPrincipalData.potentialWordCoefficient d y) u3)
    z u3 hRA hCQA hε hβ hA hAN
  rw [firstPotential_half_core_pair,firstPotential_half_core_pair,
    P.potentialQuadraticCoreL_balanced hy W u,actual_potential_adjoint_core_weak_graph P W u]
  exact ((abs_add_le _ _).trans (add_le_add hFB hAB)).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
