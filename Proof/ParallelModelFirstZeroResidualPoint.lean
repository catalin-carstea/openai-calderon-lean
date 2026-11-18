import Proof.ParallelModelFirstZeroComparison
import Proof.ParallelModelFirstLeadingPoint

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

/-- Original-energy bound for the COMPLETE paired zero-model residual:
normalized cubic commutators and both bounded geometric/scalar orientations.
Only the actual half horizontal derivative and H3/2 mass are used. -/
theorem model_first_zero_residual_point_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CW R0 BF BA Q0 : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hCW : 0 ≤ CW) (hR0 : 0 ≤ R0)
    (hBF : 0 ≤ BF) (hBA : 0 ≤ BA) (hQ0 : 0 ≤ Q0)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : DifferentiableAt ℝ U y)
    (hP : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hR : ∀ c,‖framedRaisingHalfL d y (axis c)‖ ≤ R0)
    (hF : ∀ b,‖effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y‖ ≤ BF*ε/(beta d.γ d.radius y)^2)
    (hA : ∀ b,‖modelFirstBoundedAdjointThreeHalfL d b y‖ ≤ BA*ε/(beta d.γ d.radius y)^2)
    (hMass : ∀ b,(∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a|) ≤ CW*ε/beta d.γ d.radius y)
    (hQ : ∀ k c,|modelFirstZeroWeight d k c y| ≤ Q0*beta d.γ d.radius y*metricDensity d.γ y) :
    |modelFirstZeroResidualDensity P WF U y| ≤
      (54*Q0*(6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1)*CW+2*R0*(BF+BA)))*ε*metricDensity d.γ y*
        ∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i) := by
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let H := fun b : I => fiveHalfCovariantDerivative d U (axis b) y
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  let C := 6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1)*CW
  let B := 2*R0*(BF+BA)
  have hG : 0 ≤ max (physicalPotentialGeneratorBudget CF) CG := hCG.trans (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβp := zero_lt_one.trans_le hβ
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hEnergy := model_first_component_energy_controls d U3 y β hβ
  have hGrad (b : I) : β⁻¹*‖J (H b)‖^2 ≤ En := by
    rw [show J (H b)=halfSectionCovariantDerivativeL d U3 y (axis b) from fiveHalfCovariantDerivative_half_inclusion d U y (axis b) hU]
    exact hEnergy.2 b
  have hProd (b : I) := model_first_mass_products_le ‖U3 y‖ ‖J (H b)‖ β En (norm_nonneg _) (norm_nonneg _) hβ hEnergy.1 (hGrad b)
  have hAngular (b c : I) : |sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (modelFirstZeroWordResidualValue P W b c (U3 y))| ≤
      C*ε/β*‖U3 y‖*‖J (H b)‖ := by
    calc
      _ ≤ ‖J (H b)‖*‖modelFirstZeroWordResidualValue P W b c (U3 y)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖J (H b)‖*(C*ε/β*‖U3 y‖) := mul_le_mul_of_nonneg_left
        (model_first_zero_word_residual_norm_bound hd hK P hy W hCG hCK hCW b c (U3 y) (hMass b)) (norm_nonneg _)
      _ = _ := by ring
  have hBounded (b c : I) : |modelFirstZeroBoundedResidual d b c y (U y) (H b)| ≤ B*ε/β^2*‖U3 y‖*‖J (H b)‖ :=
    model_first_zero_bounded_residual_bound d b c y (U y) (H b) R0 BF BA ε β hR0 hBF hBA hε hβp (hR c) (hF b) (hA b)
  have hEach (k c b : I) : |modelFirstZeroWeight d k c y*(
      sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (modelFirstZeroWordResidualValue P W b c (U3 y))+
      modelFirstZeroBoundedResidual d b c y (U y) (H b))| ≤ 2*Q0*(C+B)*ε*μ*En := by
    have hTerm1 : |modelFirstZeroWeight d k c y| *|sphereSobolevDualPairing (1/2:ℝ) (J (H b))
        (modelFirstZeroWordResidualValue P W b c (U3 y))| ≤ 2*Q0*C*ε*μ*En := by
      calc
        _ ≤ (Q0*β*μ)*(C*ε/β*‖U3 y‖*‖J (H b)‖) := mul_le_mul (hQ k c) (hAngular b c) (abs_nonneg _) (by positivity)
        _ = (Q0*C*ε*μ)*(‖J (H b)‖*‖U3 y‖) := by field_simp [hβp.ne'] <;> ring
        _ ≤ (Q0*C*ε*μ)*(2*En) := mul_le_mul_of_nonneg_left (hProd b).2.1 (by positivity)
        _ = _ := by ring
    have hTerm2 : |modelFirstZeroWeight d k c y| *|modelFirstZeroBoundedResidual d b c y (U y) (H b)| ≤ 2*Q0*B*ε*μ*En := by
      calc
        _ ≤ (Q0*β*μ)*(B*ε/β^2*‖U3 y‖*‖J (H b)‖) := mul_le_mul (hQ k c) (hBounded b c) (abs_nonneg _) (by positivity)
        _ = (Q0*B*ε*μ)*(β⁻¹*(‖J (H b)‖*‖U3 y‖)) := by field_simp [hβp.ne'] <;> ring
        _ ≤ (Q0*B*ε*μ)*(2*En) := mul_le_mul_of_nonneg_left (hProd b).2.2 (by positivity)
        _ = _ := by ring
    rw [abs_mul]
    calc
      _ ≤ |modelFirstZeroWeight d k c y| *(|sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (modelFirstZeroWordResidualValue P W b c (U3 y))|+|modelFirstZeroBoundedResidual d b c y (U y) (H b)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ = _ := mul_add _ _ _
      _ ≤ _ := add_le_add hTerm1 hTerm2
      _ = _ := by ring
  rw [modelFirstZeroResidualDensity_eq hY hd P WF hy W U hP]
  have hSum := abs_fin_three_sum_le _ _ (fun k => abs_fin_three_sum_le _ _ (fun c => abs_fin_three_sum_le _ _ (hEach k c)))
  exact hSum.trans_eq (by dsimp only [C,B,En,U3,β,μ];ring)

end ShrinkingSpheres.ParallelEnergy
