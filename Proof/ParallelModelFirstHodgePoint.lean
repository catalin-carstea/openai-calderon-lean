import Proof.ParallelModelFirstExchangeAlgebra
import Proof.ParallelFirstSelfHodgeIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Mixed Hodge remainder: the first source has background size and the
second source and its weak jet have epsilon size. The canonical horizontal
and H3/2 mass weights are retained. -/
lemma model_first_hodge_remainder_point_bound
    (d : Data) (q : X → ℝ) (LR LS : X → SphereSobolev (1/2:ℝ)) (y : X) (a b : I)
    (R0 B0 B1 Q0 Q1 KC ε β μ u En : ℝ)
    (hR0 : 0 ≤ R0) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hKC : 0 ≤ KC)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (hq : |q y| ≤ Q0*μ) (hDq : ∀ i,|fderiv ℝ q y (axis i)| ≤ Q1*μ)
    (hLR : ‖LR y‖ ≤ R0*u) (hLS : ‖LS y‖ ≤ B0*ε*u)
    (hCurv : ‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis a) (axis b)‖ ≤ KC)
    (v : I → ℝ) (hv0 : ∀ i,0 ≤ v i)
    (hWeak : ∀ i,‖weakHalfSourceCovariantDerivative d LS y (axis i)‖ ≤ ε*(B0*v i+B1*u))
    (hMass : β*u^2 ≤ En) (hGrad : ∀ i,β⁻¹*(v i)^2 ≤ En) :
    |balancedHalfHodgePairRemainder d q LR LS (axis a) (axis b) y| ≤
      R0*(Q0*KC*B0+2*Q1*(2*B0+B1))*ε*μ*En := by
  have hU : u^2 ≤ En := (model_first_mass_products_le u (v a) β En hu (hv0 a) hβ hMass (hGrad a)).1
  have hUV (i : I) : v i*u ≤ 2*En :=
    (model_first_mass_products_le u (v i) β En hu (hv0 i) hβ hMass (hGrad i)).2.1
  have hC : |sphereSobolevDualPairing (1/2:ℝ) (LR y)
      (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis a) (axis b) (LS y))| ≤
      R0*KC*B0*ε*En := by
    calc
      _ ≤ ‖LR y‖*‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis a) (axis b) (LS y)‖ :=
        abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (R0*u)*(KC*(B0*ε*u)) := mul_le_mul hLR
        (((frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis a) (axis b)).le_opNorm _).trans
          (mul_le_mul hCurv hLS (norm_nonneg _) hKC)) (norm_nonneg _) (by positivity)
      _ = (R0*KC*B0*ε)*u^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hU (by positivity)
  have hW (i : I) : |sphereSobolevDualPairing (1/2:ℝ) (LR y)
      (weakHalfSourceCovariantDerivative d LS y (axis i))| ≤ R0*(2*B0+B1)*ε*En := by
    calc
      _ ≤ ‖LR y‖*‖weakHalfSourceCovariantDerivative d LS y (axis i)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (R0*u)*(ε*(B0*v i+B1*u)) := mul_le_mul hLR (hWeak i) (norm_nonneg _) (by positivity)
      _ = (R0*ε*B0)*(v i*u)+(R0*ε*B1)*u^2 := by ring
      _ ≤ (R0*ε*B0)*(2*En)+(R0*ε*B1)*En := add_le_add
        (mul_le_mul_of_nonneg_left (hUV i) (by positivity))
        (mul_le_mul_of_nonneg_left hU (by positivity))
      _ = _ := by ring
  unfold balancedHalfHodgePairRemainder
  refine ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  simp only [abs_mul]
  have h1 := mul_le_mul hq hC (abs_nonneg _) (mul_nonneg hQ0 hμ)
  have h2 := mul_le_mul (hDq a) (hW b) (abs_nonneg _) (mul_nonneg hQ1 hμ)
  have h3 := mul_le_mul (hDq b) (hW a) (abs_nonneg _) (mul_nonneg hQ1 hμ)
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
