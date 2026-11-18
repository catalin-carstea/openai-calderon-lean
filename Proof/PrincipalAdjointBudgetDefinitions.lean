import Proof.WeightedPrincipalJetBounds
import Proof.Archive.ScalarAdjointCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def scalarPrincipalMatrix (g g₂ : MetricField) (r : X → ℝ) : MetricField := fun y => r y • principal g g₂ y

def principalZeroBudget (K : ℝ) : ℝ := K+1

def principalFirstBudget (K M₁ : ℝ) : ℝ := K*(K+1)+9*K^2*M₁+1

def principalSecondBudget (K M₁ M₂ C₂ : ℝ) : ℝ :=
  (K^2+9*K^2*|C₂|+27*K^2*M₁)*(K+1)+2*K*(9*K^2*M₁+1)+(162*K^3*M₁^2+9*K^2*M₂+1)

def densityFirstBudget (K M₁ : ℝ) : ℝ := 27*K*M₁

def densitySecondBudget (K M₁ M₂ : ℝ) : ℝ := 972*K^2*M₁^2+27*K*M₂

def principalAdjointFirstBudget (K M₁ : ℝ) : ℝ :=
  6*(densityFirstBudget K M₁*principalZeroBudget K+principalFirstBudget K M₁)

def principalAdjointZeroBudget (K M₁ M₂ C₂ : ℝ) : ℝ :=
  9*(densitySecondBudget K M₁ M₂*principalZeroBudget K+
    2*densityFirstBudget K M₁*principalFirstBudget K M₁+principalSecondBudget K M₁ M₂ C₂)

end ShrinkingSpheres
