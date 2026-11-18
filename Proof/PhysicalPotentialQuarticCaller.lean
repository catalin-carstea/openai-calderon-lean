import Proof.PhysicalPotentialWordMass
import Proof.FinitePolarizedQuarticWeakForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Missing producer interface for the full actual generator family.
    Compatibility is through genuine inclusions; no higher regularity
    or norm estimate is inferred from equality of the underlying types. -/
structure PhysicalPotentialQuarticData {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (CG CK : ℝ) where
  adjointHigh : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  commLow : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex →
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  commHigh : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex →
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  adjoint_compatible : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (adjointHigh a)=
    (P.potentialGeneratorLow y a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  commutator_compatible : ∀ a b,
    (P.potentialGeneratorLow y a).adjoint.comp (P.potentialGeneratorHigh y b)-
      (P.potentialGeneratorLow y b).comp (adjointHigh a)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (commHigh a b)
  commutator_balanced : ∀ a b,
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (commHigh a b)=
      (commLow a b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  adjoint_bound : ∀ a,‖adjointHigh a‖ ≤ CG*potentialGeneratorWeight (d.radius y) a
  commLow_bound : ∀ a b,‖commLow a b‖ ≤ CK*potentialGeneratorWeight (d.radius y) a*potentialGeneratorWeight (d.radius y) b
  commHigh_bound : ∀ a b,‖commHigh a b‖ ≤ CK*potentialGeneratorWeight (d.radius y) a*potentialGeneratorWeight (d.radius y) b

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def potentialQuarticWeakValue (P : PhysicalPrincipalData Y d CF CT) {y : X} {CG CK : ℝ}
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (3/2:ℝ)) : ℝ :=
  finitePolarizedQuarticWeakForm (potentialWordCoefficient d y) (potentialWordCoefficient d y)
    (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y) W.adjointHigh W.commLow W.commHigh u

/-- Checked conditional caller for the missing complete mixed-adjoint
    producer. This bounds the full matrix weak expression, not yet the
    actual physical norm difference or its complementary remainder. -/
theorem abs_potentialQuarticWeakValue_small {Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    {CG CK : ℝ} (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (3/2:ℝ)) :
    |P.potentialQuarticWeakValue W u| ≤
      (4*CG^2*CK*(49*potentialWordEntryBudget K)^2)*ε*beta d.γ d.radius y*‖u‖^2 := by
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hw := potentialGeneratorWeight_nonneg hr
  have hL (a : PhysicalPotentialGeneratorIndex) := ((P.potential_generator_norm_bounds hy hr a).1).trans
    (mul_le_mul_of_nonneg_right hBudget (hw a))
  have hH (a : PhysicalPotentialGeneratorIndex) := ((P.potential_generator_norm_bounds hy hr a).2).trans
    (mul_le_mul_of_nonneg_right hBudget (hw a))
  have hForm := abs_finitePolarizedQuarticWeakForm_le (potentialWordCoefficient d y) (potentialWordCoefficient d y) _ _ _ _ _ _ hCG hCK hw hL hH W.adjoint_bound
    W.commLow_bound W.commHigh_bound u
  have hMass0 := potentialWordMass_nonneg d y hr
  have hMass := hd.potentialWordMass_le hK hf hε hε1 hy
  let CW := 49*potentialWordEntryBudget K
  have hCW : 0 ≤ CW := by dsimp only [CW,potentialWordEntryBudget];positivity
  have hA : 0 ≤ 4*CG^2*CK := by positivity
  have hMSq : (potentialWordMass d y)^2 ≤ (CW*ε)^2 := by
    exact pow_le_pow_left₀ hMass0 hMass 2
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hεβ : ε^2 ≤ ε*beta d.γ d.radius y := by
    nlinarith only [mul_le_mul_of_nonneg_left hε1 hε,mul_le_mul_of_nonneg_left hβ hε]
  calc
    _ ≤ (4*CG^2*CK)*(potentialWordMass d y)^2*‖u‖^2 := by
      simpa only [potentialQuarticWeakValue,quadraticWordCoefficientMass,potentialWordMass,
        potentialWordWeightedEntry,pow_two] using hForm
    _ ≤ (4*CG^2*CK)*(CW*ε)^2*‖u‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMSq hA) (sq_nonneg _)
    _ = (4*CG^2*CK*CW^2)*ε^2*‖u‖^2 := by ring
    _ ≤ (4*CG^2*CK*CW^2)*(ε*beta d.γ d.radius y)*‖u‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hεβ (by positivity)) (sq_nonneg _)
    _ = _ := by ring
end PhysicalPrincipalData
end ShrinkingSpheres
