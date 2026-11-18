import Proof.PhysicalPotentialFirstWordLifts
import Proof.AmbientHigherSobolevSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def potentialQuadraticCoreL (P : PhysicalPrincipalData Y d CF CT) {y : X} {CG CK : ℝ}
    (W : PhysicalPotentialQuarticData P y CG CK) : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
    (∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
      potentialWordCoefficient d y a b • (P.potentialGeneratorHigh y a).comp (W.forwardFirstWordHigherL b))

def potentialQuadraticAdjointCoreL (P : PhysicalPrincipalData Y d CF CT) {y : X} {CG CK : ℝ}
    (W : PhysicalPotentialQuarticData P y CG CK) : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
    (∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
      potentialWordCoefficient d y a b • (W.adjointHigh b).comp (W.reverseFirstWordHigherL a))

lemma potentialQuadraticCoreL_balanced (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticCoreL W u)=
      P.potentialQuadraticHalfL y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  have h := P.potentialForwardCoreValue_balanced hy
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
    (fun a => W.forwardFirstWordHigherL a u) (fun a => W.forwardFirstWordHigherL_inclusion hy a u)
  simpa only [potentialQuadraticCoreL,potentialForwardCoreValue,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,sphereSobolevInclusionL_trans_apply] using h

/-- Full actual quadratic potential norm identity, with the common-core
lifts now PRODUCED from the SAME degree mixed-commutator row. -/
lemma potentialQuadraticCoreL_norm_difference (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    ‖P.potentialQuadraticCoreL W u‖^2-‖P.potentialQuadraticAdjointCoreL W u‖^2=
      P.potentialQuarticWeakValue W (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  have h := P.potential_core_norm_difference hy W
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
    (fun a => W.forwardFirstWordHigherL a u) (fun a => W.reverseFirstWordHigherL a u)
    (fun a => W.forwardFirstWordHigherL_inclusion hy a u) (fun a => W.reverseFirstWordHigherL_inclusion a u)
  simpa only [potentialQuadraticCoreL,potentialQuadraticAdjointCoreL,potentialForwardCoreValue,potentialReverseCoreValue,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply] using h

lemma abs_potentialQuadraticCoreL_norm_difference_small {Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    {CG CK : ℝ} (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    |‖P.potentialQuadraticCoreL W u‖^2-‖P.potentialQuadraticAdjointCoreL W u‖^2| ≤
      (4*CG^2*CK*(49*potentialWordEntryBudget K)^2)*ε*beta d.γ d.radius y*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u‖^2 := by
  rw [P.potentialQuadraticCoreL_norm_difference hy W u]
  exact P.abs_potentialQuarticWeakValue_small hd hK hf hε hε1 hy hCG hCK hBudget W _
end PhysicalPrincipalData
end ShrinkingSpheres
