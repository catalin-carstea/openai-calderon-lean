import Proof.PhysicalPotentialCoreAdjunction
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- One actual angular transpose of a full quadratic potential word.
Only the H3/2 norm of the left source and the H1/2 norm of the right source
are required in the resulting weak form. -/
lemma potentialQuadraticCoreL_half_mass_pair (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (5/2:ℝ)) :
    ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,P.potentialQuadraticCoreL W v⟫_ℝ=
      ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        potentialWordCoefficient d y a b*
          sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u)
            (P.potentialGeneratorLow y b (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) v)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let I0 := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hWord (a b : PhysicalPotentialGeneratorIndex) :
      ⟪J u,K (P.potentialGeneratorHigh y a (W.forwardFirstWordHigherL b v))⟫_ℝ=
        sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u)
          (P.potentialGeneratorLow y b (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) v)) := by
    let L := W.forwardFirstWordHigherL b v
    have hForward : I0 (J L)=P.potentialGeneratorLow y b
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) v) := by
      calc
        _ = sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) L) := by
          simp only [I0,J,sphereSobolevInclusionL_trans_apply]
        _ = sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
            (P.potentialGeneratorHigh y b (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) v)) :=
          congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
            (W.forwardFirstWordHigherL_inclusion hy b v)
        _ = _ := by
          have hh := DFunLike.congr_fun (P.potential_generator_balanced hy b)
            (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) v)
          simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh
    calc
      _ = ⟪K (P.potentialGeneratorHigh y a L),J u⟫_ℝ := real_inner_comm _ _
      _ = ⟪J L,K (W.adjointHigh a u)⟫_ℝ := P.potential_generator_core_pair hy W a L u
      _ = ⟪K (W.adjointHigh a u),J L⟫_ℝ := real_inner_comm _ _
      _ = sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u) (I0 (J L)) :=
        (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) (W.adjointHigh a u) (J L)).symm
      _ = _ := congrArg (fun z => sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u) z) hForward
  simp only [potentialQuadraticCoreL,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul,inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun z : ℝ => potentialWordCoefficient d y a b*z) (hWord a b)

lemma abs_potentialQuadraticCoreL_half_mass_le (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (hr : 0 ≤ d.radius y) {CG CK : ℝ}
    (hCG : 0 ≤ CG) (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (5/2:ℝ)) :
    |⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,P.potentialQuadraticCoreL W v⟫_ℝ| ≤
      CG^2*potentialWordMass d y*‖u‖*
        ‖sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) v‖ := by
  let V := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) v
  let w := potentialGeneratorWeight (d.radius y)
  have hw := potentialGeneratorWeight_nonneg hr
  have hL (b : PhysicalPotentialGeneratorIndex) : ‖P.potentialGeneratorLow y b‖ ≤ CG*w b :=
    ((P.potential_generator_norm_bounds hy hr b).1).trans (mul_le_mul_of_nonneg_right hBudget (hw b))
  have hTerm (a b : PhysicalPotentialGeneratorIndex) :
      |potentialWordCoefficient d y a b*sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u)
        (P.potentialGeneratorLow y b V)| ≤
        (CG^2*‖u‖*‖V‖)*(|potentialWordCoefficient d y a b| *w a*w b) := by
    rw [abs_mul]
    have hA := ((W.adjointHigh a).le_opNorm u).trans (mul_le_mul_of_nonneg_right (W.adjoint_bound a) (norm_nonneg _))
    have hB := ((P.potentialGeneratorLow y b).le_opNorm V).trans (mul_le_mul_of_nonneg_right (hL b) (norm_nonneg _))
    calc
      _ ≤ |potentialWordCoefficient d y a b| *(‖W.adjointHigh a u‖*‖P.potentialGeneratorLow y b V‖) :=
        mul_le_mul_of_nonneg_left (abs_sphereSobolevDualPairing_le (1/2:ℝ) _ _) (abs_nonneg _)
      _ ≤ |potentialWordCoefficient d y a b| *((CG*w a*‖u‖)*(CG*w b*‖V‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB (norm_nonneg _)
          (mul_nonneg (mul_nonneg hCG (hw a)) (norm_nonneg _))) (abs_nonneg _)
      _ = _ := by ring
  rw [P.potentialQuadraticCoreL_half_mass_pair hy W u v]
  calc
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        |potentialWordCoefficient d y a b*sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u)
          (P.potentialGeneratorLow y b V)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        (CG^2*‖u‖*‖V‖)*(|potentialWordCoefficient d y a b| *w a*w b) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by
      simp only [potentialWordMass,potentialWordWeightedEntry,Finset.mul_sum,Finset.sum_mul,w,V]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end PhysicalPrincipalData
end ShrinkingSpheres
