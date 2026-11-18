import Proof.ParallelFirstPotentialCubic
import Proof.ParallelFirstPotentialIntegrability
import Proof.ParallelNormAssemblyReservedFiveHalfSections
import Proof.ParallelNormAssemblyReservedHigherGreen

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
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma firstPotential_half_core_pair (u : SphereSobolev (1/2:ℝ)) (v : SphereSobolev 0) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u,v⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) u (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) v) := by
  rw [sphereSobolevDualPairing_zero_inclusion,real_inner_comm]
  norm_num

lemma firstPotential_quadratic_weak_value {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordForwardWeakValue P y (PhysicalPrincipalData.potentialWordCoefficient d y) u=
      P.potentialQuadraticHalfL y u := by
  rw [P.potentialQuadraticHalfL_eq_word_matrix]
  rfl

/-- Exact coefficient-row cancellation. Both complete first orientations
are combined before the first base Green step or any absolute value. -/
theorem firstPotential_coefficient_row_pair
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I)
    (hRaw : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (5/2:ℝ)) (v : SphereSobolev (3/2:ℝ)) :
    let u3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstCovariantCoordinateHigherL b y v),P.potentialQuadraticCoreL W u⟫_ℝ+
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (WF.covariantCoordinateAdjointHigher b y v),P.potentialQuadraticAdjointCoreL W u⟫_ℝ=
    (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
      (sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a v) (P.potentialQuadraticHalfL y u3)+
       sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a u3) (P.potentialQuadraticHalfL y v)-
       sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
         (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u3)))+
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (firstPotentialBoundedForwardHigherL d b y v),P.potentialQuadraticCoreL W u⟫_ℝ+
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (effectiveFirstBoundedAdjointHigherL d b y v),P.potentialQuadraticAdjointCoreL W u⟫_ℝ := by
  let u3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  have hF (a : PhysicalPotentialGeneratorIndex) :
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (normalizedPotentialGeneratorHigh P y a v),P.potentialQuadraticCoreL W u⟫_ℝ=
        sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a v) (P.potentialQuadraticHalfL y u3) := by
    rw [firstPotential_half_core_pair,P.potentialQuadraticCoreL_balanced hy W u]
  have hA (a : PhysicalPotentialGeneratorIndex) :
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (firstPotentialNormalizedAdjointHigh W a v),P.potentialQuadraticAdjointCoreL W u⟫_ℝ=
        sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a u3) (P.potentialQuadraticHalfL y v)-
        sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
          (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u3) := by
    have hh := firstPotential_normalized_adjoint_quadratic_pair P hy W a
      (PhysicalPrincipalData.potentialWordCoefficient d y) u3 v
      (fun c => W.forwardFirstWordHigherL c u) (fun c => W.reverseFirstWordHigherL c u)
      (fun c => W.forwardFirstWordHigherL_inclusion hy c u) (fun c => W.reverseFirstWordHigherL_inclusion c u)
    rw [firstPotential_quadratic_weak_value] at hh
    simpa only [PhysicalPrincipalData.potentialQuadraticAdjointCoreL,quadraticWordAdjointCoreValue,
      ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply] using hh
  rw [firstPotential_forward_higher_word_split hY hd P hy b hRaw,
    firstPotential_adjoint_higher_word_split hY hd P WF hy W b]
  simp only [_root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,
    inner_add_left,sum_inner,real_inner_smul_left,hF,hA]
  have hS :
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
        sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a v) (P.potentialQuadraticHalfL y u3))+
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
        (sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a u3) (P.potentialQuadraticHalfL y v)-
        sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
          (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u3)))=
      ∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
        (sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a v) (P.potentialQuadraticHalfL y u3)+
        sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a u3) (P.potentialQuadraticHalfL y v)-
        sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
          (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u3)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  linarith only [hS]

end ShrinkingSpheres.ParallelEnergy
