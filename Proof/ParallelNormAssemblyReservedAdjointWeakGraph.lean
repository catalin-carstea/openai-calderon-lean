import Proof.ParallelNormAssemblyReservedModelZeroAdjoint
import Proof.PhysicalPotentialWordMass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma actual_potential_adjoint_core_weak_graph {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreL W u)=
      quadraticWordAdjointWeakValue P W (PhysicalPrincipalData.potentialWordCoefficient d y)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  have hh := quadratic_word_adjoint_core_balanced P W (PhysicalPrincipalData.potentialWordCoefficient d y)
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
    (fun c => W.reverseFirstWordHigherL c u) (fun c => W.reverseFirstWordHigherL_inclusion c u)
  simpa only [PhysicalPrincipalData.potentialQuadraticAdjointCoreL,quadraticWordAdjointCoreValue,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,sphereSobolevInclusionL_trans_apply] using hh

lemma actual_potential_adjoint_section_weak_graph {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)=
      quadraticWordAdjointWeakValue P (W y hy) (PhysicalPrincipalData.potentialWordCoefficient d y)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  simp only [PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,dite_eq_left hy]
  exact actual_potential_adjoint_core_weak_graph P (W y hy) (U y)

/-- True quadratic-adjoint weak output has the sharp complete potential
size on H3/2. Only the SAME W genuine adjoints are used. -/
theorem actual_potential_adjoint_weak_norm_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (hCG : 0 ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (3/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    ‖quadraticWordAdjointWeakValue P W (PhysicalPrincipalData.potentialWordCoefficient d y) u‖ ≤
      (G^2*(49*potentialWordEntryBudget K))*ε*‖u‖ := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let w := potentialGeneratorWeight (d.radius y)
  let p := PhysicalPrincipalData.potentialWordCoefficient d y
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hw := potentialGeneratorWeight_nonneg hr
  have hL (e : PhysicalPotentialGeneratorIndex) : ‖(P.potentialGeneratorLow y e).adjoint‖ ≤ G*w e := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact ((P.potential_generator_norm_bounds hy hr e).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw e))
  have hA (c : PhysicalPotentialGeneratorIndex) : ‖W.adjointHigh c‖ ≤ G*w c :=
    (W.adjoint_bound c).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hw c))
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      ‖(P.potentialGeneratorLow y e).adjoint (W.adjointHigh c u)‖ ≤ G^2*(w c*w e)*‖u‖ := by
    exact ((((P.potentialGeneratorLow y e).adjoint).le_opNorm _).trans
      (mul_le_mul (hL e) (((W.adjointHigh c).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (hA c) (norm_nonneg u)))
        (norm_nonneg _) (mul_nonneg hG (hw e)))).trans_eq (by ring)
  have hWord : ‖quadraticWordAdjointWeakValue P W p u‖ ≤
      G^2*quadraticWordCoefficientMass p w*‖u‖ := by
    calc
      _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
          ‖p c e • (P.potentialGeneratorLow y e).adjoint (W.adjointHigh c u)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => norm_sum_le _ _))
      _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
          |p c e| *(G^2*(w c*w e)*‖u‖) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro e _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hTerm c e) (abs_nonneg _)
      _ = _ := by
        simp only [quadraticWordCoefficientMass,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro e _
        ring
  have hMass := hd.potentialWordMass_le hK hf hε hε1 hy
  exact hWord.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMass (sq_nonneg G))
    (norm_nonneg u)).trans_eq (by ring))

end ShrinkingSpheres.ParallelEnergy
