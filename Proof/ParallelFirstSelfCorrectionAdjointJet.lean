import Proof.PhysicalCorrectionStrongHalfData
import Proof.CovariantCorrectionGradedJets
import Proof.StrongHalfCovariantAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine HIGH transpose of a bounded negative-grade coefficient. -/
def correctionAdjointHigherL (d : Data) (y b : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (physicalFirstCorrectionAtL (-(1/2:ℝ)) d y b).adjoint.comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma correctionAdjointHigherL_graph (d : Data) (y b : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (correctionAdjointHigherL d y b)=
      (physicalFirstCorrectionHalfL d y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [physicalFirstCorrectionHalfL,ContinuousLinearMap.adjoint_comp,sphereSobolevHalfNegativeInclusion_adjoint,
    ContinuousLinearMap.comp_assoc]
  rfl

lemma correctionCovariantHalfJet_eq_negative (d : Data) (y a b : X) :
    halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d y a b)=
      (physicalFirstCorrectionCovariantJetAtL (-(1/2:ℝ)) d y a b).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (physicalFirstCorrectionBoundedCovariantJetL d y a b
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u))=_
  rw [←physicalFirstCorrectionCovariantJetAtL_zero,
    physicalFirstCorrectionCovariantJetAtL_inclusion,sphereSobolevInclusionL_trans_apply]
  rfl

/-- Genuine HIGH transpose of the SAME bounded physical covariant jet. -/
def correctionAdjointCovariantHigherJet (d : Data) (y a b : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (physicalFirstCorrectionCovariantJetAtL (-(1/2:ℝ)) d y a b).adjoint.comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma correctionAdjointCovariantHigherJet_graph (d : Data) (y a b : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (correctionAdjointCovariantHigherJet d y a b)=
      (halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d y a b)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [correctionCovariantHalfJet_eq_negative,ContinuousLinearMap.adjoint_comp,
    sphereSobolevHalfNegativeInclusion_adjoint,ContinuousLinearMap.comp_assoc]
  rfl

lemma norm_correctionAdjointCovariantHigherJet_le (d : Data) (y a b : X) :
    ‖correctionAdjointCovariantHigherJet d y a b‖ ≤
      ‖physicalFirstCorrectionCovariantJetAtL (-(1/2:ℝ)) d y a b‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq
      (by rw [mul_one,ContinuousLinearMap.adjoint.norm_map]))

/-- The physical correction's true-adjoint covariant derivative has a
genuine HIGH graph with uniform reference norm, for ANY coherent endpoint.
Axis conversion uses frame values and the linear covariant derivative. -/
theorem uniform_physical_correction_true_adjoint_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : I,
      ∀ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ y ∈ Y,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
        (physicalFirstCorrectionHalfL d y (axis b)).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
      ∀ i : I,∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        halfOperatorCovariantDerivativeL d (fun x => (physicalFirstCorrectionHalfL d x (axis b)).adjoint) AH y (axis i)=
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧ ‖H‖ ≤ Q := by
  obtain ⟨Q0,hQ0,hBounds⟩ := uniform_physical_correction_covariant_grade_bound
    hY hΩ (-(1/2:ℝ)) hm K ρ c₀ M Cj hK
  refine ⟨3*K*Q0,by positivity,?_⟩
  intro floor hf ε hε hε1 d hd b AH y hy hAH i
  have hKpos := zero_lt_one.trans_le hK
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun a c => (hd.1.1.1 a c).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  let Lo := fun x => physicalFirstCorrectionHalfL d x (axis b)
  let Hi := fun x => physicalFirstCorrectionHigherL d x (axis b)
  have hLS : ContDiffOn ℝ ∞ Lo Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hKpos (-(1/2:ℝ)) (axis b)).clm_comp contDiffOn_const
  have hF (j : I) : halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y (d.frame y j)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (correctionAdjointCovariantHigherJet d y (d.frame y j) (axis b)) := by
    have hStrong := hd.physicalFirstCorrection_strong_half_frame_extension hY hΩ hKpos hy j b
    have hAdj := half_covariant_adjoint_strong_extension d Lo Hi AH
      (hLS.contDiffAt (hY.mem_nhds hy)) (d.frame y j) (physicalFirstCorrection_balanced d y (axis b)) hAH
      (halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d y (d.frame y j) (axis b))) hStrong
    exact hAdj.trans (correctionAdjointCovariantHigherJet_graph d y (d.frame y j) (axis b)).symm
  let c := fun j => frameCoordinateLinear d.γ d.frame y j (axis i)
  let H := ∑ j : I,c j • correctionAdjointCovariantHigherJet d y (d.frame y j) (axis b)
  have hAxis : halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y (axis i)=
      ∑ j : I,c j • halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y (d.frame y j) := by
    let T := halfOperatorCovariantDerivativeFamilyL d (fun x => (Lo x).adjoint) AH y
    have hh := congrArg T (frameCoordinateLinear_reconstruct d.γ d.frame y (axis i) hFrame)
    simpa only [T,c,map_sum,map_smul,halfOperatorCovariantDerivativeFamilyL_apply] using hh.symm
  refine ⟨H,?_,?_⟩
  · rw [hAxis]
    apply ContinuousLinearMap.ext
    intro u
    simp only [hF,H,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  · apply norm_weighted_sum_three_le _ _ K Q0 (zero_le_one.trans hK)
    · intro j
      dsimp only [c]
      rw [frameCoordinateLinear_apply]
      exact hg.frame_coordinate_abs_bound hK d.frame hy hFrame i j
    · intro j
      exact (norm_correctionAdjointCovariantHigherJet_le d y (d.frame y j) (axis b)).trans
        (hBounds floor hf ε hε hε1 d hd y hy j b)

end ShrinkingSpheres.ParallelEnergy
