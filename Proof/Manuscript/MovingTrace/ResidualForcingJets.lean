module

public import Proof.CalderonN.BallForcingJetBounds
public import Proof.CalderonN.CommonSupportMultiplierDerivative
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
open Set CalderonN CalderonN.BallDirichlet
open scoped ContDiff

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
local instance (priority := 1500) forcingNorm (m : ℕ) :
    NormedAddCommGroup (ClosedCoefficientJets dim (m+1) →L[ℝ] BallSobolev dim m) :=
  ContinuousLinearMap.toNormedAddCommGroup

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The actual fixed-ball forcing lift bounds all parameter derivatives by
the corresponding mixed parameter-spatial derivatives of the smooth residual. -/
theorem ballForcingFamily_all_parameter_jets (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : P × X dim → ℝ) (hd : ContDiff ℝ ∞ d)
      (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → d (p,z) = 0)
      (p : P) (N : ℕ) (M : ℝ), 0 ≤ M →
      (∀ j ≤ N, ∀ k ≤ m+1, ∀ z,
        ‖iteratedFDeriv ℝ j (fun q : P => iteratedFDeriv ℝ k (fun x => d (q,x)) z) p‖ ≤ M) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (ballForcingFamily m d hd K hK hSupp) p‖ ≤ C * M := by
  let n := m+1
  let L : ClosedCoefficientJets dim n →L[ℝ] BallSobolev dim m :=
    (ContinuousLinearMap.apply ℝ (BallSobolev dim m)
      (smoothBallSobolev m ⟨1, contDiff_const⟩)).comp
        (closedCoefficientMultiplierL fixedSobolevCalculus m)
  refine ⟨‖L‖, norm_nonneg _, ?_⟩
  intro d hd K hK hSupp p N M hM hResidual j hj
  let D := commonSupportClosedCoefficientFamily n d hd K hK hSupp
  have hD : ContDiff ℝ ∞ D := contDiff_commonSupportClosedCoefficientFamily n d hd K hK hSupp
  have hLift : ballForcingFamily m d hd K hK hSupp = L ∘ D := by
    funext q
    change coefficientMultiplier fixedSobolevCalculus m
        (commonSupportCoefficientFamily n d hd K hK hSupp q) (smoothBallSobolev m ⟨1, contDiff_const⟩) =
      closedCoefficientMultiplierL fixedSobolevCalculus m
        (smoothCoefficientClosureInclusionL n (commonSupportCoefficientFamily n d hd K hK hSupp q))
          (smoothBallSobolev m ⟨1, contDiff_const⟩)
    rw [closedCoefficientMultiplierL_eq_on_smooth]
  have hDJet : ‖iteratedFDeriv ℝ j D p‖ ≤ M := by
    refine ContinuousMultilinearMap.opNorm_le_bound hM fun v => ?_
    let B : ℝ := M * ∏ i, ‖v i‖
    have hB : 0 ≤ B := by dsimp [B]; positivity
    change ‖((iteratedFDeriv ℝ j D p) v).val‖ ≤ B
    refine (pi_norm_le_iff_of_nonneg hB).mpr fun k =>
      (BoundedContinuousFunction.norm_le hB).mpr fun z => ?_
    let eval := closedCoefficientJetEvaluationL n k z
    have he : eval ∘ D = fun q : P => iteratedFDeriv ℝ k.val (fun x => d (q,x)) z := by
      funext q
      simp only [D, Function.comp_apply, eval, closedCoefficientJetEvaluationL_apply,
        commonSupportClosedCoefficientFamily_val, commonSupportCoefficientFamily_jet]
    have hEval := eval.iteratedFDeriv_comp_left (x := p) hD.contDiffAt
      (by simp : (j : ℕ∞ω) ≤ ∞)
    have hBound : ‖(eval.compContinuousMultilinearMap (iteratedFDeriv ℝ j D p)) v‖ ≤ B := by
      rw [← hEval, he]
      have hK : k.val ≤ m+1 := by have := k.isLt; dsimp [n] at this; omega
      exact ((iteratedFDeriv ℝ j (fun q : P => iteratedFDeriv ℝ k.val (fun x => d (q,x)) z) p).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hResidual j hj k.val hK z) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      eval, closedCoefficientJetEvaluationL_apply] using hBound
  rw [hLift]
  exact (L.norm_iteratedFDeriv_comp_left hD.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞)).trans
    (mul_le_mul_of_nonneg_left hDJet (norm_nonneg _))

end CalderonPaper
