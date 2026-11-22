module

public import Proof.CalderonN.ParametricBallStrongSolution

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! Adapted from `BallForcingJetBounds` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1700000

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

open CalderonN.BallDirichlet

local instance (priority := 1500) ballForcingCLMNorm (m : ℕ) :
    NormedAddCommGroup ((ClosedCoefficientJets dim) (m+1) →L[ℝ] (BallSobolev dim) m) :=
  ContinuousLinearMap.toNormedAddCommGroup

private def closedCoefficientJetEval (m : ℕ) (j : Fin (m+1)) (z : (X dim)) :
    (ClosedCoefficientJets dim) m →L[ℝ] (X dim) [×j.val]→L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ z).comp
    ((ContinuousLinearMap.proj j).comp ((smoothCoefficientJetSubmodule dim) m).topologicalClosure.subtypeL)

private theorem closedCoefficientJetEval_apply (m : ℕ) (j : Fin (m+1)) (z : (X dim))
    (F : (ClosedCoefficientJets dim) m) :
    closedCoefficientJetEval m j z F = F.1 j z := rfl

private theorem norm_closedCoefficient_le {m : ℕ} (F : (ClosedCoefficientJets dim) m)
    {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ (j : Fin (m+1)) (z : (X dim)), ‖closedCoefficientJetEval m j z F‖ ≤ B) :
    ‖F‖ ≤ B := by
  change ‖F.val‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  exact (BoundedContinuousFunction.norm_le hB).mpr (fun z => hF j z)

private def ballForcingL (m : ℕ) : (ClosedCoefficientJets dim) (m+1) →L[ℝ] (BallSobolev dim) m :=
  (ContinuousLinearMap.apply ℝ ((BallSobolev dim) m) (smoothBallSobolev m ⟨1,contDiff_const⟩)).comp
    (closedCoefficientMultiplierL fixedSobolevCalculus m)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A common-support smooth lift to the fixed-ball Sobolev graph norm is
bounded by its spatial jets and by those jets differentiated in a
parameter direction. The parameter direction may include a radius factor. -/
theorem exists_ballForcingFamily_jet_bounds (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d) (K : Set (X dim)) (hK : IsCompact K)
        (hSupp : ∀ p z, z ∉ K → d (p,z) = 0) (p v : P) (M N : ℝ), 0 ≤ M → 0 ≤ N →
        (∀ k : ℕ, k ≤ m+1 → ∀ z : (X dim), ‖iteratedFDeriv ℝ k (fun x => d (p,x)) z‖ ≤ M) →
        (∀ k : ℕ, k ≤ m+1 → ∀ z : (X dim),
          ‖fderiv ℝ (fun q : P => iteratedFDeriv ℝ k (fun x => d (q,x)) z) p v‖ ≤ N) →
        ‖ballForcingFamily m d hd K hK hSupp p‖ ≤ C*M ∧
        ‖fderiv ℝ (ballForcingFamily m d hd K hK hSupp) p v‖ ≤ C*N := by
  let L := ballForcingL (dim := dim) m
  refine ⟨‖L‖,norm_nonneg _,fun d hd K hK hSupp p v M N hM hN h₀ h₁ => ?_⟩
  let n := m+1
  let D := commonSupportClosedCoefficientFamily n d hd K hK hSupp
  have hD : ContDiff ℝ ∞ D := contDiff_commonSupportClosedCoefficientFamily n d hd K hK hSupp
  have hD₁ := hD.differentiable (by simp) p
  have he (j : Fin (n+1)) (z : (X dim)) (q : P) :
      closedCoefficientJetEval n j z (D q) = iteratedFDeriv ℝ j.val (fun x => d (q,x)) z := by
    simp only [D,closedCoefficientJetEval_apply,commonSupportClosedCoefficientFamily_val,
      commonSupportCoefficientFamily_jet]
  have he' (j : Fin (n+1)) (z : (X dim)) :
      closedCoefficientJetEval n j z (fderiv ℝ D p v) =
        fderiv ℝ (fun q : P => iteratedFDeriv ℝ j.val (fun x => d (q,x)) z) p v := by
    let E := closedCoefficientJetEval n j z
    have h := (E.hasFDerivAt.comp p hD₁.hasFDerivAt).fderiv
    have hh : E ∘ D = fun q : P => iteratedFDeriv ℝ j.val (fun x => d (q,x)) z := funext (he j z)
    rw [hh] at h
    exact (congrArg (fun F : P →L[ℝ] (X dim) [×j.val]→L[ℝ] ℝ => F v) h).symm
  have hB : ballForcingFamily m d hd K hK hSupp = L ∘ D := by
    funext q
    change coefficientMultiplier fixedSobolevCalculus m
        (commonSupportCoefficientFamily n d hd K hK hSupp q) (smoothBallSobolev m ⟨1,contDiff_const⟩) =
      closedCoefficientMultiplierL fixedSobolevCalculus m
        (smoothCoefficientClosureInclusionL n (commonSupportCoefficientFamily n d hd K hK hSupp q))
          (smoothBallSobolev m ⟨1,contDiff_const⟩)
    rw [closedCoefficientMultiplierL_eq_on_smooth]
  have hDval : ‖D p‖ ≤ M :=
    norm_closedCoefficient_le (dim := dim) (D p) hM (fun j z => by rw [he]; exact h₀ j.val (by omega) z)
  have hDderiv : ‖fderiv ℝ D p v‖ ≤ N :=
    norm_closedCoefficient_le (dim := dim) _ hN (fun j z => by rw [he']; exact h₁ j.val (by omega) z)
  rw [hB,(L.hasFDerivAt.comp p hD₁.hasFDerivAt).fderiv]
  exact ⟨(L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hDval (norm_nonneg _)),
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hDderiv (norm_nonneg _))⟩

end CalderonN
