import Proof.ClosedOneBoundaryScalarMultiplier
import Mathlib.Analysis.Calculus.FDeriv.Const
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma smoothCoefficientJets_ext_of_value (r : ℕ) (Q P : SmoothCoefficientJets r)
    (h : coefficientValue r Q = coefficientValue r P) : Q = P := by
  apply Subtype.ext
  funext j
  apply BoundedContinuousFunction.ext
  intro x
  rw [coefficientJet_eq_iteratedFDeriv,coefficientJet_eq_iteratedFDeriv,h]

lemma norm_compactCoefficient_le_of_jets (r : ℕ) (f : X → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (B : ℝ) (hB : 0 ≤ B)
    (hJets : ∀ n : ℕ,n ≤ r → ∀ x,‖iteratedFDeriv ℝ n f x‖ ≤ B) :
    ‖compactCoefficient r f hf hc‖ ≤ B := by
  change ‖compactCoefficientJet r f hf hc‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  apply (BoundedContinuousFunction.norm_le hB).mpr
  intro x
  exact hJets j.1 (by omega) x

lemma norm_iteratedFDeriv_fixedDirectional_le (f : X → ℝ) (v : X) (x : X)
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ f z v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (n+1) f x‖ := by
  let ev : (X →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hev : ‖ev‖ ≤ ‖v‖ := by
    apply ev.opNorm_le_bound (norm_nonneg v)
    intro A
    exact (A.le_opNorm v).trans_eq (mul_comm _ _)
  have hh := norm_iteratedFDeriv_clm_comp_le ev (fderiv ℝ f) x
    (hf.fderiv_right (m:=∞) (by simp)) n
  have hNorm : ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ (n+1) f x‖ :=
    norm_iteratedFDeriv_fderiv
  exact hh.trans ((mul_le_mul_of_nonneg_right hev (norm_nonneg _)).trans_eq
    (congrArg (fun a : ℝ => ‖v‖*a) hNorm))

def smoothCoefficientDirectionalDerivative (r : ℕ) (v : X) (Q : SmoothCoefficientJets (r+1)) :
    SmoothCoefficientJets r :=
  compactCoefficient r (fun x => fderiv ℝ (coefficientValue (r+1) Q) x v)
    (((contDiff_coefficientValue (r+1) Q).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const)
    ((hasCompactSupport_coefficientValue (r+1) Q).fderiv_apply ℝ v)

lemma coefficientValue_smoothCoefficientDirectionalDerivative (r : ℕ) (v : X)
    (Q : SmoothCoefficientJets (r+1)) :
    coefficientValue r (smoothCoefficientDirectionalDerivative r v Q) =
      fun x => fderiv ℝ (coefficientValue (r+1) Q) x v :=
  coefficientValue_compactCoefficient _ _ _ _

lemma norm_smoothCoefficientDirectionalDerivative_le (r : ℕ) (v : X)
    (Q : SmoothCoefficientJets (r+1)) :
    ‖smoothCoefficientDirectionalDerivative r v Q‖ ≤ ‖v‖*‖Q‖ := by
  apply norm_compactCoefficient_le_of_jets r _ _ _ _ (by positivity)
  intro n hn x
  exact (norm_iteratedFDeriv_fixedDirectional_le (coefficientValue (r+1) Q) v x
    (contDiff_coefficientValue (r+1) Q).contDiffAt n).trans
      (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_coefficientValue_le (r+1) Q (n+1) (by omega) x) (norm_nonneg v))

end ShrinkingSpheres
