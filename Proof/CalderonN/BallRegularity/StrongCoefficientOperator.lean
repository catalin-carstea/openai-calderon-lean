module

public import Proof.CalderonN.BallRegularity.CoefficientMultiplier
public import Proof.CalderonN.BallRegularity.SobolevDivergenceAssembly

/-! From Proof/Archive/StrongCoefficientOperator.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


abbrev SmoothCoefficientMatrix (dim : ℕ) (r : ℕ) := Fin dim → Fin dim → (SmoothCoefficientJets dim) r

instance instNormedSpaceSmoothCoefficientMatrix (r : ℕ) :
    NormedSpace ℝ ((SmoothCoefficientMatrix dim) r) := by
  letI : ∀ _ : Fin dim, SeminormedAddCommGroup ((SmoothCoefficientJets dim) r) :=
    fun _ => inferInstance
  letI : ∀ _ : Fin dim, NormedSpace ℝ ((SmoothCoefficientJets dim) r) := fun _ => inferInstance
  letI : ∀ _ : Fin dim, SeminormedAddCommGroup (Fin dim → (SmoothCoefficientJets dim) r) :=
    fun _ => inferInstance
  letI : ∀ _ : Fin dim, NormedSpace ℝ (Fin dim → (SmoothCoefficientJets dim) r) :=
    fun _ => Pi.normedSpace (E := fun _ : Fin dim => (SmoothCoefficientJets dim) r)
  exact Pi.normedSpace (E := fun _ : Fin dim => Fin dim → (SmoothCoefficientJets dim) r)

 
def strongCoordinateDerivativeL (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) (j : Fin dim) :=
  (unitBallCoordinateDerivativeL hcalc (s + 1) j).comp
    ((strongDirichletSubmodule dim) s).toSubmodule.subtypeL

 
def coefficientMatrixMultiplierL (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) :=
  ContinuousLinearMap.pi fun i : Fin dim => ContinuousLinearMap.pi fun j : Fin dim =>
    (coefficientMultiplierL hcalc (s + 1)).comp
      ((ContinuousLinearMap.proj j :
        (Fin dim → (SmoothCoefficientJets dim) (s + 2)) →L[ℝ] (SmoothCoefficientJets dim) (s + 2)).comp
        (ContinuousLinearMap.proj i :
          (SmoothCoefficientMatrix dim) (s + 2) →L[ℝ] Fin dim → (SmoothCoefficientJets dim) (s + 2)))

theorem coefficientMatrixMultiplierL_apply (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) (i j : Fin dim) :
    coefficientMatrixMultiplierL hcalc s F i j = coefficientMultiplier hcalc (s + 1) (F i j) :=
  rfl

 
def strongCoefficientOperatorL (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) :=
  (unitBallDivergenceL hcalc s).comp (coefficientMatrixMultiplierL hcalc s)

theorem strongCoefficientOperatorL_apply (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) :
    strongCoefficientOperatorL hcalc s F =
      -∑ i, ∑ j, ((unitBallCoordinateDerivativeL hcalc s i).comp
        (coefficientMultiplier hcalc (s + 1) (F i j))).comp
          (strongCoordinateDerivativeL hcalc s j) := by
  exact coefficientDivergenceL_apply _ _ _

theorem strongCoefficientOperatorL_apply_apply (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) (u : (StrongDirichletSpace dim) s) :
    strongCoefficientOperatorL hcalc s F u =
      -∑ i, ∑ j, unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)) := by
  exact coefficientDivergenceL_apply_apply _ _ _ _

 
def strongCoefficientOperatorBound (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) : ℝ :=
  ∑ i : Fin dim, ∑ j : Fin dim,
    ‖unitBallCoordinateDerivativeL hcalc s i‖ * sobolevMultiplierBound hcalc (s + 1) *
      ‖strongCoordinateDerivativeL hcalc s j‖

theorem strongCoefficientOperatorBound_nonneg (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) :
    0 ≤ strongCoefficientOperatorBound hcalc s :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (sobolevMultiplierBound_nonneg hcalc _))
      (norm_nonneg _)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_strongCoefficientOperator {n : WithTop ℕ∞}
    (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : E → (SmoothCoefficientMatrix dim) (s + 2)) (q : Set E)
    (hF : ContDiffOn ℝ n F q) :
    ContDiffOn ℝ n (fun x => strongCoefficientOperatorL hcalc s (F x)) q :=
  (strongCoefficientOperatorL hcalc s).contDiff.comp_contDiffOn hF

end CalderonN.BallDirichlet
